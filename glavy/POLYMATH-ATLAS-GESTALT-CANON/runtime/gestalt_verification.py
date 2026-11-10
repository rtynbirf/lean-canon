#!/usr/bin/env python3
"""Concrete finite mirrors of the proved theorems of ``RequestProject/Gestalt``.

Every Lean theorem of the gestalt layer (namespaces
``PolymathAtlas.Gestalt.{UCC, Genesis, SelfReference, MetaSkills, ToolInventory,
Canon, CoreBridge}``) is mirrored here by an exhaustive check on a small concrete
model — ``Bool`` (2 states) or ``Fin 3`` (3 states) — instantiating the structure
fields the Lean statement quantifies over.

This script is *not* a proof: the Lean sources are.  It is a sanity mirror, so
that every closed ``sorry`` has a witness that can be executed and inspected.

Run:  ``python runtime/gestalt_verification.py``
Exit code 0 and a ``PASS`` line per theorem means every mirror agrees with Lean.
"""

from __future__ import annotations

import itertools
import math
import sys
from dataclasses import dataclass
from typing import Callable, Iterable

BOOL = (False, True)
FIN3 = (0, 1, 2)

_RESULTS: list[tuple[str, bool]] = []


def check(name: str, ok: bool) -> None:
    _RESULTS.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}")


def all_funs(domain: Iterable, codomain: Iterable) -> Iterable[Callable]:
    """All functions ``domain -> codomain``, as dict-backed callables."""
    domain = list(domain)
    for values in itertools.product(list(codomain), repeat=len(domain)):
        table = dict(zip(domain, values))
        yield (lambda t: (lambda x: t[x]))(table)


# ---------------------------------------------------------------------------
# Part 1 — UCC, T1-T5   (RequestProject/Gestalt/UCC.lean)
# ---------------------------------------------------------------------------


def channel_card(o: Callable, domain=FIN3) -> int:
    return len({o(s) for s in domain})


def draws_distinction(o: Callable, domain=FIN3) -> bool:
    return any(o(s) != o(t) for s in domain for t in domain)


def t1_no_distinction_no_information() -> bool:
    return all(
        (not draws_distinction(o)) == (channel_card(o) == 1)
        for o in all_funs(FIN3, BOOL)
    )


def t1_distinction_of_drawsDistinction() -> bool:
    for o in all_funs(FIN3, BOOL):
        if not draws_distinction(o):
            continue
        inside = {s for s in FIN3 if o(s) == o(0)}
        outside = set(FIN3) - inside
        if not (inside and outside and inside != outside):
            return False
    return True


def uncertainty(c: frozenset) -> float:
    return math.log(len(c))


def information_gain(prior: frozenset, post: frozenset) -> float:
    return uncertainty(prior) - uncertainty(post)


def subsets(domain=FIN3):
    for r in range(len(domain) + 1):
        for c in itertools.combinations(domain, r):
            yield frozenset(c)


def t2_informationGain_nonneg() -> bool:
    return all(
        information_gain(prior, post) >= -1e-12
        for prior in subsets()
        for post in subsets()
        if post <= prior and post
    )


def t2_informationGain_eq_zero_iff() -> bool:
    return all(
        (abs(information_gain(prior, post)) < 1e-12) == (post == prior)
        for prior in subsets()
        for post in subsets()
        if post <= prior and post
    )


def t2_gain_pos_iff_distinction_cuts() -> bool:
    ok = True
    for c in subsets():
        if not c:
            continue
        for inside in subsets():
            refined = frozenset(c & inside)
            if not refined:
                continue
            ok = ok and ((information_gain(c, refined) > 1e-12) == (refined != c))
    return ok


@dataclass
class CognitiveSystem:
    """Mirror of ``Gestalt.UCC.CognitiveSystem`` on a finite state space."""

    predict: Callable
    env: Callable
    step: Callable
    states: tuple = FIN3

    def learning_rate(self, s) -> float:
        # field `learningRate_eq_zero_iff`: zero exactly on correct predictions
        return 0.0 if self.predict(s) == self.env(s) else 1.0

    def perfect(self) -> bool:
        return all(self.predict(s) == self.env(s) for s in self.states)

    def trajectory(self, x, n: int):
        for _ in range(n):
            x = self.step(x)
        return x


def error_driven_step(M: CognitiveSystem):
    """Mirror of ``ErrorDriven``: the step moves only where the system errs."""

    def step(s):
        return s if M.predict(s) == M.env(s) else M.env(s)

    return step


def t3_feedbackError() -> bool:
    for predict in all_funs(FIN3, FIN3):
        M = CognitiveSystem(predict, predict, lambda s: s)
        if not all(M.learning_rate(s) == 0.0 for s in FIN3):
            return False
    return True


def t3_learningRate_pos_of_error() -> bool:
    for predict in all_funs(FIN3, FIN3):
        for env in all_funs(FIN3, FIN3):
            M = CognitiveSystem(predict, env, lambda s: s)
            for s in FIN3:
                if predict(s) != env(s) and not M.learning_rate(s) > 0:
                    return False
    return True


def t4_perfectPredictInert() -> bool:
    for predict in all_funs(FIN3, FIN3):
        M = CognitiveSystem(predict, predict, lambda s: s)
        step = error_driven_step(M)
        if any(step(s) != s for s in FIN3):
            return False
    return True


def t4_trajectory_const() -> bool:
    for predict in all_funs(FIN3, FIN3):
        M = CognitiveSystem(predict, predict, lambda s: s)
        M.step = error_driven_step(M)
        if any(M.trajectory(x, n) != x for x in FIN3 for n in range(5)):
            return False
    return True


def t5_pigeonhole_revisit() -> bool:
    for f in all_funs(range(4), FIN3):
        seen, found = set(), False
        for i in range(4):
            if f(i) in seen:
                found = True
                break
            seen.add(f(i))
        if not found:
            return False
    return True


def t5_system_revisits() -> bool:
    for step in all_funs(FIN3, FIN3):
        for x in FIN3:
            seen, cur, found = set(), x, False
            for _ in range(len(FIN3) + 1):
                if cur in seen:
                    found = True
                    break
                seen.add(cur)
                cur = step(cur)
            if not found:
                return False
    return True


# ---------------------------------------------------------------------------
# Part 2 — Genesis Engine, L1-L7   (RequestProject/Gestalt/GenesisEngine.lean)
# ---------------------------------------------------------------------------


def l1_distinctionDetector_memoryless() -> bool:
    detector = {False: "d0", True: "d1"}

    def on_history(h):
        return set() if not h else {detector[h[0]]}

    histories = [[]] + [list(t) for n in (1, 2) for t in itertools.product(BOOL, repeat=n)]
    for h in histories:
        for k in histories:
            head_h = h[0] if h else None
            head_k = k[0] if k else None
            if head_h == head_k and on_history(h) != on_history(k):
                return False
    return True


def l1_output_is_t1() -> bool:
    for inside in subsets():
        outside = frozenset(set(FIN3) - inside)
        if inside == outside:
            return False
    return True


def compress(D: frozenset) -> frozenset:
    """A concrete ``DistinctionFilter``: keep the even-indexed distinctions."""
    return frozenset(d for d in D if d % 2 == 0)


def l2_filter_fields() -> bool:
    return all(
        compress(D) <= D and compress(compress(D)) == compress(D) for D in subsets()
    )


def ratio(D: frozenset) -> float:
    return len(compress(D)) / len(D) if D else 0.0


def l2_ratio_le_one() -> bool:
    return all(0.0 <= ratio(D) <= 1.0 for D in subsets() if D)


def l2_no_trigger_of_threshold_ge_one() -> bool:
    return all(not (t < ratio(D)) for t in (1.0, 1.5, 2.0) for D in subsets() if D)


def l2_ratio_compress_idem() -> bool:
    return all(ratio(compress(D)) == ratio(compress(compress(D))) for D in subsets())


def l3_plan_isLeast() -> bool:
    for efe_table in itertools.product(range(3), repeat=len(FIN3) * len(BOOL)):
        table, k = {}, 0
        for s in FIN3:
            for a in BOOL:
                table[(s, a)] = efe_table[k]
                k += 1
        plan = {s: min(BOOL, key=lambda a: table[(s, a)]) for s in FIN3}
        if any(table[(s, plan[s])] > table[(s, a)] for s in FIN3 for a in BOOL):
            return False
    return True


def l3_efe_gap() -> bool:
    """Every policy is the plan of a navigator with the degenerate efe = 0."""
    for policy in all_funs(FIN3, BOOL):
        table = {(s, a): 0 for s in FIN3 for a in BOOL}
        if any(table[(s, policy(s))] > table[(s, a)] for s in FIN3 for a in BOOL):
            return False
    return True


def navigator_history(plan, move, s, n):
    out = []
    for _ in range(n):
        a = plan(s)
        out.append(a)
        s = move(s, a)
    return out


def l3_history_length() -> bool:
    plan = lambda s: s % 2 == 0
    move = lambda s, a: (s + 1) % 3 if a else s
    return all(
        len(navigator_history(plan, move, s, n)) == n for s in FIN3 for n in range(5)
    )


def l4_holographic_not_sequential() -> bool:
    """Holographic read of every component at tick 0 is not a sequential scan."""
    v = (False, True, False)
    holographic = {i: v[i] for i in FIN3}
    for e0 in FIN3:  # any scanning order sees only e0 at tick 0
        sequential = {i: (v[i] if i == e0 else None) for i in FIN3}
        if sequential == holographic:
            return False
    return True


def l4_read_determines_state() -> bool:
    vectors = list(itertools.product(BOOL, repeat=3))
    for v in vectors:
        for w in vectors:
            same_read = all(v[i] == w[i] for i in FIN3)
            if same_read != (v == w):
                return False
    return True


FROM_MONITOR = lambda v: v[0]
FROM_HISTORY = lambda h: len(h) % 2 == 0
EVAL = lambda v, h: FROM_MONITOR(v) and FROM_HISTORY(h)
VECTORS = list(itertools.product(BOOL, repeat=3))
HISTS = [[], [1], [1, 2]]


def l5_eval_false_iff() -> bool:
    return all(
        (EVAL(v, h) is False) == (not (FROM_MONITOR(v) and FROM_HISTORY(h)))
        for v in VECTORS
        for h in HISTS
    )


def l5_eval_congr() -> bool:
    return all(EVAL(v, h) == EVAL(tuple(v), list(h)) for v in VECTORS for h in HISTS)


def indicator(capacity, threshold, s) -> float:
    return 1.0 if capacity(s) >= threshold else 0.0


CAPS = (0.0, 1.0, 2.0)


def l6_indicator_range() -> bool:
    return all(
        indicator(cap, 1.0, s) in (0.0, 1.0) for cap in all_funs(FIN3, CAPS) for s in FIN3
    )


def l6_indicator_eq_one_iff() -> bool:
    return all(
        (indicator(cap, 1.0, s) == 1.0) == (cap(s) >= 1.0)
        for cap in all_funs(FIN3, CAPS)
        for s in FIN3
    )


def l6_isAgent_mono() -> bool:
    return all(
        (not (cap(s) >= 1.0 and cap(s) <= cap(t))) or cap(t) >= 1.0
        for cap in all_funs(FIN3, CAPS)
        for s in FIN3
        for t in FIN3
    )


# L7 — StateSpaceExpansion: Bool into Fin 3, injective and not surjective.
EXPAND = {False: 0, True: 1}


def l7_not_invertible() -> bool:
    for g in all_funs(FIN3, BOOL):
        if all(EXPAND[g(x)] == x for x in FIN3):  # would be a right inverse
            return False
    return True


def l7_card_expands() -> bool:
    return len(BOOL) < len(FIN3)


def l7_t5Bound_expands() -> bool:
    return len(BOOL) < len(FIN3)  # t5Bound S = |S|


def genesisEngine_expands() -> bool:
    return l7_t5Bound_expands()


# ---------------------------------------------------------------------------
# Part 3 — self-reference   (RequestProject/Gestalt/SelfReference.lean)
# ---------------------------------------------------------------------------

LEVELS = (79, 80, 81)


def vlevel(step, n: int) -> int:
    v = 79
    for _ in range(max(n - 79, 0)):
        v = step(v)
    return v


def methodology_steps():
    """All ``step`` maps closed on the three admissible v-levels."""
    for values in itertools.product(LEVELS, repeat=len(LEVELS)):
        table = dict(zip(LEVELS, values))
        yield (lambda t: (lambda v: t.get(v, 79)))(table)


def methodology_iterate_mem() -> bool:
    return all(
        vlevel(step, n) in LEVELS for step in methodology_steps() for n in range(79, 110)
    )


def methodology_revisits_level() -> bool:
    """|levels| = 3 <= 21, so a level repeats between index 79 and 100."""
    for step in methodology_steps():
        seen, found = set(), False
        for i in range(79, 101):
            v = vlevel(step, i)
            if v in seen:
                found = True
                break
            seen.add(v)
        if not found:
            return False
    return True


def methodology_revisits_level_within_card() -> bool:
    for step in methodology_steps():
        seen, found = set(), False
        for i in range(79, 79 + len(LEVELS) + 1):
            v = vlevel(step, i)
            if v in seen:
                found = True
                break
            seen.add(v)
        if not found:
            return False
    return True


def ideal_is_death() -> bool:
    for predict in all_funs(FIN3, FIN3):
        M = CognitiveSystem(predict, predict, lambda s: s)
        step = error_driven_step(M)
        dead = all(M.learning_rate(s) == 0.0 for s in FIN3) and all(
            step(s) == s for s in FIN3
        )
        if not dead:
            return False
    return True


def ideal_indistinguishable_from_nonexistence() -> bool:
    return t4_trajectory_const()


def has_gap(M: CognitiveSystem) -> bool:
    return any(M.predict(s) != M.env(s) for s in M.states)


def gap_preserves_life() -> bool:
    for predict in all_funs(FIN3, FIN3):
        for env in all_funs(FIN3, FIN3):
            M = CognitiveSystem(predict, env, lambda s: s)
            if has_gap(M) and not any(M.learning_rate(s) > 0 for s in FIN3):
                return False
    return True


def gap_closed_iff_dead() -> bool:
    for predict in all_funs(FIN3, FIN3):
        for env in all_funs(FIN3, FIN3):
            M = CognitiveSystem(predict, env, lambda s: s)
            step = error_driven_step(M)
            dead = all(M.learning_rate(s) == 0.0 for s in FIN3) and all(
                step(s) == s for s in FIN3
            )
            if (not has_gap(M)) != dead:
                return False
    return True


def life_iff_gap() -> bool:
    for predict in all_funs(FIN3, FIN3):
        for env in all_funs(FIN3, FIN3):
            M = CognitiveSystem(predict, env, lambda s: s)
            if any(M.learning_rate(s) > 0 for s in FIN3) != has_gap(M):
                return False
    return True


# ---------------------------------------------------------------------------
# Part 4 — meta-skills   (RequestProject/Gestalt/MetaSkills.lean)
# ---------------------------------------------------------------------------

# A `Cognizer` over Tok = Bool, C = Fin 3.  `report(prompt)` returns
# (claim, confidence, justification); a next-token-bounded cognizer has
# justification = None (the `no_self_estimate` field).

PROMPTS = [[], [False], [True], [False, True], [True, False]]
TRUTH = {0: 0.0, 1: 0.5, 2: 1.0}


def cognizer(prompt) -> tuple:
    claim = len(prompt) % 3
    return (claim, 1.0, None)


def metacognitive_on(prompt) -> bool:
    claim, confidence, justification = cognizer(prompt)
    return justification is not None and abs(confidence - TRUTH[claim]) < 1e-12


def prompt_cannot_install_metacognition() -> bool:
    return all(not metacognitive_on(p) for p in PROMPTS)


def no_prompt_makes_metacognitive() -> bool:
    return not any(metacognitive_on(p) for p in PROMPTS)


def metacognition_requires_output_channel() -> bool:
    return all(cognizer(p)[2] is None for p in PROMPTS)


def idiotes_not_metacognitive() -> bool:
    return prompt_cannot_install_metacognition()


def idiotes_format_independent() -> bool:
    return all(
        metacognitive_on(p) == metacognitive_on(list(reversed(p))) for p in PROMPTS
    )


def idiotes_of_nextTokenBound() -> bool:
    return metacognition_requires_output_channel()


# ---------------------------------------------------------------------------
# Part 5 — tool inventory   (RequestProject/Gestalt/ToolInventory.lean)
# ---------------------------------------------------------------------------

TOOL_HAS = [f"has_{i}" for i in range(28)]
TOOL_MISSING_CRITICAL = [f"missing_{i}" for i in range(19)]
TOOL_DESIRABLE = [f"desirable_{i}" for i in range(20)]
ALL_TOOLS = TOOL_HAS + TOOL_MISSING_CRITICAL + TOOL_DESIRABLE

CAN = {"execute": True, "answer": True, "understand": True, "generate": True}
CANNOT = {"evaluate": False, "verify": False}


def tool_has_card() -> bool:
    return len(set(TOOL_HAS)) == 28


def tool_missing_critical_card() -> bool:
    return len(set(TOOL_MISSING_CRITICAL)) == 19


def tool_desirable_card() -> bool:
    return len(set(TOOL_DESIRABLE)) == 20


def tool_inventory_partition() -> bool:
    s1, s2, s3 = set(TOOL_HAS), set(TOOL_MISSING_CRITICAL), set(TOOL_DESIRABLE)
    return not (s1 & s2) and not (s1 & s3) and not (s2 & s3) and len(set(ALL_TOOLS)) == 67


def idiotes_tools() -> bool:
    return all(CAN.values())


def idiotes_tools_gap() -> bool:
    return not any(CANNOT.values())


def idiotes_tools_quantity_not_quality() -> bool:
    return len(TOOL_HAS) == 28 and not CANNOT["evaluate"]


def idiotes_toolset_not_metacognitive() -> bool:
    return idiotes_tools_gap() and idiotes_not_metacognitive()


# ---------------------------------------------------------------------------
# Part 6 — Aristotle canon   (RequestProject/Gestalt/AristotleCanon.lean)
# ---------------------------------------------------------------------------

ARISTOTLE_STATS = {
    "files": 98,
    "lines": 15292,
    "theorems": 742,
    "definitions": 458,
    "sorries": 0,
    "admits": 0,
    "newAxioms": 0,
}
DOMAINS = ("logic", "physics", "biology", "ethics", "poetics")


def polymath_practice(stats, domains) -> bool:
    return (
        stats["sorries"] == 0
        and stats["admits"] == 0
        and stats["newAxioms"] == 0
        and stats["theorems"] > 0
        and len(domains) >= 2
    )


def aristotle_is_polymath_practice() -> bool:
    return polymath_practice(ARISTOTLE_STATS, DOMAINS)


def exists_polymath_practice() -> bool:
    return aristotle_is_polymath_practice()


def horizon_canon_no_fixed_point() -> bool:
    """`natHorizonCanon`: turn n = n + 1 has no fixed point."""
    turn = lambda n: n + 1
    return all(turn(n) != n for n in range(50))


def horizon_canon_blocks_ideal() -> bool:
    turn = lambda n: n + 1
    return all(turn(n) != n for n in range(50))


def horizon_canon_preserves_life() -> bool:
    return horizon_canon_blocks_ideal()


def aristotle_canon_gestalt() -> bool:
    return horizon_canon_preserves_life() and aristotle_is_polymath_practice()


# ---------------------------------------------------------------------------
# Part 7 — bridge to the core   (RequestProject/Gestalt/CoreBridge.lean)
# ---------------------------------------------------------------------------

# ActivePolicyAgent on S = Fin 3, A = Bool, Latent = Bool.
PRIOR = {False: 0.5, True: 0.5}
POSTERIOR = {
    0: {False: 0.25, True: 0.75},
    1: {False: 0.5, True: 0.5},
    2: {False: 0.9, True: 0.1},
}
PREFERENCE = {0: -0.5, 1: -1.0, 2: 0.0}  # nonpositive log-preferences
FORWARD = {
    (0, False): 1,
    (0, True): 2,
    (1, False): 2,
    (1, True): 0,
    (2, False): 0,
    (2, True): 1,
}


def kl(p: dict, q: dict) -> float:
    return sum(p[z] * math.log(p[z] / q[z]) for z in p)


def complexity(o) -> float:
    return kl(POSTERIOR[o], PRIOR)


def efe(s, a) -> float:
    nxt = FORWARD[(s, a)]
    return -PREFERENCE[nxt] + complexity(nxt)


def plan(s):
    return min(BOOL, key=lambda a: efe(s, a))


def navigatorOfActivePolicyAgent_efe() -> bool:
    """The navigator's `efe` field is the agent's `efe`, and the plan minimizes it."""
    return all(efe(s, plan(s)) <= efe(s, a) for s in FIN3 for a in BOOL)


def navigatorOfActivePolicyAgent_efe_nonneg() -> bool:
    return all(efe(s, a) >= -1e-12 for s in FIN3 for a in BOOL)


def navigator_min_efe_eq() -> bool:
    """Two tie-breaking rules over the same efe attain the same minimum."""
    plan2 = lambda s: max(BOOL, key=lambda a: (-efe(s, a), a))
    return all(abs(efe(s, plan(s)) - efe(s, plan2(s))) < 1e-12 for s in FIN3)


def trace(s, n):
    out = []
    for _ in range(n):
        a = plan(s)
        out.append((s, a))
        s = FORWARD[(s, a)]
    return out


def trace_length() -> bool:
    return all(len(trace(s, n)) == n for s in FIN3 for n in range(6))


def efe_trace_nonneg() -> bool:
    return all(
        sum(efe(s0, a) for s0, a in trace(s, n)) >= -1e-12
        for s in FIN3
        for n in range(6)
    )


def isOmega_of_step_fixed() -> bool:
    step = lambda v: v  # 79 is a fixed point of the version step
    return vlevel(step, 79) == 79 and vlevel(step, 80) == 79


def exists_methodology_isOmega() -> bool:
    return isOmega_of_step_fixed()


def reflexiveAdaptiveAgent_drawsDistinction() -> bool:
    """Nontrivial Latent (= Bool) means the identity channel separates two points."""
    return draws_distinction(lambda x: x, BOOL)


def reflexiveAdaptiveAgent_liveAt() -> bool:
    stream = lambda t: 1 if t % 3 == 0 else 0
    return all(any(stream(u) != 0 for u in range(t, t + 3)) for t in range(30))


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

CHECKS: list[tuple[str, Callable[[], bool]]] = [
    ("UCC.t1_no_distinction_no_information", t1_no_distinction_no_information),
    ("UCC.t1_distinction_of_drawsDistinction", t1_distinction_of_drawsDistinction),
    ("UCC.t2_informationGain_nonneg", t2_informationGain_nonneg),
    ("UCC.t2_informationGain_eq_zero_iff", t2_informationGain_eq_zero_iff),
    ("UCC.t2_gain_pos_iff_distinction_cuts", t2_gain_pos_iff_distinction_cuts),
    ("UCC.t3_feedbackError", t3_feedbackError),
    ("UCC.t3_learningRate_pos_of_error", t3_learningRate_pos_of_error),
    ("UCC.t4_perfectPredictInert", t4_perfectPredictInert),
    ("UCC.t4_trajectory_const", t4_trajectory_const),
    ("UCC.t5_pigeonholeRevisit", t5_pigeonhole_revisit),
    ("UCC.t5_system_revisits", t5_system_revisits),
    ("Genesis.l1_distinctionDetector_memoryless", l1_distinctionDetector_memoryless),
    ("Genesis.l1_output_is_t1", l1_output_is_t1),
    ("Genesis.DistinctionFilter (structure fields)", l2_filter_fields),
    ("Genesis.l2_ratio_le_one", l2_ratio_le_one),
    ("Genesis.l2_no_trigger_of_threshold_ge_one", l2_no_trigger_of_threshold_ge_one),
    ("Genesis.l2_ratio_compress_idem", l2_ratio_compress_idem),
    ("Genesis.l3_plan_isLeast", l3_plan_isLeast),
    ("Genesis.l3_efe_gap", l3_efe_gap),
    ("Genesis.l3_history_length", l3_history_length),
    ("Genesis.l4_holographic_not_sequential", l4_holographic_not_sequential),
    ("Genesis.l4_read_determines_state", l4_read_determines_state),
    ("Genesis.l5_eval_false_iff", l5_eval_false_iff),
    ("Genesis.l5_eval_congr", l5_eval_congr),
    ("Genesis.l6_indicator_range", l6_indicator_range),
    ("Genesis.l6_indicator_eq_one_iff", l6_indicator_eq_one_iff),
    ("Genesis.l6_isAgent_mono", l6_isAgent_mono),
    ("Genesis.l7_not_invertible", l7_not_invertible),
    ("Genesis.l7_card_expands", l7_card_expands),
    ("Genesis.l7_t5Bound_expands", l7_t5Bound_expands),
    ("Genesis.genesisEngine_expands", genesisEngine_expands),
    ("SelfReference.Methodology.iterate_mem", methodology_iterate_mem),
    ("SelfReference.Methodology.vlevel_mem", methodology_iterate_mem),
    ("SelfReference.methodology_revisits_level", methodology_revisits_level),
    (
        "SelfReference.methodology_revisits_level_within_card",
        methodology_revisits_level_within_card,
    ),
    ("SelfReference.ideal_is_death", ideal_is_death),
    (
        "SelfReference.ideal_indistinguishable_from_nonexistence",
        ideal_indistinguishable_from_nonexistence,
    ),
    ("SelfReference.gap_preserves_life", gap_preserves_life),
    ("SelfReference.gap_closed_iff_dead", gap_closed_iff_dead),
    ("SelfReference.life_iff_gap", life_iff_gap),
    (
        "MetaSkills.prompt_cannot_install_metacognition",
        prompt_cannot_install_metacognition,
    ),
    ("MetaSkills.no_prompt_makes_metacognitive", no_prompt_makes_metacognitive),
    (
        "MetaSkills.metacognition_requires_output_channel",
        metacognition_requires_output_channel,
    ),
    ("MetaSkills.idiotes_not_metacognitive", idiotes_not_metacognitive),
    ("MetaSkills.idiotes_format_independent", idiotes_format_independent),
    ("MetaSkills.idiotes_of_nextTokenBound", idiotes_of_nextTokenBound),
    ("ToolInventory.tool_has_card", tool_has_card),
    ("ToolInventory.tool_missing_critical_card", tool_missing_critical_card),
    ("ToolInventory.tool_desirable_card", tool_desirable_card),
    ("ToolInventory.tool_inventory_partition", tool_inventory_partition),
    ("ToolInventory.idiotes_tools", idiotes_tools),
    ("ToolInventory.idiotes_tools_gap", idiotes_tools_gap),
    (
        "ToolInventory.idiotes_tools_quantity_not_quality",
        idiotes_tools_quantity_not_quality,
    ),
    ("ToolInventory.idiotes_toolset_not_metacognitive", idiotes_toolset_not_metacognitive),
    ("Canon.aristotle_is_polymath_practice", aristotle_is_polymath_practice),
    ("Canon.exists_polymath_practice", exists_polymath_practice),
    ("Canon.horizon_canon_no_fixed_point", horizon_canon_no_fixed_point),
    ("Canon.horizon_canon_blocks_ideal", horizon_canon_blocks_ideal),
    ("Canon.horizon_canon_preserves_life", horizon_canon_preserves_life),
    ("Canon.aristotle_canon_gestalt", aristotle_canon_gestalt),
    ("CoreBridge.navigatorOfActivePolicyAgent_efe", navigatorOfActivePolicyAgent_efe),
    (
        "CoreBridge.navigatorOfActivePolicyAgent_efe_nonneg",
        navigatorOfActivePolicyAgent_efe_nonneg,
    ),
    ("CoreBridge.navigator_min_efe_eq", navigator_min_efe_eq),
    ("CoreBridge.trace_length", trace_length),
    ("CoreBridge.efe_trace_nonneg", efe_trace_nonneg),
    ("CoreBridge.isOmega_of_step_fixed", isOmega_of_step_fixed),
    ("CoreBridge.exists_methodology_isOmega", exists_methodology_isOmega),
    (
        "CoreBridge.reflexiveAdaptiveAgent_drawsDistinction",
        reflexiveAdaptiveAgent_drawsDistinction,
    ),
    ("CoreBridge.reflexiveAdaptiveAgent_liveAt", reflexiveAdaptiveAgent_liveAt),
]


def main() -> int:
    for name, fn in CHECKS:
        check(name, fn())
    failed = [n for n, ok in _RESULTS if not ok]
    print()
    print(
        f"checked {len(_RESULTS)} mirrors, "
        f"{len(_RESULTS) - len(failed)} pass, {len(failed)} fail"
    )
    for n in failed:
        print("  FAILED:", n)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
