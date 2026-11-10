# POLYMATH-ATLAS — formal map of the L1–L7 audit items

**Scope note.** The file `POLYMATH_ATLAS_V100_AUDIT.txt` (items #3341–#3370) is *not
present in this repository*, so this map covers only the audit items whose content was
supplied in the request, plus a complete layer-by-layer map of L1–L7 onto the Lean
declarations that now exist. Items #3346–#3348, #3350–#3357, #3359–#3360, #3362–#3364,
#3366–#3368 and #3370 are listed as **unmapped** rather than guessed: their text was not
available, and inventing a classification for them would be worse than leaving the row
open. Once the audit text is added to the repository the remaining rows can be filled in
mechanically.

Buckets:

* **A — already formalized**: the claim corresponds to an existing structure/theorem.
* **B — formalizable, now formalized**: a new Lean declaration was added for it.
* **C — philosophical**: no clear mathematical content; no Lean counterpart.
* **? — unmapped**: audit text unavailable in this repository.

All references below are to `RequestProject/AdaptiveAgent.lean` unless stated otherwise.

| # | bucket | Lean counterpart |
|---|--------|------------------|
| #3341 | A | `ObservationStream` (`abbrev ObservationStream := ℕ → Observation`), `Observation` — a stream of tuples over discrete time |
| #3342 | A | `Observation` — the tuple `⟨channel, value⟩` |
| #3343 | C | «no representations at L1» is a methodological stance, not a proposition about the objects; nothing to state |
| #3344 | A | `Live`, `LiveAt`, and the liveness field `StreamTransformer.live_apply` |
| #3345 | B | **new**: `live_truncate_of_live` — liveness is a tail property, so truncating a live stream leaves it live. Companion: `live_iff_setOf_active_infinite` (liveness ⇔ the active-time set is infinite) |
| #3346–#3348 | ? | audit text not present in the repository |
| #3349 | A | `ActivePolicyAgent.efe`, `ActivePolicyAgent.efe_nonneg`; accumulation along a plan: `ActivePolicyAgent.efe_foldl_ge_init`, `ActivePolicyAgent.efe_foldl_nonneg_of_init_nonneg` |
| #3350–#3357 | ? | audit text not present in the repository |
| #3358 | B | **new**: `KLContinuityBound` (a Lipschitz-style bound on the posterior map measured in relative entropy) with `KLContinuityBound.mul_nonneg` and `KLContinuityBound.nonneg_of_pos`. Underlying: `klDiv`, `klDiv_nonneg` (Gibbs' inequality), `VariationalFamily.posteriorDiv` |
| #3359–#3360 | ? | audit text not present in the repository |
| #3361 | A | `AdaptivePreconditions` (C1 liveness, C2 planner optimality, C3 genuine compression) with `neg_adaptivePreconditions_of_neg_c1`, `…_c2`, `…_c3` |
| #3362–#3364 | ? | audit text not present in the repository |
| #3365 | A | `AdaptiveAgentSpec` (the three preconditions + `acts` + `bounded`), with `AdaptiveAgentSpec.live_at`, `AdaptiveAgentSpec.exists_nonneg_bound`, `neg_adaptiveAgentSpec_of_neg_live_at` |
| #3366–#3368 | ? | audit text not present in the repository |
| #3369 | A/B | `SelfMap` (alias `Endomap`), `exists_fixed_point_selfMap` (Knaster–Tarski). **Correction:** the unrestricted claim "the self-map operator always has a fixed point" is *false* — `not_forall_exists_fixed_point_selfMap` proves it, using `Bool.not` as a counterexample. It was previously carried as an axiom; it is now a theorem in its correct (monotone) form, so the project has no custom axiom |
| #3370 | ? | audit text not present in the repository |

## Layer map L1–L7

| layer | informal description | Lean |
|-------|----------------------|------|
| L1 | stream of raw tuples; liveness | `Observation`, `ObservationStream`, `Active`, `LiveAt`, `Live`, `StreamTransformer` (+ `StreamTransformer.id`, `.comp`, `comp_assoc`), `truncate`, `live_truncate_of_live`, `live_iff_setOf_active_infinite` |
| L2 | compression / variational inference | `klDiv`, `klDiv_self`, `klDiv_nonneg`, `VariationalFamily`, `VariationalFamily.complexity`, `complexity_nonneg`, `posteriorDiv`, `posteriorDiv_nonneg`, `KLContinuityBound` |
| L3 | action selection by expected free energy | `ActivePolicyAgent`, `risk`, `risk_nonneg`, `ambiguity`, `ambiguity_nonneg`, `efe`, `efe_nonneg`, `efe_foldl_ge_init`, `efe_foldl_nonneg_of_init_nonneg`, `trajectory`, `trajectory_eq_of_fixed` |
| L4 | meta-optimization | `SelfMap`, `Endomap`, `MetaOptimizer`, `exists_fixed_point_selfMap`, `exists_fixed_point_of_idempotent`, `not_forall_exists_fixed_point_selfMap` |
| L5 | the three necessary preconditions | `AdaptivePreconditions`, `neg_adaptivePreconditions_of_neg_c1/_c2/_c3` |
| L6 | the five-condition agent specification | `AdaptiveAgentSpec`, `AdaptiveAgentSpec.live`, `.live_at`, `.exists_nonneg_bound`, `neg_adaptiveAgentSpec_of_neg_live_at` |
| L7 | reflexive closure / self-reference | `ReflexiveAdaptiveAgent`, `.adaptive_agent_spec`, `.adaptive_preconditions`, `.live_at`, `.self_nontrivial`, `.exists_fixed_point_metaUpdate` |
| witness | the theory is non-vacuous | `RequestProject/ExampleAdaptiveAgent.lean`: `pulse`, `uniformFamily`, `flipAgent`, `flipAgent_spec`, `flipReflexive` |

## Items with no mathematical content

Claims of the form "intelligence is a process, not a substance", "there are no
representations at L1", or "self-reference is what it is like to be a model" are
**[PHILOSOPHICAL — no Lean formalization]**: they fix a vocabulary rather than assert
something that can be true or false about the formal objects. Where such a claim does
constrain the objects, the constraint itself was formalized instead — e.g. "the system
must not die" became `Live`, and "the self-model must not be degenerate" became
`ReflexiveAdaptiveAgent.self_ne` together with `self_nontrivial`.
