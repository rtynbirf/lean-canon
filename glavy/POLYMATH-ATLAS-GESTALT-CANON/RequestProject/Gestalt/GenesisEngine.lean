/-
# POLYMATH_ATLAS_GESTALT — Part 2.  The Genesis Engine, layers L1–L7.

Source: **POLYMATH ATLAS v6 Final Report**, the seven-layer Genesis Engine, read
together with the **Status Report** (which identifies EFE as the critical gap of
the Combine verify layer).

Each layer is an *interface*: a `structure` whose fields are the data the layer
provides plus the properties the informal text demands of it.  No bare axiom is
used — every postulate of the informal source is a structure field, so that a
concrete engine has to exhibit it.

All statements in this file are fully proved: no `sorry` remains.
-/
import RequestProject.Gestalt.UCC

namespace PolymathAtlas.Gestalt.Genesis

open PolymathAtlas.Core (Distinction)
open PolymathAtlas.Gestalt.UCC

/-! ## L1 — Reactor -/

/-- **POLYMATH ATLAS v6, Layer 1 — Reactor.  Maps to UCC T1.**

The nuclear layer.  Takes raw input and produces primitive distinctions; its
output type is `Set (Distinction S)`.  No memory, no learning — pure atomic
distinction, i.e. a plain function of the *current* input only. -/
structure DistinctionDetector (I S : Type*) where
  /-- The primitive distinctions fired by one raw input. -/
  distinctions : I → Set (Distinction S)

namespace DistinctionDetector

variable {I S : Type*}

/-- The reactor seen as a processor of input *histories* (most recent input
first).  Used to state the "no memory" property of L1 against the general shape
of a stateful layer.  POLYMATH ATLAS v6, Layer 1. -/
def onHistory (R : DistinctionDetector I S) : List I → Set (Distinction S)
  | [] => ∅
  | i :: _ => R.distinctions i

end DistinctionDetector

/-- A history processor is **memoryless** when its output depends on the most
recent input alone.  POLYMATH ATLAS v6, Layer 1 — Reactor ("no memory, no
learning"). -/
def Memoryless {I S : Type*} (F : List I → Set (Distinction S)) : Prop :=
  ∀ h h' : List I, h.head? = h'.head? → F h = F h'

/-- **POLYMATH ATLAS v6, Layer 1 — Reactor.  Maps to UCC T1.**

The reactor is memoryless: nothing but the current raw input influences the
primitive distinctions it fires. -/
theorem l1_distinctionDetector_memoryless {I S : Type*} (R : DistinctionDetector I S) :
    Memoryless R.onHistory := by
  intro h h' hh
  cases h with
  | nil =>
      cases h' with
      | nil => rfl
      | cons b u => simp at hh
  | cons a t =>
      cases h' with
      | nil => simp at hh
      | cons b u =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          rfl

/-- **POLYMATH ATLAS v6, Layer 1 — Reactor.  Maps to UCC T1.**

The bridge to the Universal Cognition Cycle: every distinction produced by the
reactor is a genuine T1 distinction, i.e. it really cuts the state space into a
non-empty inside and a non-empty outside.  (Membership in the fired set is not
needed for the conclusion — it holds of every `Distinction` — so the statement is
phrased as a bounded quantifier over the layer's output.) -/
theorem l1_output_is_t1 {I S : Type*} (R : DistinctionDetector I S) (i : I) :
    ∀ d ∈ R.distinctions i, d.inside ≠ d.outside :=
  fun d _ => PolymathAtlas.Core.distinction_nontrivial d

/-! ## L2 — Compressor -/

/-- **POLYMATH ATLAS v6, Layer 2 — Compressor.  EFE (Expected Free Energy)
threshold is the trigger for the L2→L3 transition.**

Takes the distinctions produced by L1 and compresses them by filtering noise and
merging redundant distinctions.  The two fields record the informal
requirements: compression only ever *removes* (`compress_subset`), and
recompressing a compressed set changes nothing (`compress_idem`). -/
structure DistinctionFilter (S : Type*) where
  /-- The compressed distinction set. -/
  compress : Set (Distinction S) → Set (Distinction S)
  /-- Compression filters: it never invents a distinction L1 did not fire. -/
  compress_subset : ∀ D, compress D ⊆ D
  /-- Compression is a normal form: nothing is left to merge afterwards. -/
  compress_idem : ∀ D, compress (compress D) = compress D

namespace DistinctionFilter

variable {S : Type*}

/-- The compression ratio achieved on a distinction set: surviving distinctions
per input distinction.  POLYMATH ATLAS v6, Layer 2. -/
noncomputable def ratio (C : DistinctionFilter S) (D : Set (Distinction S)) : ℝ :=
  ((C.compress D).ncard : ℝ) / (D.ncard : ℝ)

/-- The critical transition point of the Genesis Engine: when the compression
ratio exceeds the EFE threshold, L2 hands control to L3.  POLYMATH ATLAS v6,
Layer 2 — "EFE threshold is the trigger for the L2→L3 transition". -/
def TriggersNavigator (C : DistinctionFilter S) (efeThreshold : ℝ) (D : Set (Distinction S)) : Prop :=
  efeThreshold < C.ratio D

end DistinctionFilter

/-- **POLYMATH ATLAS v6, Layer 2 — Compressor.  EFE threshold is the trigger for
the L2→L3 transition.**

Compression never inflates: on a finite, non-empty distinction set the ratio
lies in `[0,1]`. -/
theorem l2_ratio_le_one {S : Type*} (C : DistinctionFilter S) {D : Set (Distinction S)}
    (hfin : D.Finite) (hne : D.Nonempty) : 0 ≤ C.ratio D ∧ C.ratio D ≤ 1 := by
  have hpos : 0 < D.ncard := (Set.ncard_pos hfin).mpr hne
  have hposR : (0 : ℝ) < (D.ncard : ℝ) := by exact_mod_cast hpos
  have hle : (C.compress D).ncard ≤ D.ncard := Set.ncard_le_ncard (C.compress_subset D) hfin
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hposR)
  · rw [DistinctionFilter.ratio, div_le_one hposR]
    exact_mod_cast hle

/-- **POLYMATH ATLAS v6, Layer 2 — Compressor.  EFE threshold is the trigger for
the L2→L3 transition.**

A threshold at or above `1` can never fire the L2→L3 transition on a finite
input: the trigger is meaningful only for EFE thresholds strictly below `1`. -/
theorem l2_no_trigger_of_threshold_ge_one {S : Type*} (C : DistinctionFilter S) {t : ℝ}
    (ht : 1 ≤ t) {D : Set (Distinction S)} (hfin : D.Finite) (hne : D.Nonempty) :
    ¬ C.TriggersNavigator t D := by
  intro htrig
  exact absurd (lt_of_le_of_lt ht htrig) (not_lt.mpr (l2_ratio_le_one C hfin hne).2)

/-- **POLYMATH ATLAS v6, Layer 2 — Compressor.  EFE threshold is the trigger for
the L2→L3 transition.**

Compression is a projection: the second pass gains nothing, so the L2→L3 trigger
evaluates identically on `D` and on `compress D` once the fixed point is
reached. -/
theorem l2_ratio_compress_idem {S : Type*} (C : DistinctionFilter S) (D : Set (Distinction S)) :
    C.ratio (C.compress D) = C.ratio (C.compress (C.compress D)) := by
  rw [C.compress_idem D]

/-! ## L3 — Navigator -/

/-- **POLYMATH ATLAS v6, Layer 3 — Navigator.  EFE threshold.  The Status Report
identifies EFE as absent from the Combine architecture.**

Takes compressed distinctions and navigates the state space, using Expected Free
Energy as its decision criterion: the chosen action minimizes expected free
energy.  `plan_minimizes` is exactly that criterion, as a field rather than an
axiom.  THIS IS THE CRITICAL GAP: a verify layer without an `efe` field cannot
express `plan_minimizes` at all. -/
structure Navigator (S A : Type*) where
  /-- Expected Free Energy of taking an action in a state. -/
  efe : S → A → ℝ
  /-- The action the navigator chooses. -/
  plan : S → A
  /-- The EFE decision criterion. -/
  plan_minimizes : ∀ s a, efe s (plan s) ≤ efe s a

namespace Navigator

variable {S A : Type*}

/-- The navigation history: the actions chosen along the trajectory driven by a
transition map.  Feeds the L5 genesis conditions.  POLYMATH ATLAS v6, Layer 3. -/
def history (N : Navigator S A) (move : S → A → S) (s : S) : ℕ → List A
  | 0 => []
  | n + 1 => N.plan s :: N.history move (move s (N.plan s)) n

end Navigator

/-- **POLYMATH ATLAS v6, Layer 3 — Navigator.  EFE threshold.  The Status Report
identifies EFE as absent from the Combine architecture.**

The planned action realizes the least expected free energy available in the
current state. -/
theorem l3_plan_isLeast {S A : Type*} (N : Navigator S A) (s : S) :
    IsLeast (Set.range (N.efe s)) (N.efe s (N.plan s)) := by
  refine ⟨⟨N.plan s, rfl⟩, ?_⟩
  rintro x ⟨a, rfl⟩
  exact N.plan_minimizes s a

/-- **POLYMATH ATLAS v6, Layer 3 — Navigator.  EFE threshold.  The Status Report
identifies EFE as absent from the Combine architecture.**

Formal statement of the critical gap: an architecture that only records *which*
action it takes, with no expected-free-energy functional attached, cannot
distinguish an EFE-minimizing navigator from an arbitrary policy — every policy
is the `plan` field of some navigator for a suitably degenerate `efe`.  Hence
"choose the action minimizing EFE" carries no content until EFE is supplied. -/
theorem l3_efe_gap {S A : Type*} (policy : S → A) :
    ∃ N : Navigator S A, N.plan = policy :=
  ⟨{ efe := fun _ _ => 0, plan := policy, plan_minimizes := fun _ _ => le_refl 0 }, rfl⟩

/-- **POLYMATH ATLAS v6, Layer 3 — Navigator.  EFE threshold.**

The navigation history has exactly the requested length; it is the finite record
that L5 consumes. -/
theorem l3_history_length {S A : Type*} (N : Navigator S A) (move : S → A → S) (s : S) (n : ℕ) :
    (N.history move s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [Navigator.history, ih]

/-! ## L4 — Holographic Monitor -/

/-- **POLYMATH ATLAS v6, Layer 4 — Holographic Monitor.**

A monitor of a system whose state is a vector `Ix → S` of component states.
`read t v i` is what the monitor knows, at tick `t`, about component `i` of the
full state vector `v`. -/
structure Monitor (Ix S : Type*) where
  /-- What the monitor knows about each component at each tick. -/
  read : ℕ → (Ix → S) → Ix → Option S

/-- **POLYMATH ATLAS v6, Layer 4 — Holographic Monitor.**

Simultaneous observation of all system states: the whole state vector is
available already at the first tick — parallel access, not a scan. -/
def Holographic {Ix S : Type*} (M : Monitor Ix S) : Prop :=
  ∀ v i, M.read 0 v i = some (v i)

/-- **POLYMATH ATLAS v6, Layer 4 — Holographic Monitor.**

The contrasting mode: a sequential scan visiting the component `e t` at tick `t`
and seeing nothing else. -/
def SequentialScan {Ix S : Type*} (M : Monitor Ix S) (e : ℕ → Ix) : Prop :=
  (∀ t v, M.read t v (e t) = some (v (e t))) ∧ (∀ t v i, e t ≠ i → M.read t v i = none)

/-- **POLYMATH ATLAS v6, Layer 4 — Holographic Monitor.**

Holographic observation is *not* a sequential scan: as soon as the system has
more than one component, no scanning order reproduces parallel access to the
full state vector. -/
theorem l4_holographic_not_sequential {Ix S : Type*} [Nontrivial Ix] [Nonempty S] (M : Monitor Ix S)
    (e : ℕ → Ix) (h : Holographic M) : ¬ SequentialScan M e := by
  rintro ⟨-, hnone⟩
  obtain ⟨s₀⟩ := ‹Nonempty S›
  obtain ⟨i, hi⟩ := exists_ne (e 0)
  have h1 := h (fun _ => s₀) i
  have h2 := hnone 0 (fun _ => s₀) i (Ne.symm hi)
  rw [h1] at h2
  exact Option.some_ne_none _ h2

/-- **POLYMATH ATLAS v6, Layer 4 — Holographic Monitor.**

The monitor's first-tick output determines the entire state vector; this is the
input on which L5 evaluates the genesis condition. -/
theorem l4_read_determines_state {Ix S : Type*} (M : Monitor Ix S) (h : Holographic M)
    {v w : Ix → S} (hvw : M.read 0 v = M.read 0 w) : v = w := by
  funext i
  have hv := h v i
  have hw := h w i
  have hi := congrFun hvw i
  rw [hv, hw] at hi
  exact Option.some.inj hi

/-! ## L5 — Genesis Conditions -/

/-- **POLYMATH ATLAS v6, Layer 5 — Genesis Conditions.**

Evaluates whether the current state satisfies all preconditions of a genesis
event, and returns a boolean.  The conditions are derived from the L4 output
(the full state vector) together with the L3 navigation history; the field
`eval_iff` ties the boolean verdict to those two components. -/
structure GenesisConditions (Ix S A : Type*) where
  /-- The part of the precondition read off the holographic monitor (L4). -/
  fromMonitor : (Ix → S) → Prop
  /-- The part of the precondition read off the navigation history (L3). -/
  fromHistory : List A → Prop
  /-- The boolean verdict of the layer. -/
  eval : (Ix → S) → List A → Bool
  /-- The verdict is exactly the conjunction of the two derived conditions. -/
  eval_iff : ∀ v h, eval v h = true ↔ (fromMonitor v ∧ fromHistory h)

/-- **POLYMATH ATLAS v6, Layer 5 — Genesis Conditions.**

The verdict is `false` exactly when one of the two derived preconditions
fails — the layer hides no third source of information. -/
theorem l5_eval_false_iff {Ix S A : Type*} (G : GenesisConditions Ix S A)
    (v : Ix → S) (h : List A) :
    G.eval v h = false ↔ ¬ (G.fromMonitor v ∧ G.fromHistory h) := by
  constructor
  · intro hf hc
    have htrue := (G.eval_iff v h).mpr hc
    rw [hf] at htrue
    exact Bool.noConfusion htrue
  · intro hn
    cases hb : G.eval v h with
    | false => rfl
    | true => exact absurd ((G.eval_iff v h).mp hb) hn

/-- **POLYMATH ATLAS v6, Layer 5 — Genesis Conditions.**

`GenesisConditions` is derived from L4 + L3: systems agreeing on the monitored
state vector and on the navigation history receive the same verdict. -/
theorem l5_eval_congr {Ix S A : Type*} (G : GenesisConditions Ix S A)
    {v w : Ix → S} {h k : List A} (hv : v = w) (hh : h = k) :
    G.eval v h = G.eval w k := by
  rw [hv, hh]

/-! ## L6 — Minimal Intelligence -/

/-- **POLYMATH ATLAS v6, Layer 6 — Minimal Intelligence.**

The minimum viable cognitive state.  Below the threshold the system is not an
agent — it is a rock; above it, agency emerges.  This is a *threshold* function,
not a gradual scale. -/
structure MinimalIntelligence (S : Type*) where
  /-- The measured cognitive capacity of a state. -/
  capacity : S → ℝ
  /-- The minimal viable level. -/
  threshold : ℝ

namespace MinimalIntelligence

variable {S : Type*}

/-- Agency: the state reaches the minimal-intelligence threshold.  POLYMATH
ATLAS v6, Layer 6. -/
def IsAgent (M : MinimalIntelligence S) (s : S) : Prop := M.threshold ≤ M.capacity s

/-- The all-or-nothing verdict of L6.  POLYMATH ATLAS v6, Layer 6 — "this is a
threshold function, not a gradual scale". -/
noncomputable def indicator (M : MinimalIntelligence S) (s : S) : ℝ :=
  haveI := Classical.dec (M.IsAgent s)
  if M.IsAgent s then 1 else 0

end MinimalIntelligence

/-- **POLYMATH ATLAS v6, Layer 6 — Minimal Intelligence.**

Agency is not a gradual scale: the L6 verdict takes only the two values `0`
(rock) and `1` (agent). -/
theorem l6_indicator_range {S : Type*} (M : MinimalIntelligence S) :
    Set.range M.indicator ⊆ ({0, 1} : Set ℝ) := by
  rintro x ⟨s, rfl⟩
  unfold MinimalIntelligence.indicator
  split <;> simp

/-- **POLYMATH ATLAS v6, Layer 6 — Minimal Intelligence.**

The verdict is `1` exactly for agents, `0` exactly for rocks. -/
theorem l6_indicator_eq_one_iff {S : Type*} (M : MinimalIntelligence S) (s : S) :
    M.indicator s = 1 ↔ M.IsAgent s := by
  unfold MinimalIntelligence.indicator
  split_ifs with hagent
  · simp [hagent]
  · simp only [zero_ne_one, false_iff]
    exact hagent

/-- **POLYMATH ATLAS v6, Layer 6 — Minimal Intelligence.**

Monotonicity of the threshold: more capacity never destroys agency. -/
theorem l6_isAgent_mono {S : Type*} (M : MinimalIntelligence S) {s t : S}
    (h : M.capacity s ≤ M.capacity t) (hs : M.IsAgent s) : M.IsAgent t :=
  le_trans hs h

/-! ## L7 — Genesis Event -/

/-- **POLYMATH ATLAS v6, Layer 7 — Genesis Event.  After genesis, the UCC
restarts with an expanded state space.**

The event itself: a phase transition of the state space.  It embeds the old
space into a strictly larger new one (`embed`, `not_surjective`), so it is a
*non-invertible* state transformation: information about the new level cannot be
pulled back to the old one. -/
structure StateSpaceExpansion (S S' : Type*) where
  /-- The transformation of the state space. -/
  transform : S → S'
  /-- Nothing already distinguished is lost. -/
  embed : Function.Injective transform
  /-- The new level is genuinely new: the transformation is onto nothing. -/
  not_surjective : ¬ Function.Surjective transform

/-- **POLYMATH ATLAS v6, Layer 7 — Genesis Event.  After genesis, the UCC
restarts with an expanded state space.**

The genesis event is non-invertible: no map back can undo it on both sides. -/
theorem l7_not_invertible {S S' : Type*} (E : StateSpaceExpansion S S') :
    ¬ ∃ g : S' → S, Function.LeftInverse g E.transform ∧ Function.RightInverse g E.transform := by
  rintro ⟨g, -, hright⟩
  exact E.not_surjective hright.surjective

/-- **POLYMATH ATLAS v6, Layer 7 — Genesis Event.  After genesis, the UCC
restarts with an expanded state space.**

The state space really expands: `|S| < |S'|`. -/
theorem l7_card_expands {S S' : Type*} [Fintype S] [Fintype S'] (E : StateSpaceExpansion S S') :
    Fintype.card S < Fintype.card S' := by
  have hle : Fintype.card S ≤ Fintype.card S' := Fintype.card_le_of_injective _ E.embed
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd
      ((Fintype.bijective_iff_injective_and_card E.transform).mpr ⟨E.embed, heq⟩).surjective
      E.not_surjective

/-- **POLYMATH ATLAS v6, Layer 7 — Genesis Event.  After genesis, the UCC
restarts with an expanded state space.**

The link back to T5: after the genesis event the UCC restarts at T1, but the
pigeonhole horizon before a state necessarily recurs has strictly grown. -/
theorem l7_t5Bound_expands {S S' : Type*} [Fintype S] [Fintype S'] (E : StateSpaceExpansion S S') :
    UCC.t5Bound S < UCC.t5Bound S' :=
  l7_card_expands E

/-! ## The engine as a whole -/

/-- **POLYMATH ATLAS v6 — the Genesis Engine.**

The seven layers assembled into one interface: L1 fires distinctions, L2
compresses them, L3 navigates by EFE, L4 monitors holographically, L5 evaluates
the genesis condition, L6 decides agency, L7 performs the phase transition. -/
structure GenesisEngine (I Ix S A S' : Type*) where
  /-- L1. -/ reactor : DistinctionDetector I S
  /-- L2. -/ compressor : DistinctionFilter S
  /-- L3. -/ navigator : Navigator S A
  /-- L4. -/ monitor : Monitor Ix S
  /-- L4 is holographic. -/ monitor_holographic : Holographic monitor
  /-- L5. -/ conditions : GenesisConditions Ix S A
  /-- L6. -/ minimalIntelligence : MinimalIntelligence S
  /-- L7. -/ expansion : StateSpaceExpansion S S'

/-- **POLYMATH ATLAS v6 — the Genesis Engine.**

The engine's own closure statement: the L7 event carries the system to a strictly
larger state space, i.e. the UCC restarts with an expanded `|S|`.  The L5 verdict
is not a hypothesis of the expansion: exhibiting a `GenesisEngine` already
requires exhibiting the L7 `StateSpaceExpansion`, and that alone forces
`|S| < |S'|`. -/
theorem genesisEngine_expands {I Ix S A S' : Type*} [Fintype S] [Fintype S']
    (E : GenesisEngine I Ix S A S') : UCC.t5Bound S < UCC.t5Bound S' :=
  l7_t5Bound_expands E.expansion

end PolymathAtlas.Gestalt.Genesis
