/-
# POLYMATH_ATLAS_GESTALT — Part 1.  UCC: the Universal Cognition Cycle.

Source documents referenced by the docstrings of this file:

* **POLYMATH ATLAS Status Report** — theorems T1–T5 of the Universal Cognition
  Cycle (the "engineering tail" of the gestalt);
* **POLYMATH ATLAS v6 Final Report** — the Genesis Engine layers L1–L7 (the
  "philosophical head"), formalized in `RequestProject/Gestalt/GenesisEngine.lean`.

Every statement is stated in full, with its informal source recorded in the
docstring, and every proof is complete: no `sorry` remains.
No new axiom is introduced anywhere: wherever the informal text postulates a
property of a system, the property is a **field of a `structure`**, so that a
concrete system has to exhibit it.

The `Distinction` type is *not* redefined here — the project already contains it
in `RequestProject/UCC.lean` (`PolymathAtlas.Core.Distinction`) and it is reused.
-/
import RequestProject.UCC

namespace PolymathAtlas.Gestalt.UCC

open PolymathAtlas.Core (Distinction)

/-! ## T1 — Distinction

"A system that draws no distinction has no information.  Distinction is the
atomic act of world-creation: from undifferentiated chaos, a boundary produces
an inside and an outside."

An *observer channel* on a state space `S` is a map `o : S → Ω` into the space of
observable readings.  It draws a distinction when two states are read
differently. -/

variable {S Ω : Type*}

/-- The reading channel of an observer: what the system can see of a state.
Part of POLYMATH ATLAS Status Report, Theorem 1 — Distinction. -/
abbrev Channel (S Ω : Type*) : Type _ := S → Ω

/-- The channel `o` **draws a distinction** when it separates at least two states.
Status Report, T1: the atomic act of world-creation. -/
def DrawsDistinction (o : Channel S Ω) : Prop := ∃ s t : S, o s ≠ o t

/-- The number of readings a channel can actually produce; the raw amount of
information available through it.  (`Set.ncard` is `0` on infinite ranges, which
is why the finiteness hypotheses appear explicitly in the statements below.) -/
noncomputable def channelCard (o : Channel S Ω) : ℕ := (Set.range o).ncard

/-- **POLYMATH ATLAS Status Report, Theorem 1 — Distinction.  Corresponds to
Genesis Engine L1 Reactor.**

A system that draws no distinction has no information: its channel collapses to
a single reading, so `channelCard o = 1` and there is nothing to be informed
about.  Without T1, T2–T5 are undefined — T2 measures the gain of a distinction,
T3–T4 the error of a predicted distinction, T5 the revisiting of distinguished
states. -/
theorem t1_no_distinction_no_information [Nonempty S] (o : Channel S Ω) :
    ¬ DrawsDistinction o ↔ channelCard o = 1 := by
  constructor
  · intro h
    obtain ⟨s₀⟩ := ‹Nonempty S›
    have hrange : Set.range o = {o s₀} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨s₀, rfl⟩, ?_⟩
      rintro x ⟨t, rfl⟩
      by_contra hne
      exact h ⟨t, s₀, hne⟩
    rw [channelCard, hrange, Set.ncard_singleton]
  · rintro h ⟨s, t, hst⟩
    rw [channelCard, Set.ncard_eq_one] at h
    obtain ⟨a, ha⟩ := h
    have hs : o s = a := by
      have hmem : o s ∈ Set.range o := ⟨s, rfl⟩
      rw [ha] at hmem
      exact hmem
    have ht : o t = a := by
      have hmem : o t ∈ Set.range o := ⟨t, rfl⟩
      rw [ha] at hmem
      exact hmem
    exact hst (hs.trans ht.symm)

/-- **POLYMATH ATLAS Status Report, Theorem 1 — Distinction.  Corresponds to
Genesis Engine L1 Reactor.**

The constructive half of T1: a boundary produces an inside *and* an outside.  A
channel that draws a distinction induces an honest two-block cut of the state
space (`PolymathAtlas.Core.Distinction`: both blocks non-empty, disjoint,
covering).  This is the atomic act of world-creation out of undifferentiated
chaos. -/
theorem t1_distinction_of_drawsDistinction (o : Channel S Ω) (h : DrawsDistinction o) :
    Nonempty (Distinction S) := by
  obtain ⟨s, t, hst⟩ := h
  refine ⟨{ inside := {x | o x = o s}
            outside := {x | o x ≠ o s}
            partition := ?_
            disjoint := ?_
            nonempty_inside := ⟨s, rfl⟩
            nonempty_outside := ⟨t, Ne.symm hst⟩ }⟩
  · ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact em _
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
      not_not]
    exact fun hx => hx

/-! ## T2 — informationGain

"Given a distinction (T1), information gain is the measure of how much the
distinction reduces uncertainty.  Information = difference that makes a
difference.  Zero gain implies the distinction was noise, not signal." -/

/-- Uncertainty of a set of candidate states: the log of the number of
candidates (Hartley measure).  Status Report, T2. -/
noncomputable def uncertainty (C : Set S) : ℝ := Real.log (C.ncard)

/-- **Information gain** of passing from the prior candidate set to the
posterior one: the reduction of uncertainty.  Status Report, T2 —
"information = difference that makes a difference". -/
noncomputable def informationGain (prior post : Set S) : ℝ :=
  uncertainty prior - uncertainty post

/-- Conditioning a candidate set on which side of a distinction the true state
lies: the posterior produced by *using* the distinction of T1.  Status Report,
T2 (T2 is defined "given a distinction (T1)"). -/
noncomputable def refineBy (C : Set S) (d : Distinction S) (s : S) : Set S :=
  haveI := Classical.dec (s ∈ d.inside)
  if s ∈ d.inside then C ∩ d.inside else C ∩ d.outside

/-- **POLYMATH ATLAS Status Report, Theorem 2 — informationGain.  Links to L2
Compressor.**

Information gain is non-negative: sharpening the candidate set can never
increase uncertainty.  This is the invariant the L2 Compressor relies on. -/
theorem t2_informationGain_nonneg {prior post : Set S} (hsub : post ⊆ prior)
    (hfin : prior.Finite) (hne : post.Nonempty) : 0 ≤ informationGain prior post := by
  have hpostfin : post.Finite := hfin.subset hsub
  have hle : post.ncard ≤ prior.ncard := Set.ncard_le_ncard hsub hfin
  have hpos : 0 < post.ncard := (Set.ncard_pos hpostfin).mpr hne
  have hlog : Real.log (post.ncard : ℝ) ≤ Real.log (prior.ncard : ℝ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  simpa [informationGain, uncertainty, sub_nonneg] using hlog

/-- **POLYMATH ATLAS Status Report, Theorem 2 — informationGain.  Links to L2
Compressor.**

Zero gain implies the distinction was noise, not signal: the posterior is the
prior unchanged, i.e. nothing was ruled out. -/
theorem t2_informationGain_eq_zero_iff {prior post : Set S} (hsub : post ⊆ prior)
    (hfin : prior.Finite) (hne : post.Nonempty) :
    informationGain prior post = 0 ↔ post = prior := by
  have hpostfin : post.Finite := hfin.subset hsub
  have hpos : 0 < post.ncard := (Set.ncard_pos hpostfin).mpr hne
  have hle : post.ncard ≤ prior.ncard := Set.ncard_le_ncard hsub hfin
  have hpriorpos : 0 < prior.ncard := lt_of_lt_of_le hpos hle
  constructor
  · intro h0
    have hlog : Real.log (post.ncard : ℝ) = Real.log (prior.ncard : ℝ) := by
      have := h0
      simp only [informationGain, uncertainty, sub_eq_zero] at this
      exact this.symm
    have hcast : ((post.ncard : ℝ)) = ((prior.ncard : ℝ)) := by
      have h1 : (0 : ℝ) < (post.ncard : ℝ) := by exact_mod_cast hpos
      have h2 : (0 : ℝ) < (prior.ncard : ℝ) := by exact_mod_cast hpriorpos
      calc ((post.ncard : ℝ)) = Real.exp (Real.log (post.ncard : ℝ)) := (Real.exp_log h1).symm
        _ = Real.exp (Real.log (prior.ncard : ℝ)) := by rw [hlog]
        _ = ((prior.ncard : ℝ)) := Real.exp_log h2
    have hnat : post.ncard = prior.ncard := by exact_mod_cast hcast
    exact Set.eq_of_subset_of_ncard_le hsub (le_of_eq hnat.symm) hfin
  · intro hEq
    rw [hEq]
    simp [informationGain]

/-- **POLYMATH ATLAS Status Report, Theorem 2 — informationGain.  Links to L2
Compressor.**

"Information = difference that makes a difference": refining by a distinction
yields a strictly positive gain exactly when the distinction actually cuts the
candidate set — otherwise the distinction was noise. -/
theorem t2_gain_pos_iff_distinction_cuts {C : Set S} (d : Distinction S) (s : S)
    (hfin : C.Finite) (hne : (refineBy C d s).Nonempty) :
    0 < informationGain C (refineBy C d s) ↔ refineBy C d s ≠ C := by
  have hsub : refineBy C d s ⊆ C := by
    unfold refineBy
    split <;> exact Set.inter_subset_left
  constructor
  · intro hpos hEq
    rw [hEq] at hpos
    simp [informationGain] at hpos
  · intro hne'
    have hssub : refineBy C d s ⊂ C := ⟨hsub, fun hc => hne' (Set.Subset.antisymm hsub hc)⟩
    have hlt : (refineBy C d s).ncard < C.ncard := Set.ncard_lt_ncard hssub hfin
    have hpos : 0 < (refineBy C d s).ncard :=
      (Set.ncard_pos (hfin.subset hsub)).mpr hne
    have hlog : Real.log ((refineBy C d s).ncard : ℝ) < Real.log (C.ncard : ℝ) :=
      Real.log_lt_log (by exact_mod_cast hpos) (by exact_mod_cast hlt)
    simpa [informationGain, uncertainty, sub_pos] using hlog

/-! ## T3/T4 — feedback error, and the inertia of perfect prediction

A **cognitive system** on a state space `S` consists of an environment map, a
predictor, a state-transition map and a learning rate.  The informal principle
"error is the engine of correction" is *not* postulated as an axiom: it is the
field `learningRate_eq_zero_iff`, which a concrete system must exhibit. -/

/-- A cognitive system in the sense of the UCC: it predicts its environment,
transitions between states, and learns at a rate driven by its prediction error.

Fields `learningRate_nonneg` and `learningRate_eq_zero_iff` carry the informal
principles of Status Report T3 ("error is the engine of correction": there is no
learning without error) as *hypotheses on a concrete system*, not as axioms. -/
structure CognitiveSystem (S : Type*) where
  /-- The true dynamics of the world. -/
  env : S → S
  /-- What the system expects the world to do. -/
  predict : S → S
  /-- How the system's own state changes in one UCC turn. -/
  step : S → S
  /-- How fast the system is changing its model at a given state. -/
  learningRate : S → ℝ
  /-- Learning rates are magnitudes. -/
  learningRate_nonneg : ∀ s, 0 ≤ learningRate s
  /-- Status Report T3: error is the *only* engine of correction. -/
  learningRate_eq_zero_iff : ∀ s, learningRate s = 0 ↔ predict s = env s

namespace CognitiveSystem

variable {S : Type*} (M : CognitiveSystem S)

/-- The feedback error at a state: the system's prediction disagrees with what
the environment actually does.  Status Report, T3. -/
def feedbackError (s : S) : Prop := M.predict s ≠ M.env s

/-- A system **predicts perfectly** when its feedback error vanishes at every
state.  Status Report, T3/T4. -/
def Perfect : Prop := ∀ s, M.predict s = M.env s

/-- The trajectory of the system from a starting state: iterated `step`.
Status Report, T5. -/
def trajectory (x : S) : ℕ → S := fun n => M.step^[n] x

end CognitiveSystem

/-- **POLYMATH ATLAS Status Report, Theorem 3 — feedbackError.**

A system that never encounters prediction error never learns.  Formally: if the
predicted state equals the actual state at all times, the learning rate is
identically zero. -/
theorem t3_feedbackError {S : Type*} (M : CognitiveSystem S) (h : M.Perfect) :
    ∀ s, M.learningRate s = 0 :=
  fun s => (M.learningRate_eq_zero_iff s).mpr (h s)

/-- **POLYMATH ATLAS Status Report, Theorem 3 — feedbackError.**

The converse direction of T3: wherever the system *does* err, it learns
strictly.  Error is the engine of correction. -/
theorem t3_learningRate_pos_of_error {S : Type*} (M : CognitiveSystem S) {s : S}
    (h : M.feedbackError s) : 0 < M.learningRate s := by
  rcases lt_or_eq_of_le (M.learningRate_nonneg s) with hlt | heq
  · exact hlt
  · exact absurd ((M.learningRate_eq_zero_iff s).mp heq.symm) h

/-- An **error-driven** cognitive system: one whose state only moves when it is
being corrected.  The field `step_eq_self_of_no_learning` is the architectural
commitment of Status Report T4 ("no error = no correction = no learning"),
stated as a structure field rather than as an axiom. -/
structure ErrorDriven (S : Type*) extends CognitiveSystem S where
  /-- Status Report T4: without learning there is no state change. -/
  step_eq_self_of_no_learning : ∀ s, learningRate s = 0 → step s = s

/-- **POLYMATH ATLAS Status Report, Theorem 4 — perfect predict → inert.
Corresponds to philosophical principle 'идеал = смерть'.**

A system that perfectly predicts its environment becomes inert.  No error (T3) =
no correction = no learning = death.  Formally: if the prediction error is
identically zero for all states, the state transition function becomes the
identity. -/
theorem t4_perfectPredictInert {S : Type*} (M : ErrorDriven S) (h : M.toCognitiveSystem.Perfect) :
    M.step = id := by
  funext s
  exact M.step_eq_self_of_no_learning s (t3_feedbackError M.toCognitiveSystem h s)

/-- **POLYMATH ATLAS Status Report, Theorem 4 — perfect predict → inert.
Corresponds to philosophical principle 'идеал = смерть'.**

The dynamical reading of T4: a perfect predictor's trajectory is constant — the
system is indistinguishable from a system that does nothing at all. -/
theorem t4_trajectory_const {S : Type*} (M : ErrorDriven S) (h : M.toCognitiveSystem.Perfect)
    (x : S) (n : ℕ) : M.toCognitiveSystem.trajectory x n = x := by
  have hstep : M.toCognitiveSystem.step = id := t4_perfectPredictInert M h
  simp [CognitiveSystem.trajectory, hstep]

/-! ## T5 — pigeonhole revisit -/

/-- The T5 bound of a finite state space: `|S|`, the maximal number of steps a
trajectory can take before some state necessarily recurs.  Status Report, T5
("enforced self-confrontation" in the informal text). -/
def t5Bound (S : Type*) [Fintype S] : ℕ := Fintype.card S

/-- **POLYMATH ATLAS Status Report, Theorem 5 — pigeonhole revisit within `|S|`
steps.  Corresponds to v100 = v79 = Ω = Urobouros closure.**

In a finite state space `|S|`, any trajectory of length `> |S|` must revisit a
previously visited state.  Stated for an arbitrary trajectory `f : ℕ → S`, since
the mechanism does not depend on the trajectory being generated by a `step`
map. -/
theorem t5_pigeonholeRevisit {S : Type*} [Fintype S] (f : ℕ → S) {n : ℕ}
    (hn : t5Bound S < n) : ∃ i j, i < j ∧ j ≤ n ∧ f i = f j := by
  have hcard : Fintype.card S < Fintype.card (Fin (n + 1)) := by
    simpa [t5Bound] using Nat.lt_succ_of_lt hn
  obtain ⟨a, b, hab, hfab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => f i.val) hcard
  have hne : (a : ℕ) ≠ (b : ℕ) := fun hh => hab (Fin.ext hh)
  rcases Nat.lt_or_ge (a : ℕ) (b : ℕ) with h | h
  · exact ⟨a, b, h, Nat.lt_succ_iff.mp b.isLt, hfab⟩
  · exact ⟨b, a, lt_of_le_of_ne h (Ne.symm hne), Nat.lt_succ_iff.mp a.isLt, hfab.symm⟩

/-- **POLYMATH ATLAS Status Report, Theorem 5 — pigeonhole revisit within `|S|`
steps.  Corresponds to v100 = v79 = Ω = Urobouros closure.**

The T5 mechanism applied to a cognitive system: within `|S|` turns of its own
UCC the trajectory necessarily returns to a state it has already occupied.  The
informal text reads this recurrence as "enforced self-confrontation"; formally it
is the pigeonhole principle on a finite state space. -/
theorem t5_system_revisits {S : Type*} [Fintype S] (M : CognitiveSystem S) (x : S) :
    ∃ i j, i < j ∧ j ≤ t5Bound S + 1 ∧
      M.trajectory x i = M.trajectory x j :=
  t5_pigeonholeRevisit (M.trajectory x) (Nat.lt_succ_self _)

end PolymathAtlas.Gestalt.UCC
