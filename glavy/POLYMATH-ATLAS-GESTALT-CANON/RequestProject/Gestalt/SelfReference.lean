/-
# POLYMATH_ATLAS_GESTALT — Part 3.  Urobouros closure.

Source: the **gestalt synthesis of POLYMATH ATLAS v6 (head / philosophy) and the
Status Report (tail / engineering)** — the two documents are the same Universal
Cognition Cycle viewed from opposite ends.

Three statements:

* `methodology_revisits_level`  — v100 = v79 = Ω = the T5 bound: the methodology's own
  version dynamics is subject to the pigeonhole principle it states;
* `ideal_is_death`     — 'идеал = смерть', T4 read philosophically;
* `gap_preserves_life` — 'щель', the complement of `ideal_is_death`.

All statements in this file are fully proved: no `sorry` remains.
-/
import RequestProject.Gestalt.UCC

namespace PolymathAtlas.Gestalt.SelfReference

open PolymathAtlas.Gestalt.UCC

/-! ## 1.  The methodology as a dynamical system on version space -/

/-- A **methodology** with versioned levels: a finite set of admissible v-levels
together with the map taking one version to its successor.  The Status Report's
rule *"do not add new v-levels"* is the field `mapsTo`: the successor of an
admissible level is again admissible, so the version space never grows.

Gestalt synthesis of POLYMATH ATLAS v6 + Status Report. -/
structure Methodology where
  /-- The admissible v-levels.  Finite by the "no new v-levels" rule. -/
  levels : Finset ℕ
  /-- Where the methodology goes after a given version. -/
  step : ℕ → ℕ
  /-- "Do not add new v-levels": the version space is closed under `step`. -/
  mapsTo : ∀ v ∈ levels, step v ∈ levels
  /-- The synthesis starts from v79, the last level of the Status Report. -/
  start_mem : 79 ∈ levels

namespace Methodology

variable (M : Methodology)

/-- The v-level the methodology occupies at index `n ≥ 79`, obtained by iterating
`step` from v79.  So `vlevel M 79 = 79` and `vlevel M 100` is v100. -/
def vlevel (n : ℕ) : ℕ := M.step^[n - 79] 79

/-- Every level reached from v79 is admissible: the "no new v-levels" rule is
preserved along the trajectory.  Status Report. -/
theorem iterate_mem (k : ℕ) : M.step^[k] 79 ∈ M.levels := by
  induction k with
  | zero => simpa using M.start_mem
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact M.mapsTo _ ih

/-- Every v-level the methodology occupies is admissible.  Status Report, the
"do not add new v-levels" rule. -/
theorem vlevel_mem (n : ℕ) : M.vlevel n ∈ M.levels := M.iterate_mem (n - 79)

/-- **Ω** — a version level that the methodology's own evolution returns to.
The system's methodology returns to its own foundation. -/
def IsOmega (w : ℕ) : Prop := ∃ i j, 79 ≤ i ∧ i < j ∧ M.vlevel i = w ∧ M.vlevel j = w

end Methodology

/-- **Gestalt synthesis of POLYMATH ATLAS v6 + Status Report.  v6
(head/philosophy) and the Status Report (tail/engineering) are the same UCC
viewed from opposite ends.  The prohibition against new v-levels is T5 applied
to methodology itself.**

`v100 = v79 = Ω = t5Bound`.  If the admissible version space has at most 21
levels — the distance from v79 to v100 — then the trajectory of the methodology
must revisit a level between v79 and v100.  The revisited level is Ω: the point
at which the methodology returns to its own foundation.  This is not
circularity, it is self-awareness: the rule "do not add new v-levels" is itself
an instance of T5, the pigeonhole principle applied to version space, and the
bound is exactly the T5 bound `|levels|`. -/
theorem methodology_revisits_level (M : Methodology) (hcard : M.levels.card ≤ 21) :
    ∃ w, M.IsOmega w ∧ ∃ i j, 79 ≤ i ∧ i < j ∧ j ≤ 100 ∧ M.vlevel i = w ∧ M.vlevel j = w := by
  have hcards : M.levels.card < (Finset.Icc 79 100).card := by
    rw [Nat.card_Icc]
    omega
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcards
      (f := M.vlevel) (fun x _ => M.vlevel_mem x)
  rw [Finset.mem_Icc] at ha hb
  rcases Nat.lt_or_ge a b with h | h
  · exact ⟨M.vlevel a, ⟨a, b, ha.1, h, rfl, hfab.symm⟩, a, b, ha.1, h, hb.2, rfl, hfab.symm⟩
  · have hba : b < a := lt_of_le_of_ne h (fun hh => hab hh.symm)
    exact ⟨M.vlevel b, ⟨b, a, hb.1, hba, rfl, hfab⟩, b, a, hb.1, hba, ha.2, rfl, hfab⟩

/-- **Gestalt synthesis of POLYMATH ATLAS v6 + Status Report.**

The bound of the Urobouros closure is literally the T5 bound of the version
space: the methodology re-confronts a level of its own history within
`|levels|` version steps. -/
theorem methodology_revisits_level_within_card (M : Methodology) :
    ∃ i j, 79 ≤ i ∧ i < j ∧ j ≤ 79 + M.levels.card ∧ M.vlevel i = M.vlevel j := by
  have hcards : M.levels.card < (Finset.Icc 79 (79 + M.levels.card)).card := by
    rw [Nat.card_Icc]
    omega
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcards
      (f := M.vlevel) (fun x _ => M.vlevel_mem x)
  rw [Finset.mem_Icc] at ha hb
  rcases Nat.lt_or_ge a b with h | h
  · exact ⟨a, b, ha.1, h, hb.2, hfab⟩
  · exact ⟨b, a, hb.1, lt_of_le_of_ne h (fun hh => hab hh.symm), ha.2, hfab.symm⟩

/-! ## 2.  идеал = смерть -/

/-- A cognitive system is **cognitively dead** when it no longer learns and no
longer moves.  Philosophical principle 'идеал = смерть'. -/
def CognitivelyDead {S : Type*} (M : ErrorDriven S) : Prop :=
  (∀ s, M.learningRate s = 0) ∧ M.step = id

/-- **Philosophical principle 'идеал = смерть' formalized.  Links T4 to the
philosophical framework.  A system that never errs never learns.  See also: T4
`t4_perfectPredictInert`.**

For any cognitive system `S`, if `S` achieves perfect prediction (T4), then its
learning rate is zero, its state transitions become the identity, and `S` is
cognitively dead.  Completeness kills. -/
theorem ideal_is_death {S : Type*} (M : ErrorDriven S) (h : M.toCognitiveSystem.Perfect) :
    (∀ s, M.learningRate s = 0) ∧ M.step = id ∧ CognitivelyDead M := by
  have hlr : ∀ s, M.learningRate s = 0 := t3_feedbackError M.toCognitiveSystem h
  have hstep : M.step = id := t4_perfectPredictInert M h
  exact ⟨hlr, hstep, hlr, hstep⟩

/-- **Philosophical principle 'идеал = смерть' formalized.**

The ideal state is indistinguishable from non-existence: a perfect predictor's
trajectory never leaves its starting point, so no observation of its evolution
can tell it apart from a system that does nothing at all. -/
theorem ideal_indistinguishable_from_nonexistence {S : Type*} (M : ErrorDriven S)
    (h : M.toCognitiveSystem.Perfect) (x : S) (n : ℕ) :
    M.toCognitiveSystem.trajectory x n = x :=
  t4_trajectory_const M h x n

/-! ## 3.  щель -/

/-- A system **has a gap** when at least one distinction remains unresolved: some
state at which its prediction still disagrees with the world.  Philosophical
principle 'щель'. -/
def HasGap {S : Type*} (M : CognitiveSystem S) : Prop := ∃ s, M.predict s ≠ M.env s

/-- **Philosophical principle 'щель' formalized.  Unresolved distinction =
continued learning.  See also: T3 `t3_feedbackError` as the precondition for T2
`informationGain`.**

For any cognitive system `S`, if `S` maintains at least one unresolved
distinction (a gap), then `S`'s learning rate is strictly positive there. -/
theorem gap_preserves_life {S : Type*} (M : CognitiveSystem S) (h : HasGap M) :
    ∃ s, 0 < M.learningRate s := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, t3_learningRate_pos_of_error M hs⟩

/-- **Philosophical principle 'щель' formalized.**

The converse: closing all gaps is exactly T4, which is death.  Gap and life are
the same predicate seen from the two sides. -/
theorem gap_closed_iff_dead {S : Type*} (M : ErrorDriven S) :
    ¬ HasGap M.toCognitiveSystem ↔ CognitivelyDead M := by
  constructor
  · intro h
    have hperfect : M.toCognitiveSystem.Perfect := by
      intro s
      by_contra hs
      exact h ⟨s, hs⟩
    exact ⟨t3_feedbackError M.toCognitiveSystem hperfect,
      t4_perfectPredictInert M hperfect⟩
  · rintro ⟨hlr, -⟩ ⟨s, hs⟩
    exact hs ((M.learningRate_eq_zero_iff s).mp (hlr s))

/-- **Gestalt synthesis: 'щель' and 'идеал = смерть' are one statement.**

A system is alive (learns somewhere) if and only if it keeps a gap; the head
(philosophy: the ideal is death) and the tail (engineering: T3/T4) close on each
other, exactly as the Urobouros does. -/
theorem life_iff_gap {S : Type*} (M : ErrorDriven S) :
    (∃ s, 0 < M.learningRate s) ↔ HasGap M.toCognitiveSystem := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    intro hEq
    exact absurd ((M.learningRate_eq_zero_iff s).mpr hEq) (ne_of_gt hs)
  · exact gap_preserves_life M.toCognitiveSystem

end PolymathAtlas.Gestalt.SelfReference
