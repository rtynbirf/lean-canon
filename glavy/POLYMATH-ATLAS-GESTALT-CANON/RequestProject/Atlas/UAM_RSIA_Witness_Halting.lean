import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_HaltingBarrier

set_option autoImplicit false

/-!
# Run 33 Track A: a conditional halting witness

The table model records finite test data.  Its bridge to an acceptable
numbering is explicit, so the undecidability conclusion is conditional on that
bridge rather than being attributed to the finite table itself.
-/

namespace UAM_RSIA

open Arithmetic_Rice

universe u
variable {α : Type u}

/-- A table-level halting interpretation of RSIA systems. -/
structure ToyHaltingModel (α : Type u) where
  encode : Nat → Nat → HierarchicalParallelSystem α
  halts_table : Nat → Nat → Bool
  correct : ∀ code input,
    CollectiveShouldStop (encode code input) ↔ halts_table code input = true

/-- Explicit positive and negative entries in the finite test table. -/
def ToyHaltingModel.HaltingAdequate (toy : ToyHaltingModel α) : Prop :=
  (∃ code input, toy.halts_table code input = true) ∧
  (∃ code input, toy.halts_table code input = false)

/-- Agreement with a verified simulation in an acceptable numbering. -/
structure ToyHaltingEmbedding (α : Type u) (toy : ToyHaltingModel α) where
  E : PartialComputableEnumeration
  sim : RSIAHaltingSimulation α E
  encode_agrees : ∀ code input,
    sim.encode ⟨code, input⟩ = toy.encode code input

/-- An interpretation-preserving table inherits the ordinary halting barrier. -/
theorem toy_halting_barrier_under_embedding
    (toy : ToyHaltingModel α)
    (emb : ToyHaltingEmbedding α toy)
    (_hToyAdequate : toy.HaltingAdequate) :
    ¬ ∃ decider : Nat → Nat → Bool,
      ∀ code input, decider code input = true ↔
        toy.halts_table code input = true := by
  intro hDec
  obtain ⟨decider, hdecider⟩ := hDec
  apply halting_problem_undecidable emb.E
  refine ⟨decider, ?_⟩
  intro program input
  constructor
  · intro htrue
    have htable := (hdecider program input).mp htrue
    have hstop := (toy.correct program input).mpr htable
    rw [← emb.encode_agrees program input] at hstop
    exact (emb.sim.correct ⟨program, input⟩).mp hstop
  · intro hhalts
    have hstop := (emb.sim.correct ⟨program, input⟩).mpr hhalts
    rw [emb.encode_agrees program input] at hstop
    exact (hdecider program input).mpr ((toy.correct program input).mp hstop)

/-- A parity table built from supplied stopping and non-stopping systems.
The parameters expose the positive and negative operational witnesses used by the table. -/
def toyHaltingFin4
    (stops doesNotStop : HierarchicalParallelSystem (Fin 4))
    (hStops : CollectiveShouldStop stops)
    (hDoesNotStop : ¬ CollectiveShouldStop doesNotStop) :
    ToyHaltingModel (Fin 4) where
  encode := fun code _ => if code % 2 = 0 then stops else doesNotStop
  halts_table := fun code _ => if code % 2 = 0 then true else false
  correct := by
    intro code input
    by_cases hEven : code % 2 = 0
    · rw [if_pos hEven, if_pos hEven]
      constructor
      · intro _
        rfl
      · intro _
        exact hStops
    · rw [if_neg hEven, if_neg hEven]
      constructor
      · intro hStop
        exact (hDoesNotStop hStop).elim
      · intro hFalse
        cases hFalse

/-- The parity table has both truth values. -/
theorem Fin4_toy_halting_adequate
    (stops doesNotStop : HierarchicalParallelSystem (Fin 4))
    (hStops : CollectiveShouldStop stops)
    (hDoesNotStop : ¬ CollectiveShouldStop doesNotStop) :
    (toyHaltingFin4 stops doesNotStop hStops hDoesNotStop).HaltingAdequate := by
  constructor
  · refine ⟨0, 0, ?_⟩
    rfl
  · refine ⟨1, 0, ?_⟩
    rfl


end UAM_RSIA
