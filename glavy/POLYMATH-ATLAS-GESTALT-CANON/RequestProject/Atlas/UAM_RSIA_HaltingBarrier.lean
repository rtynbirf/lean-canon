import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_FormalMindTheorem
import RequestProject.Atlas.UAM_RSIA_Undecidability
import RequestProject.Atlas.UAM_RSIA_SelfReference
import RequestProject.Atlas.Arithmetic_Rice

set_option autoImplicit false

/-!
# RSIA epistemic closure: halting reductions

Turing completeness cannot be obtained from the current operational structures
alone: an interpreter and a correctness proof are required.  This file states
that requirement as `RSIAHaltingSimulation` and proves the reduction theorem.
Thus no universal machine is postulated and no false unconditional claim is
made.
-/

namespace UAM_RSIA

open Arithmetic_Rice

universe u

variable {α : Type u}

/-- Collective operational termination. -/
def CollectiveShouldStop (hps : HierarchicalParallelSystem α) : Prop :=
  ∀ st ∈ hps.system.sessions, st.ShouldStop

/-- A source halting instance in an acceptable program enumeration. -/
structure HaltingInstance (E : PartialComputableEnumeration) where
  program : Nat
  input : Nat

/-- Halting means that the deterministic evaluation graph has an output. -/
def HaltingInstance.Halts {E : PartialComputableEnumeration}
    (x : HaltingInstance E) : Prop :=
  ∃ output, E.Eval x.program x.input output

/-- A verified reduction from the halting problem to collective RSIA stopping.
This is the exact extra datum needed to call an RSIA engine universal. -/
structure RSIAHaltingSimulation (α : Type u)
    (E : PartialComputableEnumeration) where
  encode : HaltingInstance E → HierarchicalParallelSystem α
  correct : ∀ x, CollectiveShouldStop (encode x) ↔ x.Halts

/-- The ordinary two-argument halting theorem, re-exposed for the source
numbering used by a simulation. -/
theorem halting_problem_undecidable (E : PartialComputableEnumeration) :
    ¬ ∃ decider : Nat → Nat → Bool,
      ∀ program input, decider program input = true ↔
        ∃ output, E.Eval program input output := by
  exact E.halting_undecidable

/-- **Halting barrier.**  If an RSIA model implements a verified universal
simulation, then collective `ShouldStop` has no Boolean decider. -/
theorem rsia_shouldStop_undecidable (E : PartialComputableEnumeration)
    (simulation : RSIAHaltingSimulation α E) :
    ¬ ∃ decider : HierarchicalParallelSystem α → Bool,
      ∀ hps, decider hps = true ↔ CollectiveShouldStop hps := by
  intro ⟨decider, hdecider⟩
  apply halting_problem_undecidable E
  use fun program input => decider (simulation.encode ⟨program, input⟩)
  intro program input
  simp [hdecider, simulation.correct]; rfl

/-- Positive half of Turing equivalence: the supplied verified simulation
produces an RSIA system for every source program/input pair. -/
theorem rsia_simulates_turing (E : PartialComputableEnumeration)
    (simulation : RSIAHaltingSimulation α E) (x : HaltingInstance E) :
    ∃ hps : HierarchicalParallelSystem α,
      CollectiveShouldStop hps ↔ x.Halts := by
  exact ⟨simulation.encode x, simulation.correct x⟩

end UAM_RSIA
