import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_Undecidability
import RequestProject.Atlas.UAM_RSIA_Witness_Fin4

set_option autoImplicit false

/-!
# Run 31: necessity of semantic nontriviality

These results isolate the converse obstruction.  If every code has the Nerode
preservation property, the constant-true Boolean function decides it and the
semantic nontriviality hypothesis required by Rice's theorem is false.
-/

namespace UAM_RSIA

universe u
variable {α : Type u}

/-- If every code preserves Nerode classes, the property has a Boolean
decider. -/
theorem barrier_fails_if_all_preserve (M : FunctionCodeModel α)
    (L : Set (UAM_Free.FreeMonoid α))
    (hAllPreserve : ∀ code, FunctionCode.isNerodePreserving M L code) :
    ∃ decider : Nat → Bool,
      ∀ code, decider code = true ↔
        FunctionCode.isNerodePreserving M L code := by
  refine ⟨fun _ => true, ?_⟩
  intro code
  constructor
  · intro _
    exact hAllPreserve code
  · intro _
    rfl

/-- A universally true semantic property is not semantically nontrivial. -/
theorem adequate_fails_if_all_preserve (M : FunctionCodeModel α)
    (L : Set (UAM_Free.FreeMonoid α))
    (hAllPreserve : ∀ code, FunctionCode.isNerodePreserving M L code) :
    ¬ FunctionCode.NerodeCodingAdequate M L := by
  intro h
  obtain ⟨yes, no, hyes, hno⟩ := h
  exact hno (hAllPreserve no)

/-- Necessity theorem: in any model where all programs preserve Nerode
classes, the claimed undecidability barrier fails and its adequacy hypothesis
is false. -/
theorem trivial_model_contradicts_barrier (M : FunctionCodeModel α)
    (L : Set (UAM_Free.FreeMonoid α))
    (hAllPreserve : ∀ code, FunctionCode.isNerodePreserving M L code) :
    (∃ decider : Nat → Bool,
      ∀ code, decider code = true ↔
        FunctionCode.isNerodePreserving M L code) ∧
    ¬ FunctionCode.NerodeCodingAdequate M L := by
  exact ⟨barrier_fails_if_all_preserve M L hAllPreserve,
    adequate_fails_if_all_preserve M L hAllPreserve⟩

end UAM_RSIA
