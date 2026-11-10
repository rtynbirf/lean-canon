import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_Undecidability
import RequestProject.Atlas.UAM_RSIA_SelfReference
import RequestProject.Atlas.UAM_RSIA_HaltingBarrier
import RequestProject.Atlas.UAM_RSIA_PhenomenalUnprovability

set_option autoImplicit false

/-! # RSIA epistemic barrier package -/

namespace UAM_RSIA

universe u

variable {α : Type u}

/-- The four rigorously scoped epistemic limits.  Universality,
self-reference, and semantic program interpretation occur as explicit inputs;
they are not consequences of the bare operational RSIA structures. -/
structure EpistemicBarrier (α : Type u) where
  undecidability_nerode :
    ∀ (M : FunctionCodeModel α) (L : Set (UAM_Free.FreeMonoid α)),
      FunctionCode.NerodeCodingAdequate M L →
      ¬ ∃ decider : FunctionCode α → Bool,
        ∀ code, decider code = true ↔
          FunctionCode.isNerodePreserving M L code
  unprovability_self_consistency :
    ∀ M : RSIASelfReferenceModel α,
      ¬ M.derivability.Provable
        (Arithmetic_Godel2.DerivabilityConditions.ConsistencyStatement
          M.derivability)
  undecidability_termination :
    ∀ E : Arithmetic_Rice.PartialComputableEnumeration,
      RSIAHaltingSimulation α E →
        ¬ ∃ decider : HierarchicalParallelSystem α → Bool,
          ∀ hps, decider hps = true ↔ CollectiveShouldStop hps
  undecidability_phenomenal :
    ∀ (P : PhenomenalConsciousnessPredicate α)
      (M : PhenomenalProgramModel α), M.Adequate P →
      ¬ ∃ decider : HierarchicalParallelSystem α →
          List (UAM_Free.FreeMonoid α) → Bool,
        ∀ hps obs, decider hps obs = true ↔ P hps obs

/-- Canonical package assembled from the four preceding tracks. -/
def epistemicBarrier : EpistemicBarrier α where
  undecidability_nerode := by
    intro M L h
    exact FunctionCode.nerode_preservation_undecidable M L h
  unprovability_self_consistency := by
    intro M
    exact rsia_cannot_prove_own_consistency M
  undecidability_termination := by
    intro E simulation
    exact rsia_shouldStop_undecidable E simulation
  undecidability_phenomenal := by
    intro P M h
    exact phenomenal_consciousness_undecidable P M h

/-- Every field of the package is definitionally backed by its corresponding
track theorem. -/
theorem epistemicBarrier_components :
    (epistemicBarrier (α := α)).undecidability_nerode =
      (fun M L h => FunctionCode.nerode_preservation_undecidable M L h) ∧
    (epistemicBarrier (α := α)).unprovability_self_consistency =
      (fun M => rsia_cannot_prove_own_consistency M) := by
  constructor <;> rfl

end UAM_RSIA
