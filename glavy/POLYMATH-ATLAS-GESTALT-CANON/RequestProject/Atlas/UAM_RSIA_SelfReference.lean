import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_System
import RequestProject.Atlas.UAM_RSIA_CognitiveSynthesis
import RequestProject.Atlas.UAM_RSIA_FormalMindTheorem
import RequestProject.Atlas.Arithmetic_Godel2

set_option autoImplicit false

/-!
# RSIA epistemic closure: self-reference

Gödel's second theorem applies only after a formal theory, a provability
predicate, the Hilbert--Bernays conditions, and a Gödel fixed point have been
provided.  Operational RSIA states do not themselves contain such syntax.
`RSIASelfReferenceModel` records this additional interpretation explicitly,
rather than manufacturing derivability conditions from operational data.
-/

namespace UAM_RSIA

open Arithmetic_Godel2

universe u

variable {α : Type u}

/-- An arithmetized internal theory assigned to an operational RSIA system. -/
structure RSIASelfReferenceModel (α : Type u) where
  system : HierarchicalParallelSystem α
  formalMind : RSIAIsFormalMind system
  derivability : DerivabilityConditions
  godelSentence : Prop
  fixedPoint : DerivabilityConditions.IsGodelSentence derivability godelSentence
  consistent : DerivabilityConditions.Consistent derivability

/-- **Self-reference barrier.**  Any RSIA interpretation satisfying the actual
hypotheses of Gödel's second incompleteness theorem cannot prove its internal
consistency statement. -/
theorem rsia_cannot_prove_own_consistency (M : RSIASelfReferenceModel α) :
    ¬ M.derivability.Provable
      (DerivabilityConditions.ConsistencyStatement M.derivability) := by
  exact DerivabilityConditions.second_incompleteness M.derivability M.godelSentence M.fixedPoint M.consistent

/-- The operational empty execution is externally certified while the
arithmetized internal theory cannot certify its own consistency.  The theorem
keeps the external and internal levels syntactically distinct. -/
theorem rsia_main_theorem_external_only (M : RSIASelfReferenceModel α) :
    M.system.runTrace [] = M.system ∧
    ¬ M.derivability.Provable
      (DerivabilityConditions.ConsistencyStatement M.derivability) := by
  exact ⟨rfl, rsia_cannot_prove_own_consistency M⟩

/-- The formal-mind witness carried by a self-reference model remains available
externally; incompleteness does not negate the operational theorem. -/
theorem rsia_selfReference_external_formalMind (M : RSIASelfReferenceModel α) :
    RSIAIsFormalMind M.system :=
  M.formalMind

end UAM_RSIA
