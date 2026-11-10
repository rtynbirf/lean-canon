import Mathlib
import RequestProject.Atlas.Arithmetic_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Hilbert--Bernays derivability and Gödel's second theorem -/

namespace Arithmetic_Godel2

abbrev DerivabilityConditions := IdealAI.Reclaimed.DerivabilityConditions

namespace DerivabilityConditions

abbrev Consistent := IdealAI.Reclaimed.DerivabilityConditions.Consistent
abbrev ConsistencyStatement :=
  IdealAI.Reclaimed.DerivabilityConditions.ConsistencyStatement
abbrev IsGodelSentence := IdealAI.Reclaimed.DerivabilityConditions.IsGodelSentence

/-- Under D1--D3, consistency prevents a theory from proving its internal
consistency statement. -/
theorem second_incompleteness (conditions : DerivabilityConditions) (sentence : Prop)
    (fixedPoint : IsGodelSentence conditions sentence)
    (consistent : Consistent conditions) :
    ¬ conditions.Provable (ConsistencyStatement conditions) := by
  exact IdealAI.Reclaimed.DerivabilityConditions.second_incompleteness
    conditions sentence fixedPoint consistent

end DerivabilityConditions
end Arithmetic_Godel2
