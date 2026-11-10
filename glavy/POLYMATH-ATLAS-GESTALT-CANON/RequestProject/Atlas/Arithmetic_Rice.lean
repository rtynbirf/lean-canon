import Mathlib
import RequestProject.Atlas.Arithmetic_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Rice's theorem for partial computable enumerations -/

namespace Arithmetic_Rice

abbrev ProgramExtEq := IdealAI.Reclaimed.ProgramExtEq
abbrev PartialComputableEnumeration :=
  IdealAI.Reclaimed.PartialComputableEnumeration
abbrev ExtensionalProperty := IdealAI.Reclaimed.ExtensionalProperty
abbrev SemanticallyNontrivial := IdealAI.Reclaimed.SemanticallyNontrivial

/-- Every nontrivial extensional property of programs is undecidable.  The
acceptable enumeration packages the uniform switch furnished by universality
and the s-m-n construction. -/
theorem rice_theorem (enumeration : PartialComputableEnumeration)
    (property : ℕ → Prop)
    (extensional : ExtensionalProperty enumeration property)
    (nontrivial : SemanticallyNontrivial property) :
    ¬ ∃ decider : ℕ → Bool,
      ∀ program, decider program = true ↔ property program := by
  exact IdealAI.Reclaimed.rice_theorem enumeration property extensional nontrivial

end Arithmetic_Rice
