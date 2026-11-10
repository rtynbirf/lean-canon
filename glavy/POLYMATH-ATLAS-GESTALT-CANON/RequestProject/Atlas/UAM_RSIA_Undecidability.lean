import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_NerodeBridge
import RequestProject.Atlas.Arithmetic_Rice

set_option autoImplicit false

/-!
# RSIA epistemic closure: the Rice barrier

A `Bool`-valued Lean function is not an algorithm: classical choice can define
one from an arbitrary predicate.  Consequently the informal claim about “no
algorithm” is stated over the project's acceptable numbering of partial
computations.  `FunctionCodeModel` is the explicit bridge between that
numbering and word transformations.  This avoids silently assuming a universal
interpreter or an effective coding that the earlier RSIA development does not
provide.
-/

namespace UAM_RSIA

open Classical
open Arithmetic_Rice

universe u

variable {α : Type u}

/-- Program codes for transformations of words. -/
abbrev FunctionCode (_α : Type u) := Nat

/-- An interpretation of program numbers as total word transformations, tied
to an acceptable partial-computable enumeration.  `respects_program_extEq` is
the semantic adequacy condition needed by Rice's theorem. -/
structure FunctionCodeModel (α : Type u) where
  enumeration : PartialComputableEnumeration
  eval : FunctionCode α → UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α
  respects_program_extEq : ∀ {a b : FunctionCode α},
    ProgramExtEq enumeration.Eval a b → ∀ w, eval a w = eval b w

namespace FunctionCode

/-- Extensional equality of decoded word transformations. -/
def extEq (M : FunctionCodeModel α) (a b : FunctionCode α) : Prop :=
  ∀ w, M.eval a w = M.eval b w

/-- Nerode preservation is the semantic property used in the reduction. -/
def isNerodePreserving (M : FunctionCodeModel α)
    (L : Set (UAM_Free.FreeMonoid α)) (code : FunctionCode α) : Prop :=
  ∀ w, UAM_RegularLanguages.nerodeRel L w (M.eval code w)

/-- Nerode preservation depends only on the decoded function. -/
theorem isNerodePreserving_extensional (M : FunctionCodeModel α)
    (L : Set (UAM_Free.FreeMonoid α)) (a b : FunctionCode α)
    (h : extEq M a b) :
    isNerodePreserving M L a ↔ isNerodePreserving M L b := by
  refine ⟨fun h' w v => (h' w v).trans (congr_arg _ (congr_arg (· ++ v) (h w))), ?_⟩
  intro h' w v
  exact (h' w v).trans (congr_arg _ (congr_arg (· ++ v) (h w).symm))

/-- Adequacy for a particular language: the numbering contains programs on
both sides of the Nerode-preservation property.  This hypothesis is necessary;
nonemptiness and nonuniversality of `L` alone say nothing about which programs
an arbitrary enumeration contains. -/
def NerodeCodingAdequate (M : FunctionCodeModel α)
    (L : Set (UAM_Free.FreeMonoid α)) : Prop :=
  SemanticallyNontrivial (isNerodePreserving M L)

/-- The decoded Nerode property is extensional in the sense required by Rice. -/
theorem isNerodePreserving_rice_extensional (M : FunctionCodeModel α)
    (L : Set (UAM_Free.FreeMonoid α)) :
    ExtensionalProperty M.enumeration (isNerodePreserving M L) := by
  intro a b h
  exact isNerodePreserving_extensional M L a b (M.respects_program_extEq h)

/-- **Rice barrier for Nerode preservation.**  For every adequate acceptable
numbering, no total Boolean algorithm on program codes decides whether the
decoded transformation preserves all Nerode classes. -/
theorem nerode_preservation_undecidable (M : FunctionCodeModel α)
    (L : Set (UAM_Free.FreeMonoid α)) (hAdequate : NerodeCodingAdequate M L) :
    ¬ ∃ decider : FunctionCode α → Bool,
      ∀ code, decider code = true ↔ isNerodePreserving M L code := by
  exact rice_theorem M.enumeration (isNerodePreserving M L)
    (isNerodePreserving_rice_extensional M L) hAdequate

/-- The code-level property agrees exactly with the Run-13 semantic notion for
the decoded transformation. -/
theorem ruleUnmisunderstandable_iff_functionCode
    (M : FunctionCodeModel α) (L : Set (UAM_Free.FreeMonoid α))
    (code : FunctionCode α) :
    RuleUnmisunderstandable L (M.eval code) ↔
      isNerodePreserving M L code := by
  rfl

end FunctionCode
end UAM_RSIA
