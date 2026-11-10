import Mathlib
import RequestProject.Atlas.ReclaimedTheorems

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Arithmetic foundations

A small first-order arithmetic syntax is provided explicitly.  The metatheorems
use `ArithmetizedSyntax`, whose fields isolate a Gödel numbering, numeral
substitution, and the verified diagonal substitution equation.
-/

namespace Arithmetic_Foundations

inductive Term where
  | zero
  | var (index : ℕ)
  | succ (term : Term)
  | add (left right : Term)
  | mul (left right : Term)
  deriving DecidableEq, Encodable

inductive Formula where
  | falsum
  | equal (left right : Term)
  | implies (left right : Formula)
  | neg (body : Formula)
  | forallE (body : Formula)
  deriving DecidableEq, Encodable

/-- A concrete Gödel numbering supplied by Lean's injective encoding of syntax. -/
def godelNumber (formula : Formula) : ℕ := Encodable.encode formula

/-- Coding is injective, as required of a Gödel numbering. -/
theorem godelNumber_injective : Function.Injective godelNumber := by
  exact Encodable.encode_injective

abbrev ArithmetizedSyntax := IdealAI.Reclaimed.ArithmetizedSyntax
abbrev DiagonalTheory := IdealAI.Reclaimed.DiagonalTheory

/-- The syntactic diagonal equation. -/
theorem diagonal_lemma (arithSyntax : ArithmetizedSyntax)
    (template : arithSyntax.Sentence) :
    arithSyntax.diagonal template =
      arithSyntax.substituteNumeral template (arithSyntax.code template) := by
  exact IdealAI.Reclaimed.ArithmetizedSyntax.diagonal_lemma arithSyntax template

end Arithmetic_Foundations
