import Mathlib
import RequestProject.Atlas.Arithmetic_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Tarski's undefinability theorem -/

namespace Arithmetic_Truth

open Arithmetic_Foundations

abbrev DefinesTruth := IdealAI.Reclaimed.DefinesTruth

/-- No representable predicate agrees with arithmetic satisfaction on every
sentence.  The contradiction is obtained from the diagonal fixed point of its
negation. -/
theorem tarski_undefinability (theory : DiagonalTheory) :
    ¬ ∃ truth : theory.Sentence → Prop,
      theory.Representable truth ∧ DefinesTruth theory truth := by
  exact IdealAI.Reclaimed.truth_undefinability theory

end Arithmetic_Truth
