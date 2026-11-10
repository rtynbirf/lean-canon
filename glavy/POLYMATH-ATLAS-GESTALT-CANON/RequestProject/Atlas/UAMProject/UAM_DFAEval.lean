import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Free
import RequestProject.Atlas.UAMProject.UAM_Congruence
import RequestProject.Atlas.UAMProject.UAM_Morphism

namespace UAMP_DFAEval
universe u

open UAMP_Free hiding FreeMonoid

/-- Deterministic finite automaton (namespace-member, methods style) -/
structure DFA (α Q : Type u) [DecidableEq Q] where
  δ : Q → α → Q
  q₀ : Q
  F : Set Q

variable {α Q : Type u} [DecidableEq Q] (A : DFA α Q)

/-- Run DFA from state q on word w -/
def evalFrom (A : DFA α Q) (q : Q) : UAMP_Free.FreeMonoid α → Q
  | [] => q
  | a :: w => evalFrom A (A.δ q a) w

/-- Run DFA from initial state -/
def eval (w : UAMP_Free.FreeMonoid α) : Q := evalFrom A A.q₀ w

/-- Does DFA accept word w? -/
def accepts (w : UAMP_Free.FreeMonoid α) : Prop := eval A w ∈ A.F

/-- Language recognized by DFA -/
def language : Set (UAMP_Free.FreeMonoid α) := {w | accepts A w}

/-- evalFrom distributes over concatenation -/
theorem evalFrom_concat (q : Q) (w₁ w₂ : UAMP_Free.FreeMonoid α) :
    evalFrom A q (w₁ ++ w₂) = evalFrom A (evalFrom A q w₁) w₂ := by
  induction w₁ generalizing q with
  | nil => rfl
  | cons a _ ih => exact ih (A.δ q a)

/-- eval distributes over concatenation -/
theorem eval_concat (w₁ w₂ : UAMP_Free.FreeMonoid α) :
    eval A (w₁ ++ w₂) = evalFrom A (eval A w₁) w₂ := evalFrom_concat A A.q₀ w₁ w₂

/-- Equal evalFrom for equal states (consistency) -/
theorem eval_eq_of_eval_eq {q₁ q₂ : Q} (w : UAMP_Free.FreeMonoid α)
    (h : ∀ v, evalFrom A q₁ v = evalFrom A q₂ v) : evalFrom A q₁ w = evalFrom A q₂ w :=
  h w

/-- Equal evalFrom under state equality -/
theorem evalFrom_eq_of_eval_eq {q₁ q₂ : Q} (h : q₁ = q₂) (w : UAMP_Free.FreeMonoid α) :
    evalFrom A q₁ w = evalFrom A q₂ w := by rw [h]

end UAMP_DFAEval
