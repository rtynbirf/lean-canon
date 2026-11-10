import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Green
import RequestProject.Atlas.UAMProject.UAM_Regular

namespace UAMP_RectangularBand
universe u

/-- Rectangular band: L × R with (l₁,r₁) * (l₂,r₂) = (l₁, r₂).

Архивная версия объявляла на прямоугольной связке структуру моноида
(с `sorry` в полях `one`, `one_mul`, `mul_one`). Это невозможно: при
`|L| > 1` или `|R| > 1` у прямоугольной связки нет единицы, так как
`x * y` не зависит ни от второй компоненты `x`, ни от первой компоненты `y`.
Поэтому здесь строится только полугруппа (`Mul` + ассоциативность), и
доказываются её содержательные свойства. -/
structure RectangularBand (L R : Type u) where
  left : L
  right : R

instance (L R : Type u) : Mul (RectangularBand L R) where
  mul := fun x y => ⟨x.left, y.right⟩

@[simp] theorem mul_def {L R : Type u} (x y : RectangularBand L R) :
    x * y = ⟨x.left, y.right⟩ := rfl

/-- Умножение ассоциативно: прямоугольная связка — полугруппа. -/
theorem mul_assoc' {L R : Type u} (x y z : RectangularBand L R) :
    x * y * z = x * (y * z) := rfl

/-- All elements are idempotent -/
theorem all_idempotent {L R : Type u} (x : RectangularBand L R) : x * x = x := by
  cases x; rfl

/-- Умножение поглощает середину: `x * y * x = x`. -/
theorem mul_mul_self {L R : Type u} (x y : RectangularBand L R) : x * y * x = x := by
  cases x; rfl

/-- Идемпотенты прямоугольной связки не коммутируют, если `L` (или `R`)
содержит не менее двух элементов. Это контрпример к утверждению
«идемпотенты коммутируют во вполне регулярной полугруппе». -/
theorem not_commutative {L R : Type u} (l₁ l₂ : L) (hl : l₁ ≠ l₂) (r : R) :
    (⟨l₁, r⟩ : RectangularBand L R) * ⟨l₂, r⟩ ≠ (⟨l₂, r⟩ : RectangularBand L R) * ⟨l₁, r⟩ := by
  intro h
  have : l₁ = l₂ := congrArg RectangularBand.left h
  exact hl this

end UAMP_RectangularBand
