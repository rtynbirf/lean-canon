import Mathlib.Tactic

/-!
# UAM — Layer (Application): Моноид преобразований (Action)

Моноидная структура на функциях `Q → Q` с умножением-композицией в порядке
«сначала левый сомножитель»: `f * g = g ∘ f`. Единица — тождественная функция.

Этот порядок согласован с чтением слов слева направо в DFA: если `f`
соответствует действию слова `w₁`, а `g` — действию слова `w₂`, то `f * g`
соответствует действию `w₁ ++ w₂`.

**Важно.** Эта инстанция вводится в отдельном namespace `UAM_Action`, чтобы
активировать её точечно (через `open UAM_Action`) и не конфликтовать с
поточечным `Pi.monoid`, который Mathlib синтезирует на `Q → Q`.
-/

namespace UAM_Action
universe u

/-- Моноид преобразований `Q → Q`: `f * g = g ∘ f`, единица — тождество. -/
instance instMonoid {Q : Type u} : Monoid (Q → Q) where
  mul f g := g ∘ f
  one := id
  mul_assoc := fun _ _ _ => rfl
  one_mul := fun _ => rfl
  mul_one := fun _ => rfl

variable {Q : Type u}

/-- Определяющее равенство для умножения преобразований. -/
theorem mul_def (f g : Q → Q) : f * g = g ∘ f := rfl

/-- Значение произведения в точке. -/
theorem mul_apply (f g : Q → Q) (q : Q) : (f * g) q = g (f q) := rfl

/-- Единица — тождественная функция. -/
theorem one_def : (1 : Q → Q) = id := rfl

/-- Значение единицы в точке. -/
theorem one_apply (q : Q) : (1 : Q → Q) q = q := rfl

end UAM_Action
