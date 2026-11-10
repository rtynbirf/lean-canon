import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_Morphism         -- MonoidMorphism

/-!
# UAM — Layer 8: Свободный моноид (Free)

Свободный моноид `FreeMonoid α` — моноид слов (списков) над алфавитом `α`
с конкатенацией. Формулируется универсальное свойство: любое отображение
алфавита в произвольный моноид единственным образом продолжается до морфизма
свободного моноида.
-/

namespace UAM_Free
universe u

open UAM_Idempotent UAM_Morphism

/-- Свободный моноид над алфавитом `α`: слова с конкатенацией.
    Используем `abbrev`, чтобы прозрачно наследовать нотацию и леммы `List`. -/
abbrev FreeMonoid (α : Type u) := List α

namespace FreeMonoid
variable {α : Type u}

/-- Пустое слово — единица свободного моноида. -/
def empty : FreeMonoid α := []

/-- Конкатенация слов. -/
def concat (w1 w2 : FreeMonoid α) : FreeMonoid α := w1 ++ w2

/-- Одиночный символ как слово. -/
def of (a : α) : FreeMonoid α := [a]

/-- Свободный моноид является моноидом. -/
instance instMonoid : Monoid (FreeMonoid α) where
  mul := concat
  mul_assoc a b c := List.append_assoc a b c
  one := empty
  one_mul := List.nil_append
  mul_one := List.append_nil

/-! ### §1. Базовые свойства -/

/-- Одиночный символ — непустое слово. -/
theorem empty_ne_of (a : α) : of a ≠ empty := by
  intro h
  exact List.cons_ne_nil a [] h

/-- Конкатенация двух одиночных символов даёт двухбуквенное слово. -/
theorem concat_of_of (a b : α) : concat (of a) (of b) = [a, b] := rfl

/-- Ассоциативность конкатенации. -/
theorem concat_assoc' (w1 w2 w3 : FreeMonoid α) :
    concat (concat w1 w2) w3 = concat w1 (concat w2 w3) :=
  List.append_assoc w1 w2 w3

/-- Вложение алфавита инъективно. -/
theorem of_injective : Function.Injective (of : α → FreeMonoid α) :=
  fun _ _ h => (List.cons.inj h).1

/-- Длина конкатенации — сумма длин. -/
theorem length_concat (w1 w2 : FreeMonoid α) :
    (w1 ++ w2).length = w1.length + w2.length :=
  List.length_append

/-- Длина пустого слова равна нулю. -/
theorem length_empty : ((empty : FreeMonoid α)).length = 0 := rfl

/-! ### §2. Универсальное свойство -/

/-- Рекурсивное продолжение отображения алфавита на слова. -/
def liftFun {N : Type u} [Monoid N] (f : α → N) : List α → N
  | [] => 1
  | a :: ws => f a * liftFun f ws

/-- Универсальное свойство: любое `f : α → N` продолжается до морфизма
    свободного моноида в `N`. -/
def lift {N : Type u} [Monoid N] (f : α → N) : MonoidMorphism (FreeMonoid α) N where
  toFun := liftFun f
  map_mul := by
    intro w1 w2
    show liftFun f (w1 ++ w2) = liftFun f w1 * liftFun f w2
    induction w1 with
    | nil => simp [liftFun]
    | cons a ws ih => simp only [List.cons_append, liftFun, ih, mul_assoc]
  map_one := rfl

/-- Продолжение согласовано с вложением алфавита. -/
theorem lift_of {N : Type u} [Monoid N] (f : α → N) (a : α) :
    (lift f).toFun (of a) = f a := by
  show liftFun f [a] = f a
  simp [liftFun]

/-- Единственность продолжения: любой морфизм, согласованный с `f` на алфавите,
    совпадает с `lift f`. -/
theorem lift_unique {N : Type u} [Monoid N] (f : α → N)
    (g : MonoidMorphism (FreeMonoid α) N)
    (h_compat : ∀ a, g.toFun (of a) = f a) (w : FreeMonoid α) :
    g.toFun w = (lift f).toFun w := by
  induction w with
  | nil =>
    show g.toFun 1 = (1 : N)
    exact g.map_one
  | cons a ws ih =>
    show g.toFun (of a * ws) = liftFun f (a :: ws)
    rw [g.map_mul, h_compat a, ih]
    rfl

/-! ### §3. Связь с идемпотентами -/

/-- Пустое слово идемпотентно. -/
theorem empty_idempotent : IsIdempotent (empty : FreeMonoid α) := rfl

/-- Одиночный символ не идемпотентен. -/
theorem of_not_idempotent (a : α) : ¬ IsIdempotent (of a) := by
  intro h
  have h' : ([a, a] : FreeMonoid α) = [a] := h
  exact List.cons_ne_nil a [] (List.cons.inj h').2

end FreeMonoid
end UAM_Free
