import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Morphism

namespace UAMP_Free
universe u

open UAMP_Morphism UAMP_Idempotent

/-- Free monoid over α: abbreviation for List α -/
abbrev FreeMonoid (α : Type u) := List α

/-- Monoid instance on FreeMonoid: multiplication = concatenation, unit = empty list -/
instance FreeMonoid.monoid (α : Type u) : Monoid (FreeMonoid α) where
  mul := List.append
  one := []
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

/-- Empty word -/
def empty (α : Type u) : FreeMonoid α := []

/-- Concatenation -/
def concat (α : Type u) (w₁ w₂ : FreeMonoid α) : FreeMonoid α := w₁ ++ w₂

/-- Singleton word -/
def of {α : Type u} (a : α) : FreeMonoid α := [a]

/-- Свёртка по конкатенации: значение свободного морфизма на произведении слов. -/
theorem foldr_append_mul {α : Type u} {N : Type u} [Monoid N] (f : α → N)
    (w₁ w₂ : List α) :
    (w₁ ++ w₂).foldr (fun a acc => f a * acc) 1
      = (w₁.foldr (fun a acc => f a * acc) 1) * (w₂.foldr (fun a acc => f a * acc) 1) := by
  induction w₁ with
  | nil => simp
  | cons a w ih => simp [ih, mul_assoc]

/-- Universal property: lift a function α → N to a monoid morphism FreeMonoid α → N -/
def lift {α : Type u} {N : Type u} [Monoid N] (f : α → N) : MonoidMorphism (FreeMonoid α) N where
  toFun := fun w => w.foldr (fun a acc => f a * acc) 1
  map_mul := fun w₁ w₂ => foldr_append_mul f w₁ w₂
  map_one := by
    show ([] : FreeMonoid α).foldr _ 1 = 1
    rfl

theorem lift_of {α : Type u} {N : Type u} [Monoid N] (f : α → N) (a : α) :
    (lift f).toFun (of a) = f a := by
  show ([a] : FreeMonoid α).foldr _ _ = _
  rw [List.foldr_cons, List.foldr_nil, mul_one]

theorem lift_unique {α : Type u} {N : Type u} [Monoid N] (f : α → N)
    (g : MonoidMorphism (FreeMonoid α) N) (h : ∀ a, g.toFun (of a) = f a) :
    g = lift f := by
  apply UAMP_Morphism.morphism_ext
  funext w
  induction w with
  | nil => exact g.map_one.trans (lift f).map_one.symm
  | cons a w ih =>
    have hcons : (a :: w : FreeMonoid α) = of a * w := rfl
    rw [hcons, g.map_mul, ih, h a]
    rfl

theorem empty_idempotent (α : Type u) : IsIdempotent (@empty α) := by
  rw [IsIdempotent]
  rfl

/-- Однобуквенное слово не идемпотентно.
(В архивной версии предполагались лишние инстансы `Inhabited`/`Nontrivial`.) -/
theorem of_not_idempotent {α : Type u} (a : α) : ¬ IsIdempotent (of a) := by
  intro h
  have h' : ([a, a] : List α) = [a] := h
  simp at h'

theorem of_injective {α : Type u} : Function.Injective (@of α) := by
  intro a b h
  have h' : ([a] : List α) = [b] := h
  simpa using h'

end UAMP_Free
