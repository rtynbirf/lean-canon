import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Morphism

namespace UAMP_DirectProduct
universe u

open UAMP_Idempotent

/-- Direct product M × N -/
abbrev DirectProduct (M N : Type u) := M × N

/- Моноидная структура на прямом произведении: поскольку `DirectProduct M N`
это сокращение для `M × N`, используется стандартный инстанс `Prod.instMonoid`
(архивная версия объявляла собственный неполный инстанс, конфликтующий с ним). -/
example (M N : Type u) [Monoid M] [Monoid N] : Monoid (DirectProduct M N) := inferInstance

/-- First projection as a morphism -/
def fst (M N : Type u) [Monoid M] [Monoid N] : UAMP_Morphism.MonoidMorphism (DirectProduct M N) M where
  toFun := fun p => p.1
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- Second projection as a morphism -/
def snd (M N : Type u) [Monoid M] [Monoid N] : UAMP_Morphism.MonoidMorphism (DirectProduct M N) N where
  toFun := fun p => p.2
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- Pair construction -/
def pair (M N : Type u) [Monoid M] [Monoid N] (a : M) (b : N) : DirectProduct M N := ⟨a, b⟩

/-- Diagonal embedding -/
def diag (M : Type u) [Monoid M] : UAMP_Morphism.MonoidMorphism M (DirectProduct M M) where
  toFun := fun a => ⟨a, a⟩
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- First projection preserves idempotents -/
theorem isIdempotent_fst {M N : Type u} [Monoid M] [Monoid N] {p : DirectProduct M N}
    (h : IsIdempotent p) : IsIdempotent p.1 := congrArg Prod.fst h

/-- Second projection preserves idempotents -/
theorem isIdempotent_snd {M N : Type u} [Monoid M] [Monoid N] {p : DirectProduct M N}
    (h : IsIdempotent p) : IsIdempotent p.2 := congrArg Prod.snd h

/-- Direct product preserves regularity -/
theorem isRegular_prod {M N : Type u} [Monoid M] [Monoid N] {p : DirectProduct M N}
    (h : UAMP_Regular.IsRegular p) : UAMP_Regular.IsRegular p.1 ∧ UAMP_Regular.IsRegular p.2 := by
  obtain ⟨x, hx⟩ := h
  exact ⟨⟨x.1, congrArg Prod.fst hx⟩, ⟨x.2, congrArg Prod.snd hx⟩⟩

/-- Projection as morphism (projectMorphism alias) -/
def projMorphism (M N : Type u) [Monoid M] [Monoid N] :
    UAMP_Morphism.MonoidMorphism (DirectProduct M N) M := fst M N

end UAMP_DirectProduct
