import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Group
import RequestProject.Atlas.UAMProject.UAM_Regular
import RequestProject.Atlas.UAMProject.UAM_Congruence

namespace UAMP_Morphism
universe u

open UAMP_Congruence UAMP_Idempotent UAMP_Group UAMP_Regular

/-- Custom MonoidMorphism (NOT Mathlib's MonoidHom) -/
structure MonoidMorphism (M N : Type u) [Monoid M] [Monoid N] where
  toFun : M → N
  map_mul : ∀ a b : M, toFun (a * b) = toFun a * toFun b
  map_one : toFun 1 = 1

instance {M N : Type u} [Monoid M] [Monoid N] :
    CoeFun (MonoidMorphism M N) (fun _ => M → N) := ⟨MonoidMorphism.toFun⟩

variable {M N P : Type u} [Monoid M] [Monoid N] [Monoid P]

/-- Два морфизма равны, если равны их носители (поля-доказательства
несущественны в силу пропозициональной иррелевантности). -/
theorem morphism_ext {M N : Type u} [Monoid M] [Monoid N]
    {F G : MonoidMorphism M N} (h : F.toFun = G.toFun) : F = G := by
  cases F; cases G; cases h; rfl

/-- Kernel of a morphism: a congruence where r a b := f a = f b -/
def kernel (f : MonoidMorphism M N) : IsCongruence M where
  r := fun a b => f.toFun a = f.toFun b
  refl := fun _ => rfl
  symm := fun _ _ => Eq.symm
  trans := fun _ _ _ hab hbc => hab.trans hbc
  mul_compat := fun _ _ _ _ hab hcd => by
    rw [f.map_mul, f.map_mul, hab, hcd]
  one_compat := rfl

/-- Range of a morphism -/
def range (f : MonoidMorphism M N) : Set N := Set.range f.toFun

/-- Composition of morphisms -/
def comp (g : MonoidMorphism N P) (f : MonoidMorphism M N) : MonoidMorphism M P where
  toFun := g.toFun ∘ f.toFun
  map_mul := fun a b => by
    show g.toFun (f.toFun (a * b)) = g.toFun (f.toFun a) * g.toFun (f.toFun b)
    rw [f.map_mul, g.map_mul]
  map_one := by
    show g.toFun (f.toFun 1) = 1
    rw [f.map_one, g.map_one]

/-- Identity morphism -/
def idMorphism (M : Type u) [Monoid M] : MonoidMorphism M M where
  toFun := id
  map_mul := fun _ _ => rfl
  map_one := rfl

theorem comp_id (f : MonoidMorphism M N) : comp (idMorphism N) f = f := rfl

theorem id_comp (f : MonoidMorphism M N) : comp f (idMorphism M) = f := rfl

theorem kernel_eq_iff (f : MonoidMorphism M N) {a b : M} :
    (kernel f).r a b ↔ f.toFun a = f.toFun b := Iff.rfl

theorem kernel_contains_one (f : MonoidMorphism M N) (a : M) (ha : (kernel f).r a 1) :
    f.toFun a = 1 := by rw [show (1 : N) = f.toFun 1 from f.map_one.symm]; exact ha

theorem mem_range_iff (f : MonoidMorphism M N) (b : N) :
    b ∈ range f ↔ ∃ a : M, f.toFun a = b := Iff.rfl

/-- Morphisms preserve idempotents -/
theorem map_idempotent (f : MonoidMorphism M N) {a : M} (ha : IsIdempotent a) :
    IsIdempotent (f.toFun a) := by
  show f.toFun a * f.toFun a = f.toFun a
  rw [← f.map_mul, ha]

/-- Morphisms preserve units -/
theorem map_isUnit (f : MonoidMorphism M N) {a : M} (ha : IsUnit' a) :
    IsUnit' (f.toFun a) := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨f.toFun b, ?_, ?_⟩
  · rw [← f.map_mul, hb.1, f.map_one]
  · rw [← f.map_mul, hb.2, f.map_one]

/-- Morphisms preserve regular elements -/
theorem map_isRegular (f : MonoidMorphism M N) {a : M} (ha : UAMP_Regular.IsRegular a) :
    UAMP_Regular.IsRegular (f.toFun a) := by
  obtain ⟨x, hx⟩ := ha
  refine ⟨f.toFun x, ?_⟩
  rw [← f.map_mul, ← f.map_mul, hx]

/-- Morphisms preserve zeros (under surjectivity) -/
theorem map_isZero (f : MonoidMorphism M N) (hsur : Function.Surjective f.toFun)
    {z : M} (hz : UAMP_Regular.IsZero z) : UAMP_Regular.IsZero (f.toFun z) := by
  intro a
  obtain ⟨b, hb⟩ := hsur a
  rw [← hb]
  refine ⟨?_, ?_⟩
  · rw [← f.map_mul, (hz b).1]
  · rw [← f.map_mul, (hz b).2]

/-- Lift through quotient -/
def liftThroughQuotient (f : MonoidMorphism M N)
    (h : ∀ a b, (kernel f).r a b → f.toFun a = f.toFun b) :
    MonoidMorphism (QuotientMonoid (kernel f)) N where
  toFun := Quotient.lift f.toFun h
  map_mul := fun x y => Quotient.inductionOn₂ x y (fun a b => f.map_mul a b)
  map_one := f.map_one

theorem lift_mk (f : MonoidMorphism M N)
    (h : ∀ a b, (kernel f).r a b → f.toFun a = f.toFun b) (a : M) :
    (liftThroughQuotient f h).toFun (mk (kernel f) a) = f.toFun a := rfl

/-- Первая теорема об изоморфизме (инъективная часть): факторизация по ядру
даёт инъективный морфизм. Архивная версия строила `MonoidHom` в подтип образа,
что не типизировалось; здесь то же содержание выражено через инъективность
и совпадение образов. -/
theorem liftThroughQuotient_injective (f : MonoidMorphism M N)
    (h : ∀ a b, (kernel f).r a b → f.toFun a = f.toFun b) :
    Function.Injective (liftThroughQuotient f h).toFun := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => exact Quotient.sound (hxy : f.toFun a = f.toFun b)

theorem liftThroughQuotient_range (f : MonoidMorphism M N)
    (h : ∀ a b, (kernel f).r a b → f.toFun a = f.toFun b) :
    Set.range (liftThroughQuotient f h).toFun = range f := by
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨x, rfl⟩
    induction x using Quotient.inductionOn with
    | _ a => exact ⟨a, rfl⟩
  · rintro y ⟨a, rfl⟩
    exact ⟨mk (kernel f) a, rfl⟩

end UAMP_Morphism
