import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Regular
import RequestProject.Atlas.UAMProject.UAM_Ideal
import RequestProject.Atlas.UAMProject.UAM_Congruence
import RequestProject.Atlas.UAMProject.UAM_Morphism

namespace UAMP_Extension
universe u

open UAMP_Ideal UAMP_Regular UAMP_Morphism

variable {M N : Type u} [Monoid M] [Monoid N]

/-- N is an extension of M by ideal I: ∃ injective f : N → M preserving structure,
    with range(f) = I (an ideal of M) -/
def IsExtension : Prop :=
  ∃ (f : N → M), f 1 = 1 ∧ (∀ a b, f (a * b) = f a * f b) ∧
    Function.Injective f ∧ ∃ (I : Set M), IsIdeal I ∧ Set.range f = I

/-- Trivial extension: identity embedding of any monoid into itself with ideal = whole monoid -/
theorem trivial_extension : IsExtension (M := M) (N := M) :=
  ⟨id, rfl, fun _ _ => rfl, Function.injective_id, Set.univ,
    ⟨⟨⟨1, Set.mem_univ _⟩, fun _ _ _ => Set.mem_univ _⟩,
      ⟨⟨1, Set.mem_univ _⟩, fun _ _ _ => Set.mem_univ _⟩⟩, Set.range_id⟩

/- Архивные формулировки

theorem extension_preserves_regular (f : N → M) (hmul) (a : N) (ha : IsRegular (f a)) : IsRegular a
theorem extension_preserves_idempotent (f : N → M) (hmul) (h1 : f 1 = 1) (a : N)
    (ha : IsIdempotent (f a)) : IsIdempotent a

в таком виде недоказуемы: без инъективности `f` из равенства образов не следует
равенство прообразов, а для регулярности нужен ещё и прообраз свидетеля.
Ниже — верные версии. -/

/-- Инъективное вложение отражает регулярность, если свидетель лежит в образе. -/
theorem extension_preserves_regular (f : N → M) (hmul : ∀ a b, f (a * b) = f a * f b)
    (hinj : Function.Injective f) (a : N) (ha : ∃ y : N, f a * f y * f a = f a) :
    UAMP_Regular.IsRegular a := by
  obtain ⟨y, hy⟩ := ha
  refine ⟨y, hinj ?_⟩
  rw [hmul, hmul]
  exact hy

/-- Инъективное вложение отражает идемпотентность. -/
theorem extension_preserves_idempotent (f : N → M) (hmul : ∀ a b, f (a * b) = f a * f b)
    (hinj : Function.Injective f) (a : N) (ha : UAMP_Idempotent.IsIdempotent (f a)) :
    UAMP_Idempotent.IsIdempotent a := by
  apply hinj
  rw [hmul]
  exact ha

end UAMP_Extension
