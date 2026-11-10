import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_Regular           -- IsRegular, IsZero
import RequestProject.Atlas.UAM_Congruence       -- IsCongruence, QuotientMonoid
import RequestProject.Atlas.UAM_PrincipalIdeals  -- principalLeft, principalRight, principalIdeal

/-!
# UAM — Layer 7: Идеалы (Ideal)

Идеал — непустое подмножество моноида, поглощающее умножение. В отличие от
подмоноида (Layer 3), идеал не обязан содержать `1`. Rees-конгруэнция по идеалу
склеивает весь идеал в один класс и оставляет элементы вне идеала нетронутыми.
-/

namespace UAM_Ideal
universe u

open UAM_Directionality UAM_Idempotent UAM_Regular UAM_Congruence

variable {M : Type u} [Monoid M]

/-! ### §0. Собственные определения -/

/-- Левый идеал: непустое подмножество, поглощающее умножение слева. -/
structure IsLeftIdeal (I : Set M) : Prop where
  nonempty : I.Nonempty
  left_absorb : ∀ a : M, ∀ b ∈ I, a * b ∈ I

/-- Правый идеал: непустое подмножество, поглощающее умножение справа. -/
structure IsRightIdeal (I : Set M) : Prop where
  nonempty : I.Nonempty
  right_absorb : ∀ a : M, ∀ b ∈ I, b * a ∈ I

/-- Двусторонний идеал. -/
structure IsIdeal (I : Set M) : Prop where
  nonempty : I.Nonempty
  left_absorb : ∀ a : M, ∀ b ∈ I, a * b ∈ I
  right_absorb : ∀ a : M, ∀ b ∈ I, b * a ∈ I

/-! ### §1. Базовые свойства идеалов -/

/-- В левом идеале произведение двух элементов идеала снова в идеале. -/
theorem left_ideal_mul_mem {I : Set M} (hI : IsLeftIdeal I) {a b : M} :
    a ∈ I → b ∈ I → a * b ∈ I :=
  fun _ hb => hI.left_absorb a b hb

/-- В правом идеале произведение двух элементов идеала снова в идеале. -/
theorem right_ideal_mul_mem {I : Set M} (hI : IsRightIdeal I) {a b : M} :
    a ∈ I → b ∈ I → a * b ∈ I :=
  fun ha _ => hI.right_absorb b a ha

/-- В двустороннем идеале произведение двух элементов идеала снова в идеале. -/
theorem ideal_mul_mem {I : Set M} (hI : IsIdeal I) {a b : M} :
    a ∈ I → b ∈ I → a * b ∈ I :=
  fun _ hb => hI.left_absorb a b hb

/-- Главный левый идеал действительно является левым идеалом. -/
theorem principalLeft_is_left_ideal (a : M) : IsLeftIdeal (principalLeft a) where
  nonempty := ⟨a, ⟨1, one_mul a⟩⟩
  left_absorb := fun c _ ⟨y, hy⟩ => ⟨c * y, by rw [mul_assoc, hy]⟩

/-- Главный правый идеал действительно является правым идеалом. -/
theorem principalRight_is_right_ideal (a : M) : IsRightIdeal (principalRight a) where
  nonempty := ⟨a, ⟨1, mul_one a⟩⟩
  right_absorb := fun c _ ⟨y, hy⟩ => ⟨y * c, by rw [← mul_assoc, hy]⟩

/-- Главный двусторонний идеал действительно является идеалом. -/
theorem principalIdeal_is_ideal (a : M) : IsIdeal (principalIdeal a) where
  nonempty := ⟨a, ⟨1, 1, by rw [one_mul, mul_one]⟩⟩
  left_absorb := fun c _ ⟨y, z, hyz⟩ => ⟨c * y, z, by rw [← hyz]; simp only [mul_assoc]⟩
  right_absorb := fun c _ ⟨y, z, hyz⟩ => ⟨y, z * c, by rw [← hyz]; simp only [mul_assoc]⟩

/-- Если двусторонний идеал содержит `1`, то он совпадает со всем моноидом. -/
theorem ideal_contains_one_iff_top {I : Set M} (hI : IsIdeal I) (h1 : (1 : M) ∈ I) :
    I = Set.univ := by
  ext x
  constructor
  · intro _; trivial
  · intro _
    have := hI.left_absorb x 1 h1
    rwa [mul_one] at this

/-! ### §2. Связь с достижимостью -/

/-- Главный правый идеал совпадает с множеством правой достижимости. -/
theorem principalRight_eq_reach (a : M) :
    principalRight a = UAM_Reachability.reach a := by
  ext x
  simp only [principalRight, UAM_Reachability.reach, algLe, Set.mem_setOf_eq]

/-- Главный левый идеал совпадает с множеством левой достижимости. -/
theorem principalLeft_eq_reachLeft (a : M) :
    principalLeft a = UAM_Reachability.reachLeft a := by
  ext x
  simp only [principalLeft, UAM_Reachability.reachLeft, Set.mem_setOf_eq]

/-- Главный правый идеал содержится в главном двустороннем идеале. -/
theorem principal_ideal_superset_right (a : M) :
    principalRight a ⊆ principalIdeal a := by
  rintro x ⟨y, hy⟩
  exact ⟨1, y, by rw [one_mul, hy]⟩

/-! ### §3. Rees-конгруэнция по идеалу -/

/-- Rees-конгруэнция по идеалу `I`: элементы эквивалентны, если оба в `I`, или равны. -/
def reesCongruence (I : Set M) (hI : IsIdeal I) : IsCongruence M where
  r a b := (a ∈ I ∧ b ∈ I) ∨ a = b
  refl := fun _ => Or.inr rfl
  symm := fun _ _ => by
    rintro (⟨ha, hb⟩ | rfl)
    · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr rfl
  trans := fun _ _ _ => by
    rintro (⟨ha, hb⟩ | rfl) (⟨hb', hc⟩ | rfl)
    · exact Or.inl ⟨ha, hc⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inl ⟨hb', hc⟩
    · exact Or.inr rfl
  mul_compat := fun a b c d => by
    rintro (⟨ha, hb⟩ | rfl) (⟨hc, hd⟩ | rfl)
    · exact Or.inl ⟨hI.left_absorb a c hc, hI.left_absorb b d hd⟩
    · exact Or.inl ⟨hI.right_absorb c a ha, hI.right_absorb c b hb⟩
    · exact Or.inl ⟨hI.left_absorb a c hc, hI.left_absorb a d hd⟩
    · exact Or.inr rfl
  one_compat := Or.inr rfl

/-- Любые два элемента идеала связаны Rees-конгруэнцией. -/
theorem reesCongruence_ideal_class {I : Set M} (hI : IsIdeal I) {a z : M}
    (ha : a ∈ I) (hz : z ∈ I) : (reesCongruence I hI).r a z :=
  Or.inl ⟨ha, hz⟩

/-- Вне идеала Rees-конгруэнция совпадает с равенством. -/
theorem reesCongruence_outside {I : Set M} (hI : IsIdeal I) {a b : M}
    (ha : a ∉ I) : (reesCongruence I hI).r a b ↔ a = b := by
  constructor
  · rintro (⟨h1, _⟩ | hab)
    · exact absurd h1 ha
    · exact hab
  · intro hab; exact Or.inr hab

/-- Если `a ∈ I` регулярен, то `a * x ∈ I` и `x * a ∈ I` для свидетеля регулярности `x`. -/
theorem reesCongruence_regular {I : Set M} (hI : IsIdeal I) {a : M}
    (ha : a ∈ I) (hreg : UAM_Regular.IsRegular a) :
    ∃ x, a * x * a = a ∧ a * x ∈ I ∧ x * a ∈ I := by
  obtain ⟨x, hx⟩ := hreg
  exact ⟨x, hx, hI.right_absorb x a ha, hI.left_absorb x a ha⟩

/-- Умножение элемента идеала справа на произвольный элемент даёт элемент,
    Rees-конгруэнтный исходному. -/
theorem reesCongruence_ideal_absorb {I : Set M} (hI : IsIdeal I)
    {a b : M} (ha : a ∈ I) :
    (reesCongruence I hI).r (a * b) a :=
  Or.inl ⟨hI.right_absorb b a ha, ha⟩

end UAM_Ideal
