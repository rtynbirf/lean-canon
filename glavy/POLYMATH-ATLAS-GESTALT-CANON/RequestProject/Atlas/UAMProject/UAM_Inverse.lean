import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Regular
import RequestProject.Atlas.UAMProject.UAM_Group
import RequestProject.Atlas.UAMProject.UAM_Green

namespace UAMP_Inverse
universe u

open UAMP_Idempotent UAMP_Regular UAMP_Group UAMP_Green

variable {M : Type u} [Monoid M]

/-- x is an inverse of a: a * x * a = a ∧ x * a * x = x -/
def IsInverse (a x : M) : Prop := a * x * a = a ∧ x * a * x = x

/-- M is an inverse semigroup: every element has a unique inverse -/
def IsInverseSemigroup (M : Type u) [Monoid M] : Prop := ∀ a : M, ∃! x : M, IsInverse a x

/-- Обращение симметрично. -/
theorem inverse_symm {a x : M} (h : IsInverse a x) : IsInverse x a := ⟨h.2, h.1⟩

/-- Идемпотент является обратным сам себе. -/
theorem idempotent_isInverse_self {e : M} (he : IsIdempotent e) : IsInverse e e := by
  constructor <;> · rw [he, he]

/-- В инверсной полугруппе обратный элемент единствен. -/
theorem unique_inverse (h : IsInverseSemigroup M) {a x y : M}
    (hx : IsInverse a x) (hy : IsInverse a y) : x = y := by
  obtain ⟨z, _, hz⟩ := h a
  rw [hz x hx, hz y hy]

/-- Произведение идемпотентов в инверсной полугруппе идемпотентно. -/
theorem idem_mul_idem (h : IsInverseSemigroup M) {e f : M}
    (he : IsIdempotent e) (hf : IsIdempotent f) : IsIdempotent (e * f) := by
  obtain ⟨x, hx, -⟩ := h (e * f)
  have hA1 : e * f * x * (e * f) = e * f := hx.1
  have hA2 : x * (e * f) * x = x := hx.2
  have hinv : IsInverse (e * f) (f * x * e) := by
    constructor
    · calc e * f * (f * x * e) * (e * f)
          = e * (f * f) * x * (e * e) * f := by simp only [mul_assoc]
        _ = e * f * x * e * f := by rw [he, hf]
        _ = e * f * x * (e * f) := by simp only [mul_assoc]
        _ = e * f := hA1
    · calc f * x * e * (e * f) * (f * x * e)
          = f * (x * (e * e) * (f * f) * x) * e := by simp only [mul_assoc]
        _ = f * (x * e * f * x) * e := by rw [he, hf]
        _ = f * (x * (e * f) * x) * e := by simp only [mul_assoc]
        _ = f * x * e := by rw [hA2]
  have hxe : x = f * x * e := unique_inverse h hx hinv
  have hxidem : IsIdempotent x := by
    show x * x = x
    conv_lhs => rw [hxe]
    calc f * x * e * (f * x * e)
        = f * (x * (e * f) * x) * e := by simp only [mul_assoc]
      _ = f * x * e := by rw [hA2]
      _ = x := hxe.symm
  have hefx : e * f = x :=
    unique_inverse h (inverse_symm hx) (idempotent_isInverse_self hxidem)
  rw [hefx]
  exact hxidem

/-- Idempotents commute in an inverse semigroup.
(В архивной версии гипотеза `IsInverseSemigroup M` была неявной, а доказательство
отсутствовало; здесь гипотеза сделана явной и утверждение доказано.) -/
theorem idempotents_commute (h : IsInverseSemigroup M)
    {e f : M} (he : IsIdempotent e) (hf : IsIdempotent f) : e * f = f * e := by
  have hef : IsIdempotent (e * f) := idem_mul_idem h he hf
  have hfe : IsIdempotent (f * e) := idem_mul_idem h hf he
  have h1 : IsInverse (e * f) (f * e) := by
    constructor
    · calc e * f * (f * e) * (e * f)
          = e * (f * f) * (e * e) * f := by simp only [mul_assoc]
        _ = e * f * e * f := by rw [he, hf]
        _ = (e * f) * (e * f) := by simp only [mul_assoc]
        _ = e * f := hef
    · calc f * e * (e * f) * (f * e)
          = f * (e * e) * (f * f) * e := by simp only [mul_assoc]
        _ = f * e * f * e := by rw [he, hf]
        _ = (f * e) * (f * e) := by simp only [mul_assoc]
        _ = f * e := hfe
  exact unique_inverse h (idempotent_isInverse_self hef) h1

/-- Natural order on idempotents: e ≤ f iff e = e * f -/
def natural_order {M : Type u} [Monoid M] (e f : M) : Prop :=
  IsIdempotent e ∧ IsIdempotent f ∧ e * f = e

/-- Natural order is antisymmetric.
(Гипотеза `IsInverseSemigroup M` сделана явной; в архиве доказательство отсутствовало.) -/
theorem natural_order_antisymm (h : IsInverseSemigroup M)
    {e f : M} (hef : natural_order e f) (hfe : natural_order f e) : e = f := by
  obtain ⟨he, hf, h1⟩ := hef
  obtain ⟨-, -, h2⟩ := hfe
  rw [← h1, idempotents_commute h he hf, h2]

end UAMP_Inverse
