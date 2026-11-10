import Mathlib.Tactic

namespace UAMP_Directionality
universe u

/-- Algebraic preorder: a ≤ b iff ∃ c, a * c = b -/
def algLe {M : Type u} [Monoid M] (a b : M) : Prop := ∃ c : M, a * c = b

theorem algLe_refl {M : Type u} [Monoid M] (a : M) : algLe a a := ⟨1, by rw [mul_one]⟩

theorem algLe_trans {M : Type u} [Monoid M] {a b c : M}
    (hab : algLe a b) (hbc : algLe b c) : algLe a c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  exact ⟨x * y, by rw [← mul_assoc, hx, hy]⟩

theorem algLe_mul_right {M : Type u} [Monoid M] (a b : M) : algLe a (a * b) := ⟨b, rfl⟩

end UAMP_Directionality
