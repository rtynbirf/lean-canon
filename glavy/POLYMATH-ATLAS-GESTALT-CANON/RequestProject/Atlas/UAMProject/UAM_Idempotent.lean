import Mathlib.Tactic

namespace UAMP_Idempotent
universe u

/-- Element a is idempotent: a * a = a -/
def IsIdempotent {M : Type u} [Monoid M] (a : M) : Prop := a * a = a

theorem one_idempotent {M : Type u} [Monoid M] : IsIdempotent (1 : M) := by
  rw [IsIdempotent, mul_one]

/-- Исходная формулировка требовала `a ^ n = a` для всех `n`, что неверно при `n = 0`
(тогда `a ^ 0 = 1`). Добавлено условие `0 < n`. -/
theorem idempotent_pow {M : Type u} [Monoid M] {a : M} (h : IsIdempotent a) (n : Nat)
    (hn : 0 < n) : a ^ n = a := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; rw [pow_one]
    · rw [pow_succ, ih hk]; exact h

theorem idempotent_mul_idempotent_of_comm {M : Type u} [Monoid M] {a b : M}
    (ha : IsIdempotent a) (hb : IsIdempotent b) (hcomm : a * b = b * a) :
    IsIdempotent (a * b) := by
  unfold IsIdempotent at ha hb ⊢
  calc a * b * (a * b) = a * (b * a) * b := by simp [mul_assoc]
    _ = a * (a * b) * b := by rw [hcomm]
    _ = (a * a) * (b * b) := by simp [mul_assoc]
    _ = a * b := by rw [ha, hb]

end UAMP_Idempotent
