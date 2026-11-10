import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Reachability
import RequestProject.Atlas.UAMProject.UAM_Green
import RequestProject.Atlas.UAMProject.UAM_Group
import RequestProject.Atlas.UAMProject.UAM_Submonoid
import RequestProject.Atlas.UAMProject.UAM_Inverse

namespace UAMP_FiniteSemigroup
universe u

open UAMP_Idempotent UAMP_Reachability

variable {M : Type u} [Monoid M]

/-- In a finite monoid, every element has an idempotent power.
(В архиве доказательство отсутствовало; здесь оно проведено по принципу Дирихле.) -/
theorem exists_idempotent_pow [Fintype M] (a : M) : ∃ n > 0, IsIdempotent (a ^ n) := by
  obtain ⟨i, j, hij, hEq⟩ : ∃ i j : ℕ, i < j ∧ a ^ i = a ^ j := by
    obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, heq⟩
    · exact ⟨j, i, h, heq.symm⟩
  obtain ⟨d, hd0, hdj⟩ : ∃ d, 0 < d ∧ i + d = j := ⟨j - i, by omega, by omega⟩
  have hbase : a ^ (i + d) = a ^ i := by rw [hdj, hEq]
  have hstep : ∀ n, i ≤ n → a ^ (n + d) = a ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hbase
    | succ n hn ih =>
      have hrw : n + 1 + d = (n + d) + 1 := by omega
      rw [hrw, pow_succ, ih, ← pow_succ]
  have hmul : ∀ t n, i ≤ n → a ^ (n + t * d) = a ^ n := by
    intro t
    induction t with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      have h1 : n + (k + 1) * d = (n + k * d) + d := by ring
      rw [h1, hstep _ (le_trans hn (Nat.le_add_right _ _)), ih n hn]
  have hm : i ≤ (i + 1) * d :=
    le_trans (Nat.le_succ i) (Nat.le_mul_of_pos_right _ hd0)
  refine ⟨(i + 1) * d, Nat.mul_pos (Nat.succ_pos i) hd0, ?_⟩
  show a ^ ((i + 1) * d) * a ^ ((i + 1) * d) = a ^ ((i + 1) * d)
  rw [← pow_add]
  exact hmul (i + 1) ((i + 1) * d) hm

/-- Finite monoid has an idempotent -/
theorem exists_idempotent [Fintype M] : ∃ e : M, IsIdempotent e := by
  obtain ⟨n, -, hidem⟩ := exists_idempotent_pow (1 : M)
  exact ⟨(1 : M) ^ n, hidem⟩

/- Архивная формулировка

theorem hclass_with_idempotent_is_group [Fintype M] {e a : M}
    (he : IsIdempotent e) (ha : H_eq e a) : IsUnit' a

неверна: элементы H-класса идемпотента `e` обратимы относительно `e`, а не
относительно единицы моноида (например, в моноиде `{1, 0}` элемент `0`
H-эквивалентен идемпотенту `0`, но не обратим). Ниже — верная версия
(теорема Грина), причём конечность не требуется. -/
theorem hclass_relative_unit {e a : M} (he : IsIdempotent e) (ha : UAMP_Green.H_eq e a) :
    ∃ x, a * x = e ∧ x * a = e := by
  have hea : e * a = a := UAMP_Submonoid.idem_mul_left he ha
  have hae : a * e = a := UAMP_Submonoid.idem_mul_right he ha
  have hy : e ∈ reach a := by rw [← ha.1]; exact mem_reach_self e
  have hz : e ∈ reachLeft a := by rw [← ha.2]; exact mem_reachLeft_self e
  obtain ⟨y, hy⟩ := hy
  obtain ⟨z, hz⟩ := hz
  refine ⟨e * y, ?_, ?_⟩
  · rw [← mul_assoc, hae, hy]
  · calc e * y * a = (z * a) * y * a := by rw [hz]
      _ = z * (a * y) * a := by simp only [mul_assoc]
      _ = z * (e * a) := by rw [hy, mul_assoc]
      _ = z * a := by rw [hea]
      _ = e := hz

/- Архивная формулировка `finite_inverse_is_semilattice_of_groups` утверждала
обратимость каждого элемента инверсной полугруппы относительно единицы моноида,
что неверно по той же причине. Верная версия: у каждого элемента есть обратный,
и оба произведения `a*x`, `x*a` идемпотентны (конечность не требуется). -/
theorem inverse_semigroup_idempotent_products (h : UAMP_Inverse.IsInverseSemigroup M) (a : M) :
    ∃ x, a * x * a = a ∧ x * a * x = x ∧ IsIdempotent (a * x) ∧ IsIdempotent (x * a) := by
  obtain ⟨x, hx, -⟩ := h a
  refine ⟨x, hx.1, hx.2, ?_, ?_⟩
  · show a * x * (a * x) = a * x
    calc a * x * (a * x) = (a * x * a) * x := by simp only [mul_assoc]
      _ = a * x := by rw [hx.1]
  · show x * a * (x * a) = x * a
    calc x * a * (x * a) = (x * a * x) * a := by simp only [mul_assoc]
      _ = x * a := by rw [hx.2]

end UAMP_FiniteSemigroup
