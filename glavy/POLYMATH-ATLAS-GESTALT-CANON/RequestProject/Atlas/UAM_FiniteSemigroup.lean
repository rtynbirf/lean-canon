import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Reachability

/-!
# UAM — Конечные полугруппы (Finite Semigroups)

Ключевое свойство конечных полугрупп (моноидов): у каждого элемента есть
положительная идемпотентная степень. Отсюда следует, что всякий непустой
конечный моноид содержит идемпотент.

Доказательство опирается на принцип Дирихле: отображение `n ↦ aⁿ` не может быть
инъективным на бесконечном `ℕ` при конечном носителе, поэтому найдутся `i < j` с
`aⁱ = aʲ`. Пусть `p = j - i > 0`. Тогда последовательность степеней
периодична с периодом `p`, начиная с показателя `i`, и подходящая степень,
кратная `p`, оказывается идемпотентной.
-/

namespace UAM_FiniteSemigroup
universe u

open UAM_Idempotent

variable {M : Type u} [Monoid M]

/-- Периодичность степеней: если `aⁱ = aⁱ⁺ᵖ`, то степени периодичны с периодом
    `p` для всех показателей `≥ i`. -/
theorem pow_periodic {a : M} {i p : ℕ} (hper : a ^ i = a ^ (i + p))
    {m : ℕ} (hm : i ≤ m) : a ^ m = a ^ (m + p) := by
  obtain ⟨t, rfl⟩ := Nat.le.dest hm
  rw [pow_add a i t, hper, ← pow_add]
  congr 1
  exact Nat.add_right_comm i p t

/-- Кратная периодичность: `a^(N + k·p) = a^N` при `N ≥ i` и периоде `p`. -/
theorem pow_add_mul_period {a : M} {i p : ℕ} (hper : a ^ i = a ^ (i + p))
    {N : ℕ} (hN : i ≤ N) (k : ℕ) : a ^ (N + k * p) = a ^ N := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hstep : a ^ (N + n * p) = a ^ (N + n * p + p) :=
      pow_periodic hper (le_trans hN (Nat.le_add_right _ _))
    calc a ^ (N + (n + 1) * p) = a ^ (N + n * p + p) := by ring_nf
      _ = a ^ (N + n * p) := hstep.symm
      _ = a ^ N := ih

/-- **В конечном моноиде у каждого элемента есть положительная идемпотентная
    степень.** -/
theorem exists_idempotent_pow [Fintype M] (a : M) :
    ∃ n, 0 < n ∧ IsIdempotent (a ^ n) := by
  obtain ⟨i, j, hij, hpow⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
  -- Приводим к случаю i < j
  wlog hlt : i < j generalizing i j
  · exact this j i (Ne.symm hij) hpow.symm (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij))
  set p := j - i with hp
  have hp_pos : 0 < p := Nat.sub_pos_of_lt hlt
  have hji : j = i + p := by
    rw [hp, Nat.add_sub_of_le hlt.le]
  have hper : a ^ i = a ^ (i + p) := by rw [← hji]; exact hpow
  refine ⟨p * (i + 1), by positivity, ?_⟩
  -- e = a^(p·(i+1)) идемпотентен
  set N := p * (i + 1) with hN
  have hNi : i ≤ N := by
    have : i < N := by
      rw [hN]; calc i < i + 1 := Nat.lt_succ_self i
        _ ≤ p * (i + 1) := Nat.le_mul_of_pos_left _ hp_pos
    exact le_of_lt this
  show a ^ N * a ^ N = a ^ N
  rw [← pow_add]
  have hNmul : N = (i + 1) * p := by rw [hN]; ring
  have : N + N = N + (i + 1) * p := by rw [← hNmul]
  rw [this]
  exact pow_add_mul_period hper hNi (i + 1)

/-- Всякий непустой конечный моноид содержит идемпотент. -/
theorem exists_idempotent [Fintype M] [Nonempty M] :
    ∃ e : M, IsIdempotent e := by
  obtain ⟨a⟩ := ‹Nonempty M›
  obtain ⟨n, _, hn⟩ := exists_idempotent_pow a
  exact ⟨a ^ n, hn⟩

end UAM_FiniteSemigroup
