import Mathlib
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_Inverse          -- idempotents_commute, IsInverseSemigroup

/-!
# UAM — Layer 8: Полурешётки (Semilattice)

Полурешётка (в алгебраическом смысле) — идемпотентный коммутативный моноид.
Устанавливается связь с обратными полугруппами (множество идемпотентов
обратной полугруппы коммутирует) и естественный порядок полурешётки.
-/

namespace UAM_Semilattice
universe u

open UAM_Idempotent UAM_Inverse

variable {M : Type u} [Monoid M]

/-- Коммутативный моноид: умножение коммутативно. -/
def IsCommutative (M : Type u) [Monoid M] : Prop :=
  ∀ a b : M, a * b = b * a

/-- Полурешётка: идемпотентный коммутативный моноид. -/
def IsSemilattice (M : Type u) [Monoid M] : Prop :=
  IsCommutative M ∧ (∀ a : M, IsIdempotent a)

/-! ### §1. Базовые свойства -/

/-- В коммутативном моноиде единица нейтральна (тривиально, но через `IsCommutative`). -/
theorem commutative_one (h : IsCommutative M) (a : M) : 1 * a = a := by
  rw [h 1 a, mul_one]

/-- В коммутативном моноиде идемпотент поглощает свои повторные множители. -/
theorem commutative_idempotent_absorb : IsCommutative M → ∀ {a : M},
    IsIdempotent a → ∀ b : M, a * (a * b) = a * b := by
  intro _ a he b
  have ha : a * a = a := he
  rw [← mul_assoc, ha]

/-- В полурешётке каждый элемент идемпотентен. -/
theorem semilattice_idempotent (h : IsSemilattice M) : ∀ a : M, IsIdempotent a := h.2

/-- Полурешётка коммутативна. -/
theorem semilattice_commutative (h : IsSemilattice M) : IsCommutative M := h.1

/-- В полурешётке произведение любых двух элементов идемпотентно. -/
theorem semilattice_mul_idempotent (hS : IsSemilattice M) (a b : M) :
    a * b * (a * b) = a * b :=
  hS.2 (a * b)

/-! ### §2. Связь с обратными полугруппами -/

/-- Идемпотенты обратной полугруппы коммутируют. -/
theorem inverse_semigroup_idempotents_commutative (hS : IsInverseSemigroup M)
    {e f : M} (he : IsIdempotent e) (hf : IsIdempotent f) : e * f = f * e :=
  idempotents_commute hS e f he hf

/-- Множество идемпотентов обратной полугруппы обладает свойствами полурешётки:
    произведение идемпотентов идемпотентно и коммутирует. -/
theorem inverse_semigroup_idempotents_semilattice (hS : IsInverseSemigroup M)
    {e f : M} (he : IsIdempotent e) (hf : IsIdempotent f) :
    IsIdempotent (e * f) ∧ e * f = f * e :=
  ⟨prod_idempotent hS e f he hf, idempotents_commute hS e f he hf⟩

/-- В полурешётке `a * b` — наибольшая нижняя граница `a` и `b`
    относительно естественного порядка `c ≤ a ↔ c * a = c`. -/
theorem semilattice_meet (hS : IsSemilattice M) (a b : M) :
    a * b * a = a * b ∧ a * b * b = a * b ∧
    (∀ c, c * a = c → c * b = c → c * (a * b) = c) := by
  have ha : a * a = a := hS.2 a
  have hb : b * b = b := hS.2 b
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_assoc, hS.1 b a, ← mul_assoc, ha]
  · rw [mul_assoc, hb]
  · intro c hc1 hc2
    rw [← mul_assoc, hc1, hc2]

/-! ### §3. Примеры -/

/-- Булевы значения с конъюнкцией образуют полурешётку. -/
theorem bool_semilattice : IsSemilattice Bool :=
  ⟨fun a b => by cases a <;> cases b <;> rfl, fun a => by cases a <;> rfl⟩

/-- Тривиальный моноид `Unit` — полурешётка. -/
theorem unit_semilattice : IsSemilattice Unit :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

/-- В полурешётке `a ^ n = a` для любого `n ≥ 1`. -/
theorem semilattice_power_idempotent (hS : IsSemilattice M) (a : M) (n : ℕ)
    (hn : 1 ≤ n) : a ^ n = a := by
  have ha : a * a = a := hS.2 a
  induction n with
  | zero => exact (Nat.not_succ_le_zero 0 hn).elim
  | succ n ih =>
    cases n with
    | zero => rw [pow_one]
    | succ n => rw [pow_succ, ih (Nat.succ_le_succ (Nat.zero_le n)), ha]

end UAM_Semilattice
