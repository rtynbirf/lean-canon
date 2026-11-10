/-
# UAM_Zero — Нулевой элемент (поглощающий элемент)

Самодостаточный файл: двусторонний поглощающий элемент («нуль») моноида.
Все нужные определения из предыдущих UAM-файлов продублированы с пометкой
`-- duplicated from UAM_...`.
-/
import Mathlib

open scoped Classical

namespace UAMZero

universe u

/-! ### §0. Продублированные определения -/

/-- Правый порядок достижимости: `algLe a b := ∃ c, a * c = b`.
    -- duplicated from UAM_Directionality -/
def algLe {M : Type u} [Monoid M] (a b : M) : Prop := ∃ c, a * c = b

/-- Правый поглощающий элемент (End): `∀ x, x * e = e`.
    -- duplicated from UAM_End -/
def IsEnd {M : Type u} [Monoid M] (e : M) : Prop := ∀ x : M, x * e = e

/-- Левый поглощающий элемент: `∀ x, e * x = e`.
    -- duplicated from UAM_End -/
def IsLeftEnd {M : Type u} [Monoid M] (e : M) : Prop := ∀ x : M, e * x = e

/-- Правый стабилизатор элемента `a`.
    -- duplicated from UAM_Loop -/
def rightStabilizer {M : Type u} [Monoid M] (a : M) : Set M := { c | a * c = a }

/-- Левый стабилизатор элемента `a`.
    -- duplicated from UAM_Loop -/
def leftStabilizer {M : Type u} [Monoid M] (a : M) : Set M := { c | c * a = a }

/-- Идемпотентность.
    -- duplicated from UAM_Idempotent -/
def IsIdempotent {M : Type u} [Monoid M] (a : M) : Prop := a * a = a

/-- Обратимость.
    -- duplicated from UAM_Units -/
def IsInvertible {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ b, a * b = 1 ∧ b * a = 1

/-! ### §1. Определение -/

/-- Элемент `z` является двусторонним поглощающим (нулём):
    первый конъюнкт = левый End, второй = правый End. -/
def IsZero {M : Type u} [Monoid M] (z : M) : Prop :=
  (∀ x, z * x = z) ∧ (∀ x, x * z = z)

/-! ### §2. Базовые свойства -/

/-- Нуль является левым End. -/
theorem zero_is_leftEnd {M : Type u} [Monoid M] {z : M} (h : IsZero z) : IsLeftEnd z :=
  h.1

/-- Нуль является (правым) End. -/
theorem zero_is_end {M : Type u} [Monoid M] {z : M} (h : IsZero z) : IsEnd z :=
  h.2

/-- Нуль идемпотентен. -/
theorem zero_is_idempotent {M : Type u} [Monoid M] {z : M} (h : IsZero z) :
    IsIdempotent z :=
  h.2 z

/-- Нуль единствен (если существует). -/
theorem zero_unique {M : Type u} [Monoid M] {z₁ z₂ : M}
    (h₁ : IsZero z₁) (h₂ : IsZero z₂) : z₁ = z₂ := by
  have e1 : z₁ * z₂ = z₁ := h₁.1 z₂
  have e2 : z₁ * z₂ = z₂ := h₂.2 z₁
  rw [← e1, e2]

/-! ### §3. Нуль и стабилизаторы -/

/-- Правый стабилизатор нуля — всё множество. -/
theorem zero_rightStabilizer_eq_univ {M : Type u} [Monoid M] {z : M}
    (h : IsZero z) : rightStabilizer z = Set.univ := by
  ext c
  simp only [rightStabilizer, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact h.1 c

/-- Левый стабилизатор нуля — всё множество. -/
theorem zero_leftStabilizer_eq_univ {M : Type u} [Monoid M] {z : M}
    (h : IsZero z) : leftStabilizer z = Set.univ := by
  ext c
  simp only [leftStabilizer, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact h.2 c

/-- Правый и левый стабилизаторы нуля совпадают (и оба равны `Set.univ`). -/
theorem zero_rightStabilizer_eq_leftStabilizer {M : Type u} [Monoid M] {z : M}
    (h : IsZero z) :
    rightStabilizer z = leftStabilizer z ∧ rightStabilizer z = Set.univ := by
  refine ⟨?_, zero_rightStabilizer_eq_univ h⟩
  rw [zero_rightStabilizer_eq_univ h, zero_leftStabilizer_eq_univ h]

/-! ### §4. Нуль и единицы -/

/-- В нетривиальном случае (`z ≠ 1`) нуль необратим. -/
theorem zero_not_invertible_of_nontrivial {M : Type u} [Monoid M] {z : M}
    (h : IsZero z) (hne : z ≠ 1) : ¬ IsInvertible z := by
  rintro ⟨b, hb, _⟩
  apply hne
  rw [← hb, h.1 b]

/-- Обратимость нуля влечёт `z = 1` (усиление предыдущего). -/
theorem zero_invertible_iff_trivial {M : Type u} [Monoid M] {z : M}
    (h : IsZero z) (hinv : IsInvertible z) : z = 1 := by
  obtain ⟨b, hb, _⟩ := hinv
  rw [← hb, h.1 b]

/-- Если нуль совпадает с единицей, моноид тривиален. -/
theorem zero_eq_one_implies_trivial {M : Type u} [Monoid M] {z : M}
    (h : IsZero z) (hz : z = 1) : ∀ a : M, a = 1 := by
  intro a
  have h2 := h.2 a
  rw [hz, mul_one] at h2
  exact h2

/-! ### §5. Нуль и порядок algLe -/

/-- Локальный левый порядок достижимости. -/
def leftAlgLe {M : Type u} [Monoid M] (a b : M) : Prop := ∃ c, c * a = b

/-- Нуль — потолок порядка `algLe`. -/
theorem zero_is_top_algLe {M : Type u} [Monoid M] {z : M} (h : IsZero z) :
    ∀ a, algLe a z := by
  intro a
  exact ⟨z, h.2 a⟩

/-- Нуль — потолок левого порядка достижимости. -/
theorem zero_is_top_leftAlgLe {M : Type u} [Monoid M] {z : M} (h : IsZero z) :
    ∀ a, leftAlgLe a z := by
  intro a
  exact ⟨z, h.1 a⟩

/-- Единица — дно порядка `algLe`. -/
theorem one_is_bottom_algLe {M : Type u} [Monoid M] : ∀ a : M, algLe 1 a := by
  intro a
  exact ⟨a, one_mul a⟩

/-- Единица и нуль «рамляют» порядок `algLe`. -/
theorem zero_and_one_frame_algLe {M : Type u} [Monoid M] {z : M} (h : IsZero z) :
    ∀ a, algLe 1 a ∧ algLe a z :=
  fun a => ⟨one_is_bottom_algLe a, zero_is_top_algLe h a⟩

/-! ### §6. Нуль в конкретных моноидах -/

/-- В `(ℕ, *)` элемент `0` является нулём. -/
theorem Nat.zero_is_zero : IsZero (0 : ℕ) :=
  ⟨fun x => by simp, fun x => by simp⟩

/-- `(0 : ℕ) ≠ 1`. -/
theorem Nat.zero_ne_one : (0 : ℕ) ≠ 1 := by decide

/-- `0` необратим в `(ℕ, *)`. -/
theorem Nat.zero_not_invertible : ¬ IsInvertible (0 : ℕ) :=
  zero_not_invertible_of_nontrivial Nat.zero_is_zero Nat.zero_ne_one

/-- Если алфавит `α` непуст, то в `FreeMonoid α` нет нулевого элемента. -/
theorem FreeMonoid.no_zero_of_nonempty {α : Type u} [Nonempty α] :
    ¬ ∃ z : FreeMonoid α, IsZero z := by
  rintro ⟨w, hw⟩
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  have hlen : (w * FreeMonoid.of a).length = w.length := by rw [hw.1 _]
  rw [FreeMonoid.length_mul, FreeMonoid.length_of] at hlen
  omega

/-! ### §7. Самодвойственность -/

/-- `IsZero` самодвойствен относительно `MulOpposite`. -/
theorem isZero_iff_op {M : Type u} [Monoid M] {z : M} :
    IsZero z ↔ IsZero (MulOpposite.op z) := by
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · induction x using MulOpposite.rec' with
      | _ y => rw [← MulOpposite.op_mul, hr y]
    · induction x using MulOpposite.rec' with
      | _ y => rw [← MulOpposite.op_mul, hl y]
  · rintro ⟨hl, hr⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have := hr (MulOpposite.op x)
      rw [← MulOpposite.op_mul] at this
      exact MulOpposite.op_injective this
    · have := hl (MulOpposite.op x)
      rw [← MulOpposite.op_mul] at this
      exact MulOpposite.op_injective this

/-! ### §8. Три смысла нуля -/

/-- **Сток**: любой путь, достигший нуля, остаётся в нуле. -/
theorem zero_absorbs_from_above {M : Type u} [Monoid M] {z : M} (h : IsZero z)
    {b : M} (hb : algLe z b) : b = z := by
  obtain ⟨c, hc⟩ := hb
  rw [← hc, h.1 c]

/-- **Поглощение**: правое умножение на нуль — постоянное отображение в нуль. -/
theorem zero_right_mul_const {M : Type u} [Monoid M] {z : M} (h : IsZero z) :
    ∀ x, x * z = z := h.2

/-- **Поглощение** (слева): левое умножение на нуль — постоянное отображение в нуль. -/
theorem zero_left_mul_const {M : Type u} [Monoid M] {z : M} (h : IsZero z) :
    ∀ x, z * x = z := h.1

end UAMZero
