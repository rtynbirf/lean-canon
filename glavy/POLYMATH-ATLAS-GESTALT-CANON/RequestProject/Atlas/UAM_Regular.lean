import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_Group            -- IsUnit'

/-!
# UAM — Layer 5: Регулярные элементы (Regular)

Регулярные элементы — элементы, для которых существует «внутренний обратный»
`x`, такой что `a * x * a = a`. Файл импортирует канонические определения
`algLe`, `IsIdempotent`, `IsUnit'` и не переопределяет их.
-/

namespace UAM_Regular
universe u

open UAM_Directionality UAM_Idempotent UAM_Group

variable {M : Type u} [Monoid M]

/-! ### §0. Собственные определения -/

/-- Двусторонний поглощающий элемент (нуль). -/
def IsZero (z : M) : Prop :=
  (∀ x, z * x = z) ∧ (∀ x, x * z = z)

/-- Регулярный элемент: существует внутренний обратный. -/
def IsRegular (a : M) : Prop :=
  ∃ x, a * x * a = a

/-- Множество регулярных элементов. -/
def regulars : Set M := { a | IsRegular a }

/-- Правый стабилизатор: элементы, фиксирующие `a` при правом умножении. -/
def rightStabilizer (a : M) : Set M := { c | a * c = a }

/-- Левый стабилизатор: элементы, фиксирующие `a` при левом умножении. -/
def leftStabilizer (a : M) : Set M := { c | c * a = a }

/-! ### §1. Базовые включения -/

/-- Обратимый элемент регулярен. -/
theorem unit_is_regular {a : M} (h : IsUnit' a) : IsRegular a := by
  obtain ⟨b, h1, _⟩ := h
  exact ⟨b, by rw [h1, one_mul]⟩

/-- Идемпотент регулярен. -/
theorem idempotent_is_regular {a : M} (ha : IsIdempotent a) : IsRegular a := by
  have ha' : a * a = a := ha
  exact ⟨a, by rw [ha', ha']⟩

/-- Нуль регулярен. -/
theorem zero_is_regular {z : M} (h : IsZero z) : IsRegular z :=
  ⟨z, by rw [h.1 z, h.1 z]⟩

/-- Единица регулярна. -/
theorem one_is_regular : IsRegular (1 : M) :=
  ⟨1, by rw [mul_one, one_mul]⟩

/-! ### §2. Регулярность порождает идемпотенты -/

/-- Если `a * x * a = a`, то `a * x` идемпотентен. -/
theorem regular_left_idempotent {a x : M} (h : a * x * a = a) :
    IsIdempotent (a * x) := by
  show a * x * (a * x) = a * x
  rw [← mul_assoc, h]

/-- Если `a * x * a = a`, то `x * a` идемпотентен. -/
theorem regular_right_idempotent {a x : M} (h : a * x * a = a) :
    IsIdempotent (x * a) := by
  show x * a * (x * a) = x * a
  rw [mul_assoc, ← mul_assoc a x a, h]

/-- Пара идемпотентов, порождённая регулярностью. -/
theorem regular_idempotent_pair {a x : M} (h : a * x * a = a) :
    IsIdempotent (a * x) ∧ IsIdempotent (x * a) :=
  ⟨regular_left_idempotent h, regular_right_idempotent h⟩

/-! ### §3. Регулярность и стабилизаторы -/

/-- Если `a * x * a = a`, то `x * a` лежит в правом стабилизаторе `a`. -/
theorem regular_mem_right_stabilizer {a x : M} (h : a * x * a = a) :
    x * a ∈ rightStabilizer a := by
  show a * (x * a) = a
  rw [← mul_assoc, h]

/-- Если `a * x * a = a`, то `a * x` лежит в левом стабилизаторе `a`. -/
theorem regular_mem_left_stabilizer {a x : M} (h : a * x * a = a) :
    a * x ∈ leftStabilizer a := by
  show a * x * a = a
  exact h

/-! ### §4. Самодвойственность -/

/-- Регулярность самодвойственна относительно противоположного моноида. -/
theorem isRegular_iff_op (a : M) :
    IsRegular a ↔ IsRegular (MulOpposite.op a) := by
  constructor
  · rintro ⟨x, h⟩
    refine ⟨MulOpposite.op x, ?_⟩
    apply MulOpposite.unop_injective
    simpa [mul_assoc] using h
  · rintro ⟨x, h⟩
    refine ⟨MulOpposite.unop x, ?_⟩
    have hu := congrArg MulOpposite.unop h
    simpa [mul_assoc] using hu

end UAM_Regular
