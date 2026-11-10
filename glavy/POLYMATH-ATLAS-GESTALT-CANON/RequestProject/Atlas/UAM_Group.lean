import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Green            -- R_eq, L_eq, H_eq (и reach, reachLeft транзитивно)

/-!
# UAM — Layer 3: Группы (Group)

Обратимые элементы и группы как моноиды, где всё обратимо.
Файл импортирует канонические определения `algLe`, `reach`, `reachLeft`,
`R_eq`, `L_eq`, `H_eq` и не переопределяет их.
-/

namespace UAM_Group
universe u

open UAM_Directionality UAM_Reachability UAM_Green

variable {M : Type u} [Monoid M]

/-- Обратимый элемент: имеет двусторонний обратный. -/
def IsUnit' (a : M) : Prop := ∃ b : M, a * b = 1 ∧ b * a = 1

/-- Группа: моноид, где каждый элемент обратим. -/
def IsGroup (M : Type u) [Monoid M] : Prop := ∀ a : M, IsUnit' a

/-! ### §1. Базовые свойства обратимых элементов -/

/-- Единственность обратного элемента. -/
theorem inv_unique {a b c : M} (h1 : a * b = 1 ∧ b * a = 1) (h2 : a * c = 1 ∧ c * a = 1) :
    b = c := by
  calc b = 1 * b := by rw [one_mul]
    _ = c * a * b := by rw [h2.2]
    _ = c * (a * b) := by rw [mul_assoc]
    _ = c * 1 := by rw [h1.1]
    _ = c := by rw [mul_one]

/-- Обратный к обратному: если `b` обратен к `a`, то `b` также обратим. -/
theorem inv_inv {a b : M} (h : a * b = 1 ∧ b * a = 1) : IsUnit' b := ⟨a, h.2, h.1⟩

/-- Обратимость произведения. -/
theorem inv_mul {a a' b b' : M} (ha : a * a' = 1 ∧ a' * a = 1) (hb : b * b' = 1 ∧ b' * b = 1) :
    IsUnit' (a * b) := by
  refine ⟨b' * a', ?_, ?_⟩
  · rw [← mul_assoc, mul_assoc a b b', hb.1, mul_one, ha.1]
  · rw [← mul_assoc, mul_assoc b' a' a, ha.2, mul_one, hb.2]

/-- Единица обратима. -/
theorem one_isUnit : IsUnit' (1 : M) := ⟨1, by simp⟩

/-! ### §2. Свойства групп -/

/-- Левое сокращение в группе. -/
theorem cancel_left (hG : IsGroup M) {a b c : M} (h : a * b = a * c) : b = c := by
  obtain ⟨a', _, ha2⟩ := hG a
  calc b = a' * a * b := by rw [ha2, one_mul]
    _ = a' * (a * b) := by rw [mul_assoc]
    _ = a' * (a * c) := by rw [h]
    _ = a' * a * c := by rw [mul_assoc]
    _ = c := by rw [ha2, one_mul]

/-- Правое сокращение в группе. -/
theorem cancel_right (hG : IsGroup M) {a b c : M} (h : b * a = c * a) : b = c := by
  obtain ⟨a', ha1, _⟩ := hG a
  calc b = b * (a * a') := by rw [ha1, mul_one]
    _ = b * a * a' := by rw [mul_assoc]
    _ = c * a * a' := by rw [h]
    _ = c * (a * a') := by rw [mul_assoc]
    _ = c := by rw [ha1, mul_one]

/-! ### §3. UAM в группе: `algLe` тривиальна -/

/-- В группе любой элемент достижим из любого. -/
theorem algLe_trivial (hG : IsGroup M) (a b : M) : algLe a b := by
  obtain ⟨a', ha1, _⟩ := hG a
  exact ⟨a' * b, by rw [← mul_assoc, ha1, one_mul]⟩

/-! ### §4. UAM в группе: отношения Грина коллапсируют -/

/-- В группе множество правых кратных — весь моноид. -/
theorem reach_eq_univ (hG : IsGroup M) (a : M) : reach a = Set.univ := by
  apply Set.eq_univ_of_forall
  intro b
  obtain ⟨a', ha1, _⟩ := hG a
  exact ⟨a' * b, by rw [← mul_assoc, ha1, one_mul]⟩

/-- В группе множество левых кратных — весь моноид. -/
theorem reachLeft_eq_univ (hG : IsGroup M) (a : M) : reachLeft a = Set.univ := by
  apply Set.eq_univ_of_forall
  intro b
  obtain ⟨a', _, ha2⟩ := hG a
  exact ⟨b * a', by rw [mul_assoc, ha2, mul_one]⟩

/-- В группе отношение R тривиально. -/
theorem R_eq_trivial (hG : IsGroup M) (a b : M) : R_eq a b :=
  (reach_eq_univ hG a).trans (reach_eq_univ hG b).symm

/-- В группе отношение L тривиально. -/
theorem L_eq_trivial (hG : IsGroup M) (a b : M) : L_eq a b :=
  (reachLeft_eq_univ hG a).trans (reachLeft_eq_univ hG b).symm

/-- В группе отношение H тривиально. -/
theorem H_eq_trivial (hG : IsGroup M) (a b : M) : H_eq a b :=
  ⟨R_eq_trivial hG a b, L_eq_trivial hG a b⟩

/-! ### §5. Обратное соответствие -/

/-- Моноид является группой тогда и только тогда, когда единица достижима
    из каждого элемента и справа, и слева. -/
theorem isGroup_iff_reach_contains_one :
    IsGroup M ↔ (∀ a : M, (1 : M) ∈ reach a) ∧ (∀ a : M, (1 : M) ∈ reachLeft a) := by
  constructor
  · intro hG
    refine ⟨?_, ?_⟩
    · intro a
      obtain ⟨a', ha1, _⟩ := hG a
      exact ⟨a', ha1⟩
    · intro a
      obtain ⟨a', _, ha2⟩ := hG a
      exact ⟨a', ha2⟩
  · rintro ⟨hr, hl⟩ a
    obtain ⟨c, hc⟩ := hr a
    obtain ⟨d, hd⟩ := hl a
    have hcd : d = c := by
      calc d = d * 1 := by rw [mul_one]
        _ = d * (a * c) := by rw [hc]
        _ = d * a * c := by rw [mul_assoc]
        _ = 1 * c := by rw [hd]
        _ = c := by rw [one_mul]
    exact ⟨c, hc, by rw [← hcd]; exact hd⟩

end UAM_Group
