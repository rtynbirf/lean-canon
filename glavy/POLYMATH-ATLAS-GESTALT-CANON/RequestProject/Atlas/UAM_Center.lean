import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Group            -- IsUnit'
import RequestProject.Atlas.UAM_Submonoid        -- Submonoid

/-!
# UAM — Центр и централизаторы моноида (Center)

Центральные элементы моноида — те, что коммутируют со всеми элементами.
Множество центральных элементов образует подмоноид — центр `center M`.
Более общо, для произвольного подмножества `s` определяется его
централизатор `centralizer s` — подмоноид элементов, коммутирующих со
всеми элементами `s`. Центр — это централизатор всего носителя.

Файл — новый листовой слой: он опирается на канонические определения
`UAM_Submonoid.Submonoid`, `UAM_Idempotent.IsIdempotent`,
`UAM_Group.IsUnit'` и не переопределяет их. Тип `Submonoid` всюду
записан полностью как `UAM_Submonoid.Submonoid`, чтобы избежать
неоднозначности с `_root_.Submonoid` из Mathlib.
-/

namespace UAM_Center
universe u
variable {M : Type u} [Monoid M]

/-- Элемент `a` центральный, если он коммутирует со всеми элементами. -/
def IsCentral (a : M) : Prop := ∀ x : M, a * x = x * a

/-! ### §1. Центр как подмоноид -/

/-- Центр моноида `M` — подмоноид его центральных элементов. -/
def center (M : Type u) [Monoid M] : UAM_Submonoid.Submonoid M where
  carrier := {a | IsCentral a}
  one_mem := by intro x; rw [one_mul, mul_one]
  mul_mem := by
    intro a b ha hb x
    calc a * b * x = a * (b * x) := by rw [mul_assoc]
      _ = a * (x * b) := by rw [hb x]
      _ = a * x * b := by rw [mul_assoc]
      _ = x * a * b := by rw [ha x]
      _ = x * (a * b) := by rw [mul_assoc]

/-- Централизатор подмножества `s` — подмоноид элементов, коммутирующих
    со всеми элементами `s`. -/
def centralizer (s : Set M) : UAM_Submonoid.Submonoid M where
  carrier := {a | ∀ x ∈ s, a * x = x * a}
  one_mem := by intro x _; rw [one_mul, mul_one]
  mul_mem := by
    intro a b ha hb x hx
    calc a * b * x = a * (b * x) := by rw [mul_assoc]
      _ = a * (x * b) := by rw [hb x hx]
      _ = a * x * b := by rw [mul_assoc]
      _ = x * a * b := by rw [ha x hx]
      _ = x * (a * b) := by rw [mul_assoc]

/-! ### §2. Базовые свойства -/

theorem mem_center_iff {a : M} :
    a ∈ (center M).carrier ↔ ∀ x : M, a * x = x * a :=
  Iff.rfl

theorem one_central : IsCentral (1 : M) := by
  intro x; rw [one_mul, mul_one]

theorem mul_central {a b : M} (ha : IsCentral a) (hb : IsCentral b) :
    IsCentral (a * b) :=
  (center M).mul_mem a b ha hb

/-- Центральный элемент коммутирует с любым. -/
theorem central_comm {a : M} (ha : IsCentral a) (b : M) : a * b = b * a := ha b

/-- Два центральных элемента коммутируют между собой. -/
theorem center_mul_comm {a b : M} (ha : IsCentral a) (_hb : IsCentral b) :
    a * b = b * a := ha b

/-- Степени центрального элемента центральны. -/
theorem pow_central {a : M} (ha : IsCentral a) (n : ℕ) : IsCentral (a ^ n) := by
  induction n with
  | zero => simpa using one_central
  | succ k ih => simpa [pow_succ] using mul_central ih ha

/-! ### §3. Центр и централизаторы -/

/-- Центр — это централизатор всего носителя. -/
theorem center_eq_centralizer_univ :
    (center M).carrier = (centralizer (Set.univ : Set M)).carrier := by
  ext a
  constructor
  · intro ha x _; exact ha x
  · intro ha x; exact ha x (Set.mem_univ x)

/-- Централизатор антимонотонен: большее множество имеет меньший
    централизатор. -/
theorem centralizer_antitone {s t : Set M} (h : s ⊆ t) :
    (centralizer t).carrier ⊆ (centralizer s).carrier := by
  intro a ha x hx
  exact ha x (h hx)

/-- Центр содержится в централизаторе любого подмножества. -/
theorem center_subset_centralizer (s : Set M) :
    (center M).carrier ⊆ (centralizer s).carrier := by
  intro a ha x _; exact ha x

/-! ### §4. Взаимодействие с другими понятиями -/

/-- В коммутативном моноиде каждый элемент центральный. -/
theorem central_of_comm (hcomm : ∀ x y : M, x * y = y * x) (a : M) :
    IsCentral a := fun x => hcomm a x

/-- В коммутативном моноиде центр совпадает со всем моноидом. -/
theorem center_eq_top_of_comm (hcomm : ∀ x y : M, x * y = y * x) :
    (center M).carrier = (Set.univ : Set M) := by
  ext a
  simp only [Set.mem_univ, iff_true]
  exact central_of_comm hcomm a

/-- Обратный к центральному обратимому элементу тоже центральный. -/
theorem isUnit'_inv_central {a b : M} (ha : IsCentral a)
    (hab : a * b = 1 ∧ b * a = 1) : IsCentral b := by
  intro x
  have h1 : b * x * a = x := by
    rw [mul_assoc, ← ha x, ← mul_assoc, hab.2, one_mul]
  calc b * x = b * x * a * b := by rw [mul_assoc (b * x) a b, hab.1, mul_one]
    _ = x * b := by rw [h1]

end UAM_Center
