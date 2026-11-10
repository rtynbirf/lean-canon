import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_Regular           -- IsRegular, IsZero, rightStabilizer, leftStabilizer
import RequestProject.Atlas.UAM_Group            -- IsUnit'
import RequestProject.Atlas.UAM_Green             -- R_eq, L_eq, H_eq
import RequestProject.Atlas.UAM_HClass           -- HClass, green_theorem
import RequestProject.Atlas.UAM_Semilattice      -- IsSemilattice, IsCommutative, semilattice_meet

/-!
# UAM — Layer 10: Полностью регулярные элементы (Completely Regular)

Элемент `a` называется **полностью регулярным** (completely regular), если он имеет
внутренний обратный `x`, коммутирующий с ним: `a * x * a = a ∧ a * x = x * a`.
Это эквивалентно тому, что `a` лежит в некоторой подгруппе моноида.

Полная полугруппа — полугруппа, где каждый элемент полностью регулярен.
Устанавливается связь с H-классами идемпотентов (являющимися группами) и
формулируется ключевое свойство теоремы Клиффорда (`clifford_meet`).
-/

namespace UAM_CompletelyRegular
universe u

open UAM_Directionality UAM_Idempotent UAM_Regular UAM_Group UAM_Green UAM_HClass
open UAM_Reachability UAM_Semilattice

variable {M : Type u} [Monoid M]

/-! ### §0. Собственные определения -/

/-- Полностью регулярный элемент: имеет коммутирующий внутренний обратный.
    Эквивалентно: элемент лежит в некоторой подгруппе. -/
def IsCompletelyRegular (a : M) : Prop :=
  ∃ x, a * x * a = a ∧ a * x = x * a

/-- Полная полугруппа: каждый элемент полностью регулярен. -/
def IsCompletelyRegularSemigroup (M : Type u) [Monoid M] : Prop :=
  ∀ a : M, IsCompletelyRegular a

/-! ### §1. Базовые свойства -/

/-- Полностью регулярный элемент регулярен. -/
theorem completely_regular_imp_regular {a : M} (h : IsCompletelyRegular a) :
    UAM_Regular.IsRegular a := by
  obtain ⟨x, h1, _⟩ := h
  exact ⟨x, h1⟩

/-- Обратимый элемент полностью регулярен. -/
theorem unit_completely_regular {a : M} (h : IsUnit' a) : IsCompletelyRegular a := by
  obtain ⟨b, h1, h2⟩ := h
  refine ⟨b, ?_, ?_⟩
  · rw [h1, one_mul]
  · rw [h1, h2]

/-- Идемпотент полностью регулярен. -/
theorem idempotent_completely_regular {a : M} (ha : IsIdempotent a) :
    IsCompletelyRegular a := by
  have ha' : a * a = a := ha
  exact ⟨a, by rw [ha', ha'], rfl⟩

/-- Нуль полностью регулярен. -/
theorem regular_zero_completely_regular {z : M} (h : IsZero z) :
    IsCompletelyRegular z :=
  ⟨z, by rw [h.1 z, h.1 z], rfl⟩

/-- Если `a` полностью регулярен, то `a * x` идемпотентен для коммутирующего обратного `x`. -/
theorem completely_regular_idempotent_product {a : M} (h : IsCompletelyRegular a) :
    ∃ x, IsIdempotent (a * x) := by
  obtain ⟨x, h1, _⟩ := h
  exact ⟨x, regular_left_idempotent h1⟩

/-- Тавтологическая характеризация: регулярность с коммутирующим обратным. -/
theorem completely_regular_of_inverse_commutes {a : M}
    (_ : UAM_Regular.IsRegular a) (h : ∃ x, a * x * a = a ∧ a * x = x * a) :
    IsCompletelyRegular a := h

/-- Если `a` полностью регулярен с обратным `x`, то `a * x` лежит и в правом,
    и в левом стабилизаторе `a`. -/
theorem completely_regular_stabilizer {a x : M}
    (h : a * x * a = a) (hcomm : a * x = x * a) :
    a * x ∈ rightStabilizer a ∧ a * x ∈ leftStabilizer a := by
  constructor
  · show a * (a * x) = a
    rw [hcomm, ← mul_assoc, h]
  · show a * x * a = a
    exact h

/-! ### §2. Связь с H-классами -/

/-- Если `a` полностью регулярен с коммутирующим обратным `x`,
    то `a ∈ HClass (a * x)` (то есть `a` H-эквивалентно идемпотенту `a * x`). -/
theorem completely_regular_mem_H_idempotent {a x : M}
    (h : a * x * a = a) (hcomm : a * x = x * a) :
    a ∈ HClass (a * x) := by
  -- Вспомогательный факт: a = a * (a * x).
  have hkey : a * (a * x) = a := by rw [hcomm, ← mul_assoc, h]
  refine ⟨?_, ?_⟩
  · -- R_eq (a*x) a : reach (a*x) = reach a
    ext b
    simp only [UAM_Reachability.reach, UAM_Directionality.algLe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨x * c, by rw [mul_assoc]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨a * c, by rw [← mul_assoc, h]⟩
  · -- L_eq (a*x) a : reachLeft (a*x) = reachLeft a
    ext b
    simp only [UAM_Reachability.reachLeft, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c * x, by rw [hcomm, mul_assoc]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c * a, by rw [mul_assoc, hkey]⟩

/-- H-класс идемпотента является группой: если `e` идемпотент и `a ∈ HClass e`,
    то `a` полностью регулярен. Обратный строится как `x = e * s`, где `a * s = e`. -/
theorem H_class_group_of_completely_regular {e a : M}
    (he : IsIdempotent e) (ha : a ∈ HClass e) :
    IsCompletelyRegular a := by
  obtain ⟨hea, hae⟩ := UAM_HClass.green_theorem he ha
  -- e достижимо из a справа и слева.
  have hmem : e ∈ UAM_Reachability.reach a := by rw [← ha.1]; exact ⟨1, mul_one e⟩
  have hmemL : e ∈ UAM_Reachability.reachLeft a := by rw [← ha.2]; exact ⟨1, one_mul e⟩
  obtain ⟨s, hs⟩ := hmem
  obtain ⟨t, ht⟩ := hmemL
  -- Ключевое тождество: e * s = t * e.
  have es_te : e * s = t * e := by
    have h1 : t * (a * s) = t * e := by rw [hs]
    rw [← mul_assoc, ht] at h1
    exact h1
  -- Кандидат в обратные: x = e * s, двусторонний обратный к a относительно e.
  have hax : a * (e * s) = e := by rw [← mul_assoc, hae, hs]
  have hxa : (e * s) * a = e := by rw [es_te, mul_assoc, hea, ht]
  refine ⟨e * s, ?_, ?_⟩
  · rw [hax, hea]
  · rw [hax, hxa]

/-- Полная регулярность ↔ H-класс содержит идемпотент. -/
theorem completely_regular_iff_H_has_idempotent (a : M) :
    IsCompletelyRegular a ↔ ∃ e ∈ HClass a, IsIdempotent e := by
  constructor
  · intro h
    obtain ⟨x, h1, h2⟩ := h
    exact ⟨a * x, HClass_symm (completely_regular_mem_H_idempotent h1 h2),
            regular_left_idempotent h1⟩
  · rintro ⟨e, he, he_id⟩
    exact H_class_group_of_completely_regular he_id (HClass_symm he)

/-- Тавтология по определению: полная регулярность есть регулярность с
    коммутирующим внутренним обратным. -/
theorem completely_regular_iff_inverse_commutes (a : M) :
    IsCompletelyRegular a ↔ ∃ x, a * x * a = a ∧ a * x = x * a := Iff.rfl

/-! ### §3. Полная полугруппа и полурешётки -/

/-- Полная полугруппа регулярна. -/
theorem completely_regular_semigroup_regular
    (h : IsCompletelyRegularSemigroup M) : ∀ a : M, UAM_Regular.IsRegular a :=
  fun a => completely_regular_imp_regular (h a)

/- **ЗАМЕЧАНИЕ.** Утверждение «в полной полугруппе идемпотенты коммутируют»
   (`idempotents_commute_in_completely_regular`) в общем случае **ЛОЖНО**.
   Контрпример — прямоугольная связка `L × R` с умножением `(i,j)·(k,l) = (i,l)`:
   каждый элемент идемпотентен и полностью регулярен, но идемпотенты не коммутируют
   (`(i,j)·(k,l) = (i,l)`, тогда как `(k,l)·(i,j) = (k,j)`).
   Поэтому ложная теорема не объявляется, а коммутативность идемпотентов
   принимается как гипотеза в теореме Клиффорда ниже.
-/

/-- **Теорема Клиффорда (ключевое свойство).**
    В полной полугруппе с коммутирующими идемпотентами произведение двух
    идемпотентов `e * f` является их наибольшей нижней границей по естественному
    порядку: `e * f` идемпотентно поглощается `e` и `f`, и любая общая нижняя
    граница `g` подчинена `e * f`. -/
theorem clifford_meet (_ : IsCompletelyRegularSemigroup M)
    (hcomm : ∀ e f : M, IsIdempotent e → IsIdempotent f → e * f = f * e)
    (e f : M) (he : IsIdempotent e) (hf : IsIdempotent f) :
    e * f * e = e * f ∧ e * f * f = e * f ∧
    (∀ g : M, IsIdempotent g → g * e = g → g * f = g → g * (e * f) = g) := by
  have he' : e * e = e := he
  have hf' : f * f = f := hf
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_assoc, hcomm f e hf he, ← mul_assoc, he']
  · rw [mul_assoc, hf']
  · intro g _ hg1 hg2
    rw [← mul_assoc, hg1, hg2]

end UAM_CompletelyRegular