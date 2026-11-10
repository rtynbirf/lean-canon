import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Green

namespace UAMP_Group
universe u

open UAMP_Green UAMP_Reachability

/-- Element a is a unit: ∃ b, a * b = 1 ∧ b * a = 1 -/
def IsUnit' {M : Type u} [Monoid M] (a : M) : Prop := ∃ b, a * b = 1 ∧ b * a = 1

/-- M is a group: every element is a unit -/
def IsGroup (M : Type u) [Monoid M] : Prop := ∀ a : M, IsUnit' a

theorem inv_unique {M : Type u} [Monoid M] {a b c : M}
    (hb : a * b = 1 ∧ b * a = 1) (hc : a * c = 1 ∧ c * a = 1) : b = c := by
  calc b = b * 1 := (mul_one b).symm
    _ = b * (a * c) := by rw [hc.1]
    _ = (b * a) * c := by rw [mul_assoc]
    _ = 1 * c := by rw [hb.2]
    _ = c := one_mul c

theorem cancel_left {M : Type u} [Monoid M] {a b c : M}
    (ha : IsUnit' a) (h : a * b = a * c) : b = c := by
  obtain ⟨x, hx⟩ := ha
  have h2 : (x * a) * b = (x * a) * c := by rw [mul_assoc, mul_assoc, h]
  rw [hx.2, one_mul, one_mul] at h2
  exact h2

theorem cancel_right {M : Type u} [Monoid M] {a b c : M}
    (ha : IsUnit' a) (h : b * a = c * a) : b = c := by
  obtain ⟨x, hx⟩ := ha
  have h2 : b * (a * x) = c * (a * x) := by rw [← mul_assoc, ← mul_assoc, h]
  rw [hx.1, mul_one, mul_one] at h2
  exact h2

theorem isUnit'_one {M : Type u} [Monoid M] : IsUnit' (1 : M) :=
  ⟨1, by rw [mul_one], by rw [mul_one]⟩

theorem isUnit'_mul {M : Type u} [Monoid M] {a b : M}
    (ha : IsUnit' a) (hb : IsUnit' b) : IsUnit' (a * b) := by
  obtain ⟨xa, hxa⟩ := ha
  obtain ⟨xb, hxb⟩ := hb
  refine ⟨xb * xa, ?_, ?_⟩
  · calc a * b * (xb * xa) = a * ((b * xb) * xa) := by simp [mul_assoc]
      _ = a * xa := by rw [hxb.1, one_mul]
      _ = 1 := hxa.1
  · calc xb * xa * (a * b) = xb * ((xa * a) * b) := by simp [mul_assoc]
      _ = xb * b := by rw [hxa.2, one_mul]
      _ = 1 := hxb.2

/-- Обратный к обратимому элементу сам обратим.
(Архивная версия ссылалась на несуществующее поле `IsUnit'.exists`.) -/
theorem isUnit'_inv {M : Type u} [Monoid M] {a b : M}
    (hb : a * b = 1 ∧ b * a = 1) : IsUnit' b := ⟨a, hb.2, hb.1⟩

/- Архивная формулировка

theorem algLe_trivial (h : algLe a b) (ha : IsUnit' a) : algLe b a

неверна: при `a = 1` посылка `algLe 1 b` выполнена для любого `b`, а заключение
`algLe b 1` означало бы обратимость `b` (в свободном моноиде это не так).
Верное утверждение: обратимый элемент достижим из любого элемента только тогда,
когда он сам делится; ниже доказано, что множества достижимости обратимого
элемента совпадают со всем моноидом. -/

theorem reach_unit {M : Type u} [Monoid M] {a : M} (ha : IsUnit' a) : reach a = Set.univ := by
  obtain ⟨x, hx⟩ := ha
  apply Set.eq_univ_of_forall
  intro y
  exact ⟨x * y, by rw [← mul_assoc, hx.1, one_mul]⟩

theorem reachLeft_unit {M : Type u} [Monoid M] {a : M} (ha : IsUnit' a) :
    reachLeft a = Set.univ := by
  obtain ⟨x, hx⟩ := ha
  apply Set.eq_univ_of_forall
  intro y
  exact ⟨y * x, by rw [mul_assoc, hx.2, mul_one]⟩

/-- Любые два обратимых элемента R-эквивалентны.
(Архивная версия `R_eq_trivial` утверждала `R_eq a b` для произвольного `b`, что неверно.) -/
theorem R_eq_of_units {M : Type u} [Monoid M] {a b : M} (ha : IsUnit' a) (hb : IsUnit' b) :
    R_eq a b := by rw [R_eq, reach_unit ha, reach_unit hb]

theorem L_eq_of_units {M : Type u} [Monoid M] {a b : M} (ha : IsUnit' a) (hb : IsUnit' b) :
    L_eq a b := by rw [L_eq, reachLeft_unit ha, reachLeft_unit hb]

theorem H_eq_of_units {M : Type u} [Monoid M] {a b : M} (ha : IsUnit' a) (hb : IsUnit' b) :
    H_eq a b := ⟨R_eq_of_units ha hb, L_eq_of_units ha hb⟩

theorem isGroup_iff_reach_contains_one {M : Type u} [Monoid M] :
    IsGroup M ↔ ∀ a : M, (1 : M) ∈ reach a := by
  constructor
  · intro h a
    obtain ⟨b, hb⟩ := h a
    exact ⟨b, hb.1⟩
  · intro h a
    obtain ⟨b, hb⟩ := h a
    refine ⟨b, hb, ?_⟩
    obtain ⟨c, hc⟩ := h b
    have hac : a = c := by
      calc a = a * 1 := (mul_one a).symm
        _ = a * (b * c) := by rw [hc]
        _ = (a * b) * c := by rw [mul_assoc]
        _ = 1 * c := by rw [hb]
        _ = c := one_mul c
    rw [hac]
    exact hc

end UAMP_Group
