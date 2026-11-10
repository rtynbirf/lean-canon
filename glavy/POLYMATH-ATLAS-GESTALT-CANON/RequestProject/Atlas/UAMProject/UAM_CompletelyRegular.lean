import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Regular
import RequestProject.Atlas.UAMProject.UAM_Group
import RequestProject.Atlas.UAMProject.UAM_Green
import RequestProject.Atlas.UAMProject.UAM_HClass
import RequestProject.Atlas.UAMProject.UAM_Submonoid
import RequestProject.Atlas.UAMProject.UAM_Semilattice

namespace UAMP_CompletelyRegular
universe u

open UAMP_Green UAMP_HClass UAMP_Idempotent UAMP_Reachability

variable {M : Type u} [Monoid M]

/-- Element a is completely regular: ∃ x, a*x*a = a ∧ a*x = x*a -/
def IsCompletelyRegular (a : M) : Prop :=
  ∃ x, a * x * a = a ∧ a * x = x * a

/-- Semigroup where every element is completely regular -/
def IsCompletelyRegularSemigroup (M : Type u) [Monoid M] : Prop :=
  ∀ a : M, IsCompletelyRegular a

/-- a is completely regular iff its H-class contains an idempotent.
(В архиве доказательство отсутствовало.) -/
theorem completely_regular_iff_H_has_idempotent (a : M) :
    IsCompletelyRegular a ↔ ∃ e, IsIdempotent e ∧ e ∈ HClass a := by
  constructor
  · rintro ⟨x, hax, hcomm⟩
    refine ⟨a * x, ?_, ?_, ?_⟩
    · show a * x * (a * x) = a * x
      calc a * x * (a * x) = (a * x * a) * x := by simp only [mul_assoc]
        _ = a * x := by rw [hax]
    · -- R_eq a (a * x)
      refine R_eq_of_mem_reach ⟨x, rfl⟩ ⟨a, ?_⟩
      show a * x * a = a
      exact hax
    · -- L_eq a (a * x)
      refine L_eq_of_mem_reachLeft ⟨x, ?_⟩ ⟨a, ?_⟩
      · show x * a = a * x
        exact hcomm.symm
      · show a * (a * x) = a
        rw [hcomm, ← mul_assoc]
        exact hax
  · rintro ⟨e, he, hR, hL⟩
    -- e H-эквивалентен a, e идемпотент: e — двусторонняя единица на H-классе
    have hHea : H_eq e a := ⟨R_eq.symm hR, L_eq.symm hL⟩
    have hea : e * a = a := UAMP_Submonoid.idem_mul_left he hHea
    have hae : a * e = a := UAMP_Submonoid.idem_mul_right he hHea
    -- e достижим из a справа и слева
    have hy : e ∈ reach a := by rw [hR]; exact mem_reach_self e
    have hz : e ∈ reachLeft a := by rw [hL]; exact mem_reachLeft_self e
    obtain ⟨y, hy⟩ := hy
    obtain ⟨z, hz⟩ := hz
    refine ⟨e * y, ?_, ?_⟩
    · -- a * (e * y) * a = a
      have h1 : a * (e * y) = e := by rw [← mul_assoc, hae, hy]
      rw [h1, hea]
    · -- a * (e * y) = (e * y) * a, оба равны e
      have h1 : a * (e * y) = e := by rw [← mul_assoc, hae, hy]
      have h2 : e * y * a = e := by
        calc e * y * a = (z * a) * y * a := by rw [hz]
          _ = z * (a * y) * a := by simp only [mul_assoc]
          _ = z * (e * a) := by rw [hy, mul_assoc]
          _ = z * a := by rw [hea]
          _ = e := hz
      rw [h1, h2]

/-- Clifford: в вполне регулярном моноиде у каждого элемента есть идемпотент,
являющийся для него двусторонней единицей.
(Архивная версия дополнительно требовала коммутирования идемпотентов; это
предположение оказалось излишним.) -/
theorem clifford_meet (hCR : IsCompletelyRegularSemigroup M) :
    ∀ a : M, ∃ e, IsIdempotent e ∧ a * e = a ∧ e * a = a := by
  intro a
  obtain ⟨x, hax, hcomm⟩ := hCR a
  refine ⟨a * x, ?_, ?_, ?_⟩
  · show a * x * (a * x) = a * x
    calc a * x * (a * x) = (a * x * a) * x := by simp only [mul_assoc]
      _ = a * x := by rw [hax]
  · calc a * (a * x) = a * (x * a) := by rw [hcomm]
      _ = a * x * a := by simp only [mul_assoc]
      _ = a := hax
  · exact hax

/- Архивный комментарий: утверждение «идемпотенты коммутируют во вполне
регулярной полугруппе» ложно (контрпример — прямоугольная связка). -/

end UAMP_CompletelyRegular
