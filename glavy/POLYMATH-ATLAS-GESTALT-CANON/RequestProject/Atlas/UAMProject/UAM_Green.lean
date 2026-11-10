import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Reachability

namespace UAMP_Green
universe u

open UAMP_Reachability

/-- Green's R relation: reach a = reach b -/
def R_eq {M : Type u} [Monoid M] (a b : M) : Prop := reach a = reach b

/-- Green's L relation: reachLeft a = reachLeft b -/
def L_eq {M : Type u} [Monoid M] (a b : M) : Prop := reachLeft a = reachLeft b

/-- Green's H relation: R ∧ L -/
def H_eq {M : Type u} [Monoid M] (a b : M) : Prop := R_eq a b ∧ L_eq a b

-- R equivalence
theorem R_eq.refl {M : Type u} [Monoid M] (a : M) : R_eq a a := rfl

theorem R_eq.symm {M : Type u} [Monoid M] {a b : M} (h : R_eq a b) : R_eq b a := Eq.symm h

theorem R_eq.trans {M : Type u} [Monoid M] {a b c : M} (hab : R_eq a b) (hbc : R_eq b c) :
    R_eq a c := Eq.trans hab hbc

-- L equivalence
theorem L_eq.refl {M : Type u} [Monoid M] (a : M) : L_eq a a := rfl

theorem L_eq.symm {M : Type u} [Monoid M] {a b : M} (h : L_eq a b) : L_eq b a := Eq.symm h

theorem L_eq.trans {M : Type u} [Monoid M] {a b c : M} (hab : L_eq a b) (hbc : L_eq b c) :
    L_eq a c := Eq.trans hab hbc

-- H equivalence
theorem H_eq.refl {M : Type u} [Monoid M] (a : M) : H_eq a a := ⟨R_eq.refl _, L_eq.refl _⟩

theorem H_eq.symm {M : Type u} [Monoid M] {a b : M} (h : H_eq a b) : H_eq b a :=
  ⟨R_eq.symm h.1, L_eq.symm h.2⟩

theorem H_eq.trans {M : Type u} [Monoid M] {a b c : M} (hab : H_eq a b) (hbc : H_eq b c) :
    H_eq a c := ⟨R_eq.trans hab.1 hbc.1, L_eq.trans hab.2 hbc.2⟩

-- Multiplicative properties

/- Исходная формулировка из архива:

theorem R_eq_mul_right {M : Type u} [Monoid M] (a b : M) : R_eq a (a * b)

Она неверна: `R_eq a (a*b)` означает `a * M = a * b * M`, а включение `a * M ⊆ a * b * M`
в общем случае не выполняется (например, в свободном моноиде `a ∉ (a*b)*M`).
Верным является лишь одно включение, которое и доказано ниже. -/
theorem reach_mul_right_subset {M : Type u} [Monoid M] (a b : M) : reach (a * b) ⊆ reach a := by
  rintro c ⟨d, hd⟩
  exact ⟨b * d, by rw [← mul_assoc]; exact hd⟩

/- Аналогично, архивная формулировка `L_eq_mul_left : L_eq a (b * a)` неверна;
доказано верное включение. -/
theorem reachLeft_mul_left_subset {M : Type u} [Monoid M] (a b : M) :
    reachLeft (b * a) ⊆ reachLeft a := by
  rintro c ⟨d, hd⟩
  exact ⟨d * b, by rw [mul_assoc]; exact hd⟩

/- Архивные формулировки `H_eq.mul_right : H_eq a b → H_eq (a*c) (b*c)` и
`H_eq.mul_left : H_eq a b → H_eq (c*a) (c*b)` в общем случае неверны:
отношение Грина R является левой конгруэнцией, но не правой, а L — правой, но не левой.
(Контрпример: в моноиде всех преобразований трёхэлементного множества существуют
R-эквивалентные a, b и такое c, что a*c и b*c уже не R-эквивалентны.)
Ниже доказаны верные версии. -/

/-- R — левая конгруэнция: `a R b → (c*a) R (c*b)`. -/
theorem R_eq.mul_left {M : Type u} [Monoid M] {a b : M} (h : R_eq a b) (c : M) :
    R_eq (c * a) (c * b) := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨d, hd⟩
    have : a * d ∈ reach a := ⟨d, rfl⟩
    rw [h] at this
    obtain ⟨e, he⟩ := this
    exact ⟨e, by rw [mul_assoc, he, ← mul_assoc]; exact hd⟩
  · rintro x ⟨d, hd⟩
    have : b * d ∈ reach b := ⟨d, rfl⟩
    rw [← h] at this
    obtain ⟨e, he⟩ := this
    exact ⟨e, by rw [mul_assoc, he, ← mul_assoc]; exact hd⟩

/-- L — правая конгруэнция: `a L b → (a*c) L (b*c)`. -/
theorem L_eq.mul_right {M : Type u} [Monoid M] {a b : M} (h : L_eq a b) (c : M) :
    L_eq (a * c) (b * c) := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨d, hd⟩
    have : d * a ∈ reachLeft a := ⟨d, rfl⟩
    rw [h] at this
    obtain ⟨e, he⟩ := this
    exact ⟨e, by rw [← mul_assoc, he, mul_assoc]; exact hd⟩
  · rintro x ⟨d, hd⟩
    have : d * b ∈ reachLeft b := ⟨d, rfl⟩
    rw [← h] at this
    obtain ⟨e, he⟩ := this
    exact ⟨e, by rw [← mul_assoc, he, mul_assoc]; exact hd⟩

theorem R_eq_of_mem_reach {M : Type u} [Monoid M] {a b : M}
    (h₁ : b ∈ reach a) (h₂ : a ∈ reach b) : R_eq a b :=
  Set.Subset.antisymm (reach_mono h₂) (reach_mono h₁)

theorem L_eq_of_mem_reachLeft {M : Type u} [Monoid M] {a b : M}
    (h₁ : b ∈ reachLeft a) (h₂ : a ∈ reachLeft b) : L_eq a b :=
  Set.Subset.antisymm (reach_left_mono h₂) (reach_left_mono h₁)

end UAMP_Green
