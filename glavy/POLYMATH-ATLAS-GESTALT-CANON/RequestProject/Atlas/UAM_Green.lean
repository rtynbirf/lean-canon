import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Reachability   -- reach, reachLeft
import RequestProject.Atlas.UAM_PrincipalIdeals -- principalIdeal

/-!
# UAM — Layer 2: Отношения Грина (Green's relations)

Канонические определения отношений Грина `R_eq`, `L_eq`, `H_eq`
через равенство множеств достижимости.
-/

namespace UAM_Green
universe u

open UAM_Directionality UAM_Reachability UAM_Ideal

/-- Отношение Грина R: одинаковое множество правых кратных. -/
def R_eq {M : Type u} [Monoid M] (a b : M) : Prop := reach a = reach b

/-- Отношение Грина L: одинаковое множество левых кратных. -/
def L_eq {M : Type u} [Monoid M] (a b : M) : Prop := reachLeft a = reachLeft b

/-- Отношение Грина H: пересечение R и L. -/
def H_eq {M : Type u} [Monoid M] (a b : M) : Prop := R_eq a b ∧ L_eq a b

/-- Транзитивное замыкание отношения. -/
abbrev TransitiveClosure {α : Sort u} (r : α → α → Prop) : α → α → Prop :=
  Relation.TransGen r

/-- Отношение Грина D: транзитивное замыкание объединения R и L. -/
def D_eq {M : Type u} [Monoid M] (a b : M) : Prop :=
  TransitiveClosure (fun x y => R_eq x y ∨ L_eq x y) a b

/-- Каждая R-связь является D-связью. -/
theorem R_subset_D {M : Type u} [Monoid M] {a b : M}
    (h : R_eq a b) : D_eq a b := by
  exact Relation.TransGen.single (Or.inl h)

/-- Каждая L-связь является D-связью. -/
theorem L_subset_D {M : Type u} [Monoid M] {a b : M}
    (h : L_eq a b) : D_eq a b := by
  exact Relation.TransGen.single (Or.inr h)

/-- Каждая H-связь является D-связью. -/
theorem H_subset_D {M : Type u} [Monoid M] {a b : M}
    (h : H_eq a b) : D_eq a b := by
  exact R_subset_D h.1

/-
Отношение D рефлексивно.
-/
theorem D_eq_refl {M : Type u} [Monoid M] (a : M) : D_eq a a := by
  exact Relation.TransGen.single ( Or.inl rfl )

/-
Отношение D симметрично.
-/
theorem D_eq_symm {M : Type u} [Monoid M] {a b : M} (h : D_eq a b) : D_eq b a := by
  have base_symm : ∀ {x y : M}, R_eq x y ∨ L_eq x y → R_eq y x ∨ L_eq y x := by
    intro x y hxy
    cases hxy with
    | inl hR => exact Or.inl hR.symm
    | inr hL => exact Or.inr hL.symm
  induction h with
  | single hxy => exact Relation.TransGen.single (base_symm hxy)
  | tail hab hbc ih =>
      exact Relation.TransGen.trans
        (r := fun x y : M => R_eq x y ∨ L_eq x y)
        (Relation.TransGen.single (base_symm hbc)) ih

/-
Отношение D транзитивно.
-/
theorem D_eq_trans {M : Type u} [Monoid M] {a b c : M}
    (hab : D_eq a b) (hbc : D_eq b c) : D_eq a c := by
  convert Relation.TransGen.trans hab hbc using 1

/-- Отношение Грина J: равенство главных двусторонних идеалов. -/
def J_eq {M : Type u} [Monoid M] (a b : M) : Prop :=
  principalIdeal a = principalIdeal b

/-
Отношение J рефлексивно.
-/
theorem J_eq_refl {M : Type u} [Monoid M] (a : M) : J_eq a a := by
  rfl

/-
Отношение J симметрично.
-/
theorem J_eq_symm {M : Type u} [Monoid M] {a b : M} (h : J_eq a b) : J_eq b a := by
  exact h.symm

/-
Отношение J транзитивно.
-/
theorem J_eq_trans {M : Type u} [Monoid M] {a b c : M}
    (hab : J_eq a b) (hbc : J_eq b c) : J_eq a c := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    rw [← hbc, ← hab]
    exact hx
  · intro x hx
    rw [hab, hbc]
    exact hx

/-
R-эквивалентные элементы J-эквивалентны.
-/
theorem R_eq_implies_J_eq {M : Type u} [Monoid M] {a b : M}
    (h : R_eq a b) : J_eq a b := by
  have hb : b ∈ reach b := ⟨1, mul_one b⟩
  have ha : a ∈ reach a := ⟨1, mul_one a⟩
  have hb_from_a : b ∈ reach a := by rw [h]; exact hb
  have ha_from_b : a ∈ reach b := by rw [← h]; exact ha
  obtain ⟨p, hp⟩ := hb_from_a
  obtain ⟨q, hq⟩ := ha_from_b
  apply Set.eq_of_subset_of_subset
  · rintro c ⟨x, y, hc⟩
    refine ⟨x, q * y, ?_⟩
    calc
      x * b * (q * y) = x * (b * q) * y := by simp only [mul_assoc]
      _ = x * a * y := by rw [hq]
      _ = c := hc
  · rintro c ⟨x, y, hc⟩
    refine ⟨x, p * y, ?_⟩
    calc
      x * a * (p * y) = x * (a * p) * y := by simp only [mul_assoc]
      _ = x * b * y := by rw [hp]
      _ = c := hc

/-
L-эквивалентные элементы J-эквивалентны.
-/
theorem L_eq_implies_J_eq {M : Type u} [Monoid M] {a b : M}
    (h : L_eq a b) : J_eq a b := by
  have hb : b ∈ reachLeft b := ⟨1, one_mul b⟩
  have ha : a ∈ reachLeft a := ⟨1, one_mul a⟩
  have hb_from_a : b ∈ reachLeft a := by rw [h]; exact hb
  have ha_from_b : a ∈ reachLeft b := by rw [← h]; exact ha
  obtain ⟨p, hp⟩ := hb_from_a
  obtain ⟨q, hq⟩ := ha_from_b
  apply Set.eq_of_subset_of_subset
  · rintro c ⟨x, y, hc⟩
    refine ⟨x * q, y, ?_⟩
    calc
      (x * q) * b * y = x * (q * b) * y := by simp only [mul_assoc]
      _ = x * a * y := by rw [hq]
      _ = c := hc
  · rintro c ⟨x, y, hc⟩
    refine ⟨x * p, y, ?_⟩
    calc
      (x * p) * a * y = x * (p * a) * y := by simp only [mul_assoc]
      _ = x * b * y := by rw [hp]
      _ = c := hc

/-
D содержится в J.
-/
theorem D_eq_implies_J_eq {M : Type u} [Monoid M] {a b : M}
    (h : D_eq a b) : J_eq a b := by
  induction h with
  | single hxy =>
      cases hxy with
      | inl hR => exact R_eq_implies_J_eq hR
      | inr hL => exact L_eq_implies_J_eq hL
  | tail hab hbc ih =>
      cases hbc with
      | inl hR => exact J_eq_trans ih (R_eq_implies_J_eq hR)
      | inr hL => exact J_eq_trans ih (L_eq_implies_J_eq hL)

end UAM_Green
