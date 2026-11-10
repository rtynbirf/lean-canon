import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Green          -- R_eq, L_eq, H_eq (и reach, reachLeft, algLe транзитивно)
import RequestProject.Atlas.UAM_Idempotent     -- IsIdempotent

/-!
# UAM — Layer 4: H-классы (HClass)

Собственное определение H-класса и итоговая теорема Грина.
Файл импортирует канонические определения `algLe`, `reach`, `reachLeft`,
`R_eq`, `L_eq`, `H_eq`, `IsIdempotent` и не переопределяет их.
-/

namespace UAM_HClass
universe u

open UAM_Directionality UAM_Reachability UAM_Green UAM_Idempotent

variable {M : Type u} [Monoid M]

/-! ### §0. Собственное определение -/

/-- H-класс элемента `a`: множество элементов, H-эквивалентных `a`. -/
def HClass (a : M) : Set M := {b | H_eq a b}

/-! ### §1. Базовая достижимость -/

/-- Любой элемент достижим из самого себя справа. -/
theorem self_mem_reach (a : M) : a ∈ reach a := ⟨1, mul_one a⟩

/-- Любой элемент достижим из самого себя слева. -/
theorem self_mem_reachLeft (a : M) : a ∈ reachLeft a := ⟨1, one_mul a⟩

/-! ### §2. Отношения Грина — отношения эквивалентности -/

theorem R_eq_refl (a : M) : R_eq a a := rfl
theorem R_eq_symm {a b : M} (h : R_eq a b) : R_eq b a := h.symm
theorem R_eq_trans {a b c : M} (h1 : R_eq a b) (h2 : R_eq b c) : R_eq a c := h1.trans h2

theorem L_eq_refl (a : M) : L_eq a a := rfl
theorem L_eq_symm {a b : M} (h : L_eq a b) : L_eq b a := h.symm
theorem L_eq_trans {a b c : M} (h1 : L_eq a b) (h2 : L_eq b c) : L_eq a c := h1.trans h2

theorem H_eq_refl (a : M) : H_eq a a := ⟨rfl, rfl⟩
theorem H_eq_symm {a b : M} (h : H_eq a b) : H_eq b a := ⟨h.1.symm, h.2.symm⟩
theorem H_eq_trans {a b c : M} (h1 : H_eq a b) (h2 : H_eq b c) : H_eq a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-! ### §3. Свойства H-класса -/

/-- Принадлежность H-классу — это в точности H-эквивалентность. -/
theorem mem_HClass_iff {a b : M} : b ∈ HClass a ↔ H_eq a b := Iff.rfl

/-- Элемент лежит в собственном H-классе. -/
theorem self_mem_HClass (a : M) : a ∈ HClass a := H_eq_refl a

/-- H-класс симметричен: если `b ∈ HClass a`, то `a ∈ HClass b`. -/
theorem HClass_symm {a b : M} (h : b ∈ HClass a) : a ∈ HClass b := H_eq_symm h

/-- H-классы совпадают у H-эквивалентных элементов. -/
theorem HClass_eq_of_H_eq {a b : M} (h : H_eq a b) : HClass a = HClass b := by
  ext x
  exact ⟨fun hx => H_eq_trans (H_eq_symm h) hx, fun hx => H_eq_trans h hx⟩

/-! ### §4. Итоговая теорема Грина

  Идемпотент `e` является двусторонней единицей на всём своём H-классе:
  если `a` H-эквивалентно идемпотенту `e`, то `e * a = a` и `a * e = a`. -/

theorem green_theorem {e a : M} (he : IsIdempotent e) (h : a ∈ HClass e) :
    e * a = a ∧ a * e = a := by
  have he' : e * e = e := he
  obtain ⟨hR, hL⟩ := h
  -- Из R-эквивалентности: a ∈ reach e, значит ∃ c, e * c = a
  have haR : a ∈ reach a := self_mem_reach a
  rw [← hR] at haR
  obtain ⟨c, hc⟩ := haR
  -- Из L-эквивалентности: a ∈ reachLeft e, значит ∃ d, d * e = a
  have haL : a ∈ reachLeft a := self_mem_reachLeft a
  rw [← hL] at haL
  obtain ⟨d, hd⟩ := haL
  refine ⟨?_, ?_⟩
  · rw [← hc, ← mul_assoc, he']
  · rw [← hd, mul_assoc, he']

end UAM_HClass
