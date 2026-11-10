import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Green
import RequestProject.Atlas.UAM_Regular

/-!
# UAM — Прямоугольные банды (Rectangular Bands)

Прямоугольная банда `L × R` — полугруппа с умножением
`(l₁, r₁) * (l₂, r₂) = (l₁, r₂)`. Все её элементы идемпотентны, и выполняется
характеристическое тождество `a * b * a = a`.

**Замечание.** Прямоугольная банда — это полугруппа (при `|L|, |R| > 1` в ней нет
единицы), поэтому напрямую она не является моноидом. Чтобы связать её с
основанной на моноидах теорией UAM, мы присоединяем внешнюю единицу через
`WithOne`, получая моноид `WithOne (RectangularBand L R)`. На нём вложенные
элементы `↑a` идемпотентны и регулярны, а отношения Грина `R`/`L` совпадают с
равенством по левой/правой компоненте соответственно.
-/

namespace UAM_RectangularBand
universe u

/-- Прямоугольная банда как множество пар. -/
structure RectangularBand (L R : Type u) where
  /-- Левая компонента. -/
  left : L
  /-- Правая компонента. -/
  right : R

variable {L R : Type u}

/-- Умножение прямоугольной банды: `(l₁, r₁) * (l₂, r₂) = (l₁, r₂)`. -/
instance instMul : Mul (RectangularBand L R) where
  mul a b := ⟨a.left, b.right⟩

@[simp] theorem mul_left (a b : RectangularBand L R) : (a * b).left = a.left := rfl
@[simp] theorem mul_right (a b : RectangularBand L R) : (a * b).right = b.right := rfl

theorem mul_def (a b : RectangularBand L R) : a * b = ⟨a.left, b.right⟩ := rfl

/-- Прямоугольная банда — полугруппа. -/
instance instSemigroup : Semigroup (RectangularBand L R) where
  mul_assoc _ _ _ := rfl

/-- Все элементы идемпотентны: `a * a = a`. -/
theorem sg_idempotent (a : RectangularBand L R) : a * a = a := rfl

/-- Характеристическое тождество прямоугольной банды: `a * b * a = a`. -/
theorem rectangular_identity (a b : RectangularBand L R) : a * b * a = a := rfl

/-- В прямоугольной банде с двумя различными левыми и правыми компонентами
    идемпотенты НЕ коммутируют: она не полурешётка. -/
theorem not_commutative {l₁ l₂ : L} {r₁ r₂ : R} (hl : l₁ ≠ l₂) :
    (⟨l₁, r₁⟩ * ⟨l₂, r₂⟩ : RectangularBand L R) ≠ ⟨l₂, r₂⟩ * ⟨l₁, r₁⟩ := by
  intro h
  have : l₁ = l₂ := congrArg RectangularBand.left h
  exact hl this

/-! ### §. Связь с моноидной теорией UAM через `WithOne` -/

/-- Моноид, полученный присоединением внешней единицы к прямоугольной банде. -/
abbrev RB1 (L R : Type u) := WithOne (RectangularBand L R)

open UAM_Idempotent UAM_Regular UAM_Green UAM_Reachability

/-- Вложенный элемент идемпотентен в `WithOne`-моноиде. -/
theorem coe_isIdempotent (a : RectangularBand L R) :
    IsIdempotent (↑a : RB1 L R) := by
  show (↑a : RB1 L R) * ↑a = ↑a
  rw [← WithOne.coe_mul, sg_idempotent]

/-- Вложенный элемент регулярен: `a * a * a = a` при `x = a`. -/
theorem coe_isRegular (a : RectangularBand L R) :
    UAM_Regular.IsRegular (↑a : RB1 L R) := by
  refine ⟨↑a, ?_⟩
  show (↑a : RB1 L R) * ↑a * ↑a = ↑a
  rw [← WithOne.coe_mul, ← WithOne.coe_mul, sg_idempotent, sg_idempotent]

/-- Отношение Грина `R` на вложенных элементах — равенство по левой компоненте. -/
theorem coe_R_eq_iff (a b : RectangularBand L R) :
    R_eq (↑a : RB1 L R) (↑b) ↔ a.left = b.left := by
  have key : ∀ (x y : RectangularBand L R), x.left = y.left →
      reach (↑x : RB1 L R) ⊆ reach (↑y : RB1 L R) := by
    intro x y hxy c hc
    obtain ⟨d, hd⟩ := hc
    rcases d with _ | e
    · refine ⟨(↑(⟨y.left, x.right⟩ : RectangularBand L R) : RB1 L R), ?_⟩
      change (↑x : RB1 L R) * 1 = c at hd
      rw [mul_one] at hd
      rw [← WithOne.coe_mul, ← hd]
      apply congrArg WithOne.coe
      show (⟨y.left, x.right⟩ : RectangularBand L R) = x
      rw [← hxy]
    · refine ⟨(↑e : RB1 L R), ?_⟩
      change (↑x : RB1 L R) * ↑e = c at hd
      rw [← WithOne.coe_mul] at hd
      rw [← WithOne.coe_mul, ← hd]
      apply congrArg WithOne.coe
      show (⟨y.left, e.right⟩ : RectangularBand L R) = ⟨x.left, e.right⟩
      rw [← hxy]
  constructor
  · intro h
    have hmem : (↑a : RB1 L R) ∈ reach (↑b : RB1 L R) := by
      rw [← h]; exact ⟨1, mul_one _⟩
    obtain ⟨d, hd⟩ := hmem
    rcases d with _ | e
    · change (↑b : RB1 L R) * 1 = ↑a at hd
      rw [mul_one] at hd
      exact (congrArg RectangularBand.left (WithOne.coe_inj.mp hd)).symm
    · change (↑b : RB1 L R) * ↑e = ↑a at hd
      rw [← WithOne.coe_mul] at hd
      have h2 := WithOne.coe_inj.mp hd
      rw [mul_def] at h2
      exact (congrArg RectangularBand.left h2).symm
  · intro h
    exact Set.Subset.antisymm (key a b h) (key b a h.symm)

/-- Отношение Грина `L` на вложенных элементах — равенство по правой компоненте. -/
theorem coe_L_eq_iff (a b : RectangularBand L R) :
    L_eq (↑a : RB1 L R) (↑b) ↔ a.right = b.right := by
  have key : ∀ (x y : RectangularBand L R), x.right = y.right →
      reachLeft (↑x : RB1 L R) ⊆ reachLeft (↑y : RB1 L R) := by
    intro x y hxy c hc
    obtain ⟨d, hd⟩ := hc
    rcases d with _ | e
    · refine ⟨(↑(⟨x.left, y.right⟩ : RectangularBand L R) : RB1 L R), ?_⟩
      change (1 : RB1 L R) * ↑x = c at hd
      rw [one_mul] at hd
      rw [← WithOne.coe_mul, ← hd]
      apply congrArg WithOne.coe
      show (⟨x.left, y.right⟩ : RectangularBand L R) = x
      rw [← hxy]
    · refine ⟨(↑e : RB1 L R), ?_⟩
      change (↑e : RB1 L R) * ↑x = c at hd
      rw [← WithOne.coe_mul] at hd
      rw [← WithOne.coe_mul, ← hd]
      apply congrArg WithOne.coe
      show (⟨e.left, y.right⟩ : RectangularBand L R) = ⟨e.left, x.right⟩
      rw [← hxy]
  constructor
  · intro h
    have hmem : (↑a : RB1 L R) ∈ reachLeft (↑b : RB1 L R) := by
      rw [← h]; exact ⟨1, one_mul _⟩
    obtain ⟨d, hd⟩ := hmem
    rcases d with _ | e
    · change (1 : RB1 L R) * ↑b = ↑a at hd
      rw [one_mul] at hd
      exact (congrArg RectangularBand.right (WithOne.coe_inj.mp hd)).symm
    · change (↑e : RB1 L R) * ↑b = ↑a at hd
      rw [← WithOne.coe_mul] at hd
      have h2 := WithOne.coe_inj.mp hd
      rw [mul_def] at h2
      exact (congrArg RectangularBand.right h2).symm
  · intro h
    exact Set.Subset.antisymm (key a b h) (key b a h.symm)

end UAM_RectangularBand