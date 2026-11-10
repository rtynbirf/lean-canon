import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib

/-!
# UAM — Layer 5: Полугруппа матричного типа Риса (ReesMatrix)

Формализация полугруппы Риса `M°(G; Λ, P)`: элементы — либо нуль, либо
тройка `(i, g, j)` (индекс строки, элемент группы, индекс столбца).
Умножение задаётся «бутербродной» матрицей `P`.

Этот файл строится на `Group G` из Mathlib и не импортирует UAM-файлы:
полугруппа Риса, вообще говоря, не является моноидом.
-/

namespace UAM_ReesMatrix
universe u

/-- Элемент полугруппы Риса: либо нуль (`none`), либо тройка
    `(индекс строки, элемент группы, индекс столбца)`. -/
def ReesMatrix (G : Type u) [Group G] (Λ : Type u) [DecidableEq Λ]
    (_P : Λ → Λ → G) := Option (Λ × G × Λ)

namespace ReesMatrix
variable {G : Type u} [Group G] {Λ : Type u} [DecidableEq Λ] {P : Λ → Λ → G}

/-- Нулевой элемент. -/
def zero : ReesMatrix G Λ P := none

/-- Умножение в полугруппе Риса. -/
def mul : ReesMatrix G Λ P → ReesMatrix G Λ P → ReesMatrix G Λ P
  | some (i, g, j), some (k, h, l) =>
    if j = k then some (i, g * P j k * h, l) else none
  | _, _ => none

/-! ### §1. Нулевое умножение -/

theorem zero_mul (x : ReesMatrix G Λ P) : mul zero x = zero := rfl

theorem mul_zero (x : ReesMatrix G Λ P) : mul x zero = zero := by
  cases x with
  | none => rfl
  | some _ => rfl

/-- Умножение справа на `none` даёт `none`. -/
theorem mul_none (x : ReesMatrix G Λ P) : mul x none = none := by
  cases x with
  | none => rfl
  | some _ => rfl

/-! ### §2. Внутренние элементы -/

/-- Умножение двух совместимых троек. -/
theorem elem_mul_elem {i k : Λ} {g h : G} {j l : Λ} (heq : j = k) :
    mul (P := P) (some (i, g, j)) (some (k, h, l)) = some (i, g * P j k * h, l) := by
  show (if j = k then some (i, g * P j k * h, l) else none) = some (i, g * P j k * h, l)
  rw [if_pos heq]

/-- Умножение двух несовместимых троек даёт нуль. -/
theorem elem_mul_ne {i k : Λ} {g h : G} {j l : Λ} (hne : j ≠ k) :
    mul (P := P) (some (i, g, j)) (some (k, h, l)) = none := by
  show (if j = k then some (i, g * P j k * h, l) else none) = none
  rw [if_neg hne]

/-! ### §3. Ассоциативность -/

theorem mul_assoc (x y z : ReesMatrix G Λ P) :
    mul (mul x y) z = mul x (mul y z) := by
  cases x with
  | none => rfl
  | some xt =>
    obtain ⟨i, g, j⟩ := xt
    cases y with
    | none => rfl
    | some yt =>
      obtain ⟨k, h, l⟩ := yt
      cases z with
      | none => simp only [mul_none]
      | some zt =>
        obtain ⟨m, n, p⟩ := zt
        by_cases h1 : j = k
        · by_cases h2 : l = m
          · -- обе пары совместимы: ассоциативность в группе
            rw [elem_mul_elem h1, elem_mul_elem h2, elem_mul_elem h2, elem_mul_elem h1]
            simp only [_root_.mul_assoc]
          · -- j = k, l ≠ m
            rw [elem_mul_elem h1, elem_mul_ne h2, elem_mul_ne h2, mul_none]
        · -- j ≠ k
          by_cases h2 : l = m
          · rw [elem_mul_ne h1, elem_mul_elem h2, elem_mul_ne h1]; rfl
          · rw [elem_mul_ne h1, elem_mul_ne h2, mul_none]; rfl

end ReesMatrix
end UAM_ReesMatrix
