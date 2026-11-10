import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free

set_option autoImplicit false

/-!
# RSIA — агенты (Задача A)
-/

namespace UAM_RSIA

universe u

/-- Идентификатор агента. -/
def AgentId := Nat

/-- Агент RSIA с алфавитом действий `α`.
    `trust ∈ ℤ` кодирует уровень доверия (значение не важно для структуры). -/
structure Agent (α : Type u) where
  /-- Идентификатор агента. -/
  id : AgentId
  /-- Множество действий, доступных агенту. -/
  capability : Set (UAM_Free.FreeMonoid α)
  /-- Уровень доверия к агенту. -/
  trust : ℤ

/-- Два агента с разными идентификаторами различны. -/
theorem Agent.id_ne_of_ne {α : Type u} (a₁ a₂ : Agent α)
    (h : a₁.id ≠ a₂.id) : a₁ ≠ a₂ := by
  intro h_eq
  exact h (congrArg Agent.id h_eq)

end UAM_RSIA
