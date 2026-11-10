import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free

set_option autoImplicit false

/-!
# RSIA — кольцо фаз координации (Задача D)
-/

namespace UAM_RSIA

/-- Фаза координации RSIA. -/
inductive Phase where
  /-- Конструирование. -/
  | construction : Phase
  /-- Верификация. -/
  | verification : Phase
  /-- Компрессия. -/
  | compression : Phase
  /-- Арбитраж. -/
  | arbitration : Phase
deriving Repr, DecidableEq

/-- Циклический порядок фаз. -/
def Phase.next : Phase → Phase
  | .construction => .verification
  | .verification => .compression
  | .compression => .arbitration
  | .arbitration => .construction

/-- Четыре шага возвращают в исходную фазу. -/
theorem Phase.next_cycle (p : Phase) :
    (p.next).next.next.next = p := by cases p <;> rfl

/-- У каждой фазы есть следующая. -/
theorem Phase.next_exists (p : Phase) : ∃ q, p.next = q := ⟨p.next, rfl⟩

/-- Два шага вперёд. -/
def Phase.next2 (p : Phase) : Phase := p.next.next

end UAM_RSIA
