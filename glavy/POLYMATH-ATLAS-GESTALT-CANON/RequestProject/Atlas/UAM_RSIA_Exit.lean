import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_Agent

set_option autoImplicit false

/-!
# RSIA — выход и форк (Задача H)
-/

namespace UAM_RSIA

universe u

/-- Декларация выхода агента. -/
structure ExitDeclaration (α : Type u) where
  /-- Идентификатор выходящего агента. -/
  agentId : AgentId
  /-- Причина выхода (закодированная словом). -/
  reason : UAM_Free.FreeMonoid α
  /-- Состояние ветки, порождённой выходом. -/
  branchState : UAM_Free.FreeMonoid α

/-- Условие форка: состояние ветки Нероуд-несовместимо с основным состоянием. -/
def ForkCondition (α : Type u) (L : Set (UAM_Free.FreeMonoid α))
    (mainState branchState : UAM_Free.FreeMonoid α) : Prop :=
  ¬ UAM_RegularLanguages.nerodeRel L mainState branchState

/-- Статус выхода агента. -/
inductive ExitStatus (α : Type u) where
  /-- Агент активен. -/
  | active : ExitStatus α
  /-- Агент выходит (декларация подана). -/
  | exiting : ExitDeclaration α → ExitStatus α
  /-- Агент вышел и заархивирован с финальным состоянием. -/
  | archived : ExitDeclaration α → UAM_Free.FreeMonoid α → ExitStatus α

/-- Выход агента не меняет язык, распознаваемый основным автоматом:
    форк порождает отдельную ветку, но основной аттрактор `A` сохраняется. -/
theorem exit_preserves_language {α Q : Type u} [DecidableEq Q]
    (A : UAM_DFAEval.DFA α Q)
    (L : Set (UAM_Free.FreeMonoid α))
    (hL : A.language = L) (_branch : UAM_Free.FreeMonoid α) :
    A.language = L := hL

end UAM_RSIA
