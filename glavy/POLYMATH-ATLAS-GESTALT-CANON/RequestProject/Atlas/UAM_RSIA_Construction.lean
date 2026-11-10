import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RSIA_Agent
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Protocol
import RequestProject.Atlas.UAM_RSIA_PhaseRing
import RequestProject.Atlas.UAM_RSIA_Execution
import RequestProject.Atlas.UAM_RSIA_Session
import RequestProject.Atlas.UAM_RSIA_Verification

set_option autoImplicit false

/-!
# RSIA — фаза Construction (Задача C, Phase 1)

Фаза Construction: агенты выполняют действия, накапливая стигмергический
след. Результат передаётся в фазу Verification для проверки согласованности.
-/

namespace UAM_RSIA

universe u

/-- Результат фазы Construction. -/
structure ConstructionResult (α : Type u) where
  /-- Итоговая среда после всех действий. -/
  finalEnv : Environment α
  /-- Полный стигмергический след. -/
  trace : StigmergicTrace α
  /-- Сессия, породившая результат. -/
  session : Session α

/-- Выполнить фазу Construction: применить список действий к среде сессии. -/
def Session.runConstruction {α : Type u} (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α)) :
    ConstructionResult α :=
  let r := executeSteps α s.environment steps
  { finalEnv := r.1, trace := r.2, session := s }

/-- Среда результата = среда после выполнения всех шагов. -/
theorem Session.runConstruction_finalEnv {α : Type u} (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α)) :
    (s.runConstruction steps).finalEnv = (executeSteps α s.environment steps).1 :=
  rfl

/-- След результата = след, накопленный при выполнении. -/
theorem Session.runConstruction_trace {α : Type u} (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α)) :
    (s.runConstruction steps).trace = (executeSteps α s.environment steps).2 :=
  rfl

/-- Результат хранит породившую его сессию. -/
theorem Session.runConstruction_session {α : Type u} (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α)) :
    (s.runConstruction steps).session = s :=
  rfl

/-- Длина следа результата = числу выполненных шагов. -/
theorem Session.runConstruction_trace_length {α : Type u} (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α)) :
    (s.runConstruction steps).trace.length = steps.length := by
  rw [Session.runConstruction_trace, executeSteps_trace_length]

/-- Переход результата Construction к фазе Verification: протокол, среда и
    агенты сохраняются, меняется лишь фаза. -/
def ConstructionResult.toVerification {α : Type u} (r : ConstructionResult α) :
    Session α :=
  { r.session with phase := .verification }

/-- `toVerification` переводит сессию в фазу Verification. -/
theorem ConstructionResult.toVerification_is_verification {α : Type u}
    (r : ConstructionResult α) :
    r.toVerification.isVerificationPhase :=
  rfl

/-- `toVerification` не меняет протокол исходной сессии. -/
theorem ConstructionResult.toVerification_protocol {α : Type u}
    (r : ConstructionResult α) :
    r.toVerification.protocol = r.session.protocol :=
  rfl

/-- Пустая Construction (без шагов) не меняет среду. -/
theorem Session.runConstruction_empty {α : Type u} (s : Session α) :
    (s.runConstruction []).finalEnv = s.environment := by
  rw [Session.runConstruction_finalEnv, executeSteps_nil]

/-- Пустая Construction даёт пустой след. -/
theorem Session.runConstruction_empty_trace {α : Type u} (s : Session α) :
    (s.runConstruction []).trace = .empty := by
  rw [Session.runConstruction_trace, executeSteps_nil]

end UAM_RSIA
