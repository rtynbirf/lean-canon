import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_MyhillNerode
import RequestProject.Atlas.UAM_RSIA_Agent
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Protocol
import RequestProject.Atlas.UAM_RSIA_PhaseRing
import RequestProject.Atlas.UAM_RSIA_TargetLanguage
import RequestProject.Atlas.UAM_RSIA_Attractor

set_option autoImplicit false

/-!
# RSIA — сессия (Задача B, Phase 1)

Сессия связывает все компоненты RSIA: протокол, среду, агентов и текущую фазу
координации. Это центральный тип для выполнения фазы Construction.
-/

namespace UAM_RSIA

open Classical

universe u

/-- Сессия RSIA: полный контекст выполнения. -/
structure Session (α : Type u) where
  /-- Протокол координации. -/
  protocol : Protocol α
  /-- Текущая стигмергическая среда. -/
  environment : Environment α
  /-- Список участников. -/
  agents : List (Agent α)
  /-- Текущая фаза координации. -/
  phase : Phase

/-- Язык протокола сессии. -/
def Session.protocolLanguage {α : Type u} (s : Session α) :
    Set (UAM_Free.FreeMonoid α) :=
  s.protocol.language

/-- Аттрактор протокола сессии (канонический DFA языка протокола). -/
noncomputable def Session.attractor {α : Type u} (s : Session α) :
    UAM_DFAEval.DFA α (UAM_MyhillNerode.NerodeClass s.protocolLanguage) :=
  rsiaAttractor α s.protocolLanguage

/-- Аттрактор распознаёт язык протокола сессии. -/
theorem Session.attractor_language {α : Type u} (s : Session α) :
    (s.attractor).language = s.protocolLanguage :=
  rsiaAttractor_language α s.protocolLanguage

/-- Агент способен выполнить действие: действие входит в его capability. -/
def Agent.canAct {α : Type u} (a : Agent α)
    (σ : UAM_Free.FreeMonoid α) : Prop :=
  σ ∈ a.capability

/-- Шаг сессии допустим: (1) существует авторизованный и способный агент,
    (2) результат применения действия протокольно-совместим. -/
def Session.validStep {α : Type u} (s : Session α) (agentId : AgentId)
    (σ : UAM_Free.FreeMonoid α) : Prop :=
  (∃ a ∈ s.agents, a.id = agentId ∧ a.canAct σ) ∧
  ProtocolCompliance s.protocol (s.environment.apply σ)

/-- Текущее состояние среды протокольно-совместимо. -/
def Session.isCompliant {α : Type u} (s : Session α) : Prop :=
  ProtocolCompliance s.protocol s.environment.current

/-- Переход к следующей фазе координации. -/
def Session.nextPhase {α : Type u} (s : Session α) : Session α :=
  { s with phase := s.phase.next }

/-- Переход к следующей фазе не меняет протокол, среду и агентов. -/
theorem Session.nextPhase_protocol {α : Type u} (s : Session α) :
    s.nextPhase.protocol = s.protocol := rfl

/-- Четыре перехода фазы = возврат к исходной сессии. -/
theorem Session.nextPhase_cycle {α : Type u} (s : Session α) :
    s.nextPhase.nextPhase.nextPhase.nextPhase = s := by
  simp only [Session.nextPhase, Phase.next_cycle]

/-- Сессия находится в фазе Construction. -/
def Session.isConstructionPhase {α : Type u} (s : Session α) : Prop :=
  s.phase = .construction

/-- Сессия находится в фазе Verification. -/
def Session.isVerificationPhase {α : Type u} (s : Session α) : Prop :=
  s.phase = .verification

/-- После `nextPhase` из Construction попадаем в Verification. -/
theorem Session.construction_next_is_verification {α : Type u} (s : Session α)
    (h : s.isConstructionPhase) :
    s.nextPhase.isVerificationPhase := by
  simp only [Session.isConstructionPhase, Session.isVerificationPhase,
    Session.nextPhase] at *
  rw [h]
  rfl

end UAM_RSIA
