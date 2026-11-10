import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_Agent
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Exit
import RequestProject.Atlas.UAM_RSIA_PhaseRing
import RequestProject.Atlas.UAM_RSIA_Session
import RequestProject.Atlas.UAM_RSIA_CompressedSession

set_option autoImplicit false

/-!
# RSIA — фаза Arbitration (Задача I, Phase 4)

Арбитраж замыкает кольцо фаз. Решение может продолжить основную сессию,
чисто удалить выходящего агента или создать отдельную ветку. Во всех случаях
протокол и его язык основной сессии сохраняются, а следующая фаза —
Construction.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-! ### §1. Решения арбитража -/

/-- Дискретное решение арбитража. -/
inductive ArbitrationDecision (α : Type u) where
  /-- Продолжить работу без выхода агента. -/
  | continue : ArbitrationDecision α
  /-- Принять чистый выход агента. -/
  | exitClean : ExitDeclaration α → ArbitrationDecision α
  /-- Принять выход с созданием отдельной ветки. -/
  | exitFork : ExitDeclaration α → ArbitrationDecision α

/-! ### §2. Удаление агента -/

/-- Удалить из списка всех агентов с данным идентификатором. -/
noncomputable def removeAgent (agentId : AgentId) (agents : List (Agent α)) : List (Agent α) :=
  agents.filter (fun agent => decide (agent.id ≠ agentId))

/-- После удаления в списке нет агента с удалённым идентификатором. -/
theorem removeAgent_id_absent (agentId : AgentId) (agents : List (Agent α))
    (agent : Agent α) (h : agent ∈ removeAgent agentId agents) :
    agent.id ≠ agentId := by
  simp only [removeAgent, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

/-! ### §3. Отдельная ветка форка -/

/-- Форк-ветка хранит сжатую исходную сессию, декларацию выхода и новую,
    независимую сессию ветки. -/
structure ForkBranch (α : Type u) where
  source : CompressedSession α
  exit : ExitDeclaration α
  branch : Session α

/-- Создать отдельную ветку. Она наследует протокол и функцию применения
    действий, начинает с объявленного состояния, не содержит выходящего агента
    и возвращается в фазу Construction. -/
noncomputable def CompressedSession.mkForkBranch (cs : CompressedSession α)
    (exit : ExitDeclaration α) : ForkBranch α where
  source := cs
  exit := exit
  branch :=
    { protocol := cs.toArbitration.protocol
      environment :=
        { current := exit.branchState
          apply := cs.toArbitration.environment.apply }
      agents := removeAgent exit.agentId cs.toArbitration.agents
      phase := .construction }

/-- Ветка наследует язык протокола исходной сессии. -/
theorem ForkBranch.branch_protocolLanguage (cs : CompressedSession α)
    (exit : ExitDeclaration α) :
    (cs.mkForkBranch exit).branch.protocolLanguage =
      cs.verified.protocolLanguage :=
  cs.toArbitration_protocolLanguage

/-- Ветка начинается в фазе Construction. -/
theorem ForkBranch.branch_is_construction (cs : CompressedSession α)
    (exit : ExitDeclaration α) :
    (cs.mkForkBranch exit).branch.isConstructionPhase :=
  rfl

/-- Начальное состояние ветки задано декларацией выхода. -/
theorem ForkBranch.branch_env_current (cs : CompressedSession α)
    (exit : ExitDeclaration α) :
    (cs.mkForkBranch exit).branch.environment.current = exit.branchState :=
  rfl

/-! ### §4. Свойства условия форка -/

/-- Nerode-эквивалентные состояния не удовлетворяют условию форка. -/
theorem forkCondition_not_of_nerode
    (L : Set (UAM_Free.FreeMonoid α))
    (mainState branchState : UAM_Free.FreeMonoid α)
    (h : UAM_RegularLanguages.nerodeRel L mainState branchState) :
    ¬ ForkCondition α L mainState branchState :=
  fun hFork => hFork h

/-- Условие форка симметрично: несовместимость сохраняется при перестановке
    основного состояния и состояния ветки. -/
theorem forkCondition_antisym
    (L : Set (UAM_Free.FreeMonoid α))
    (mainState branchState : UAM_Free.FreeMonoid α)
    (hFork : ForkCondition α L mainState branchState) :
    ¬ UAM_RegularLanguages.nerodeRel L branchState mainState := by
  intro h
  exact hFork (UAM_RegularLanguages.nerodeRel_symm L branchState mainState h)

/-! ### §5. Вердикт с языковым инвариантом -/

/-- Вердикт арбитража вместе с доказательством, что основной сжатый DFA
    продолжает распознавать язык протокола. -/
structure ArbitrationVerdict (α : Type u) where
  source : CompressedSession α
  decision : ArbitrationDecision α
  languagePreserved : source.compressedDFA.language =
    source.verified.protocolLanguage

/-- Вердикт продолжения. -/
def ArbitrationVerdict.continue (cs : CompressedSession α) :
    ArbitrationVerdict α where
  source := cs
  decision := .continue
  languagePreserved := cs.compressedDFA_language

/-- Вердикт чистого выхода. -/
def ArbitrationVerdict.exitClean (cs : CompressedSession α)
    (exit : ExitDeclaration α) : ArbitrationVerdict α where
  source := cs
  decision := .exitClean exit
  languagePreserved := cs.compressedDFA_language

/-- Вердикт выхода с отдельной веткой. -/
def ArbitrationVerdict.exitFork (cs : CompressedSession α)
    (exit : ExitDeclaration α) : ArbitrationVerdict α where
  source := cs
  decision := .exitFork exit
  languagePreserved := cs.compressedDFA_language

/-! ### §6. Консенсус и возврат к Construction -/

/-- Результат консенсуса: пост-сессия и доказательство сохранения языка
    протокола исходной верифицированной сессии. -/
structure PhaseRingConsensus (α : Type u) where
  verdict : ArbitrationVerdict α
  postSession : Session α
  language_eq : postSession.protocolLanguage =
    verdict.source.verified.protocolLanguage

/-- Консенсус для продолжения: меняется только фаза. -/
def PhaseRingConsensus.fromContinue (v : ArbitrationVerdict α) :
    PhaseRingConsensus α where
  verdict := v
  postSession := { v.source.toArbitration with phase := .construction }
  language_eq := v.source.toArbitration_protocolLanguage

/-- Консенсус для чистого выхода: агент удаляется, протокол и среда
    сохраняются, начинается новая Construction-фаза. -/
noncomputable def PhaseRingConsensus.fromExitClean (cs : CompressedSession α)
    (exit : ExitDeclaration α) : PhaseRingConsensus α where
  verdict := ArbitrationVerdict.exitClean cs exit
  postSession :=
    { protocol := cs.toArbitration.protocol
      environment := cs.toArbitration.environment
      agents := removeAgent exit.agentId cs.toArbitration.agents
      phase := .construction }
  language_eq := cs.toArbitration_protocolLanguage

/-- Консенсус для форка: основная сессия удаляет выходящего агента; отдельная
    ветка может быть получена через `CompressedSession.mkForkBranch`. -/
noncomputable def PhaseRingConsensus.fromExitFork (cs : CompressedSession α)
    (exit : ExitDeclaration α) : PhaseRingConsensus α where
  verdict := ArbitrationVerdict.exitFork cs exit
  postSession :=
    { protocol := cs.toArbitration.protocol
      environment := cs.toArbitration.environment
      agents := removeAgent exit.agentId cs.toArbitration.agents
      phase := .construction }
  language_eq := cs.toArbitration_protocolLanguage

/-! ### §7. Замыкание фазового кольца -/

/-- Любой вердикт сохраняет язык основного сжатого DFA. -/
theorem arbitration_preserves_language (v : ArbitrationVerdict α) :
    v.source.compressedDFA.language = v.source.verified.protocolLanguage :=
  v.languagePreserved

/-- Любой консенсус сохраняет язык протокола. -/
theorem consensus_preserves_protocol_language (c : PhaseRingConsensus α) :
    c.postSession.protocolLanguage = c.verdict.source.verified.protocolLanguage :=
  c.language_eq

/-- После Arbitration следующей является Construction. -/
theorem Phase.arbitration_next_construction : Phase.arbitration.next =
    Phase.construction :=
  rfl

/-- Пост-сессия любого из трёх стандартных консенсусов находится в фазе
    Construction. -/
theorem PhaseRingConsensus.fromContinue_phase (v : ArbitrationVerdict α) :
    (PhaseRingConsensus.fromContinue v).postSession.phase = .construction :=
  rfl

theorem PhaseRingConsensus.fromExitClean_phase (cs : CompressedSession α)
    (exit : ExitDeclaration α) :
    (PhaseRingConsensus.fromExitClean cs exit).postSession.phase = .construction :=
  rfl

theorem PhaseRingConsensus.fromExitFork_phase (cs : CompressedSession α)
    (exit : ExitDeclaration α) :
    (PhaseRingConsensus.fromExitFork cs exit).postSession.phase = .construction :=
  rfl

/-- Переход фазы из Arbitration возвращает сессию в Construction. -/
theorem phase_advances (s : Session α) (h : s.phase = .arbitration) :
    s.nextPhase.phase = .construction := by
  simp only [Session.nextPhase, h, Phase.arbitration_next_construction]

/-- Полный обход четырёх фаз возвращает исходную фазу. -/
theorem phaseRing_full_cycle (p : Phase) :
    (p.next).next.next.next = p :=
  Phase.next_cycle p

/-- Протокольный язык пост-сессии совпадает с языком исходной Arbitration-сессии. -/
theorem PhaseRingConsensus.postSession_protocol_eq_source
    (c : PhaseRingConsensus α) :
    c.postSession.protocolLanguage =
      c.verdict.source.toArbitration.protocolLanguage :=
  c.language_eq.trans c.verdict.source.toArbitration_protocolLanguage.symm

end UAM_RSIA
