import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_Agent
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Session
import RequestProject.Atlas.UAM_RSIA_Exit
import RequestProject.Atlas.UAM_RSIA_Cycle
import RequestProject.Atlas.UAM_RSIA_Iteration
import RequestProject.Atlas.UAM_RSIA_Branch
import RequestProject.Atlas.UAM_RSIA_Compression

set_option autoImplicit false

/-!
# RSIA top-level protocol engine

This module packages the four-phase machinery into a stateful engine.  A static
configuration contains the actions used in every round and an anti-entropy
compression that preserves the current protocol language.  The mutable state
records the main-line history and all fork results.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-! ### Static configuration -/

/-- Static RSIA configuration for a protocol language `L`.  Indexing the
configuration by `L` prevents an anti-entropy proof for one protocol from being
used with a different protocol. -/
structure RSIAConfig (α : Type u)
    (L : Set (UAM_Free.FreeMonoid α)) where
  /-- Actions executed during Construction in each round. -/
  steps : List (AgentId × UAM_Free.FreeMonoid α)
  /-- The size-decreasing anti-entropy operation. -/
  antiEntropy : AntiEntropyCycle α
  /-- Anti-entropy does not change the Nerode class for `L`. -/
  antiEntropy_isNerodePreserving :
    NerodePreserving L antiEntropy.compress

/-- Reindex a configuration along equality of protocol languages. -/
def RSIAConfig.reindex {L₁ L₂ : Set (UAM_Free.FreeMonoid α)}
    (cfg : RSIAConfig α L₁) (h : L₁ = L₂) : RSIAConfig α L₂ where
  steps := cfg.steps
  antiEntropy := cfg.antiEntropy
  antiEntropy_isNerodePreserving := by
    rw [← h]
    exact cfg.antiEntropy_isNerodePreserving

/-- Configured compression preserves membership in the protocol language. -/
theorem RSIAConfig.compress_preserves_language
    {L : Set (UAM_Free.FreeMonoid α)} (cfg : RSIAConfig α L)
    (w : UAM_Free.FreeMonoid α) :
    (w ∈ L) = (cfg.antiEntropy.compress w ∈ L) := by
  exact nerodePreserving_mem_language L cfg.antiEntropy.compress
    cfg.antiEntropy_isNerodePreserving w

/-- Every number of applications of the configured anti-entropy operation is
length-nonincreasing. -/
theorem RSIAConfig.compress_monotone
    {L : Set (UAM_Free.FreeMonoid α)} (cfg : RSIAConfig α L)
    (w : UAM_Free.FreeMonoid α) (n : Nat) :
    (cfg.antiEntropy.compress^[n] w).length ≤ w.length := by
  exact UAM_RSIA.compress_monotone cfg.antiEntropy w n

/-! ### Round decisions -/

/-- Extract the Arbitration decision represented by a completed round. -/
def RSIARound.decision (r : RSIARound α) : ArbitrationDecision α :=
  r.verdict.decision

/-- Nerode preservation transfers through a round independently of which
Arbitration decision it carries. -/
theorem RSIARound.decision_isNerodePreserving (r : RSIARound α)
    (h : Environment.isNerodePreserving r.input) :
    Environment.isNerodePreserving r.output := by
  exact r.output_isNerodePreserving h

/-! ### Stateful engine -/

/-- Mutable state of the top-level engine.  `initialLanguage` and the two
language fields make the history invariant explicit rather than relying on a
partial list-head operation. -/
structure RSIAState (α : Type u) where
  /-- Current main-line session. -/
  session : Session α
  /-- Static configuration, certified for the current protocol language. -/
  config : RSIAConfig α session.protocolLanguage
  /-- The language from which this execution started. -/
  initialLanguage : Set (UAM_Free.FreeMonoid α)
  /-- Current and initial protocol languages agree. -/
  language_eq_initial : session.protocolLanguage = initialLanguage
  /-- Current environment is Nerode-preserving. -/
  isNerodePreserving : Environment.isNerodePreserving session
  /-- Completed rounds on the main line, in chronological order. -/
  rounds : List (RSIARound α)
  /-- Every recorded round belongs to this language-preserving execution. -/
  rounds_language : ∀ r ∈ rounds,
    r.input.protocolLanguage = initialLanguage ∧
      r.output.protocolLanguage = initialLanguage
  /-- Forks created by main-line Arbitration. -/
  forks : List (ForkResult α)

/-- The current protocol language is invariant throughout the execution. -/
theorem RSIAState.language_invariant (st : RSIAState α) :
    st.session.protocolLanguage = st.initialLanguage := by
  exact st.language_eq_initial

/-- If a first round exists, the current language equals that round's input
language.  This is the safe counterpart of a statement using `head!`. -/
theorem RSIAState.language_eq_first_round_input (st : RSIAState α)
    (first : RSIARound α) (rest : List (RSIARound α))
    (hRounds : st.rounds = first :: rest) :
    st.session.protocolLanguage = first.input.protocolLanguage := by
  have hFirst : first.input.protocolLanguage = st.initialLanguage :=
    (st.rounds_language first (by rw [hRounds]; exact List.mem_cons_self)).1
  exact st.language_eq_initial.trans hFirst.symm

/-- Create an initial state with empty histories. -/
def RSIAState.init (s : Session α)
    (cfg : RSIAConfig α s.protocolLanguage)
    (hNerode : Environment.isNerodePreserving s) : RSIAState α where
  session := s
  config := cfg
  initialLanguage := s.protocolLanguage
  language_eq_initial := rfl
  isNerodePreserving := hNerode
  rounds := []
  rounds_language := by
    intro r hr
    contradiction
  forks := []

@[simp] theorem RSIAState.init_rounds_nil (s : Session α)
    (cfg : RSIAConfig α s.protocolLanguage)
    (hNerode : Environment.isNerodePreserving s) :
    (RSIAState.init s cfg hNerode).rounds = [] := by
  rfl

@[simp] theorem RSIAState.init_forks_nil (s : Session α)
    (cfg : RSIAConfig α s.protocolLanguage)
    (hNerode : Environment.isNerodePreserving s) :
    (RSIAState.init s cfg hNerode).forks = [] := by
  rfl

/-! ### One-round transitions -/

/-- Execute one continue round. -/
noncomputable def RSIAState.runContinueRound (st : RSIAState α) :
    RSIAState α :=
  let r := RSIARound.fromContinue st.session st.config.steps
    st.isNerodePreserving
  { session := r.output
    config := st.config.reindex r.language_preserved.symm
    initialLanguage := st.initialLanguage
    language_eq_initial := r.language_preserved.trans st.language_eq_initial
    isNerodePreserving := r.output_isNerodePreserving st.isNerodePreserving
    rounds := st.rounds ++ [r]
    rounds_language := by
      intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      cases hx with
      | inl hOld => exact st.rounds_language x hOld
      | inr hNew =>
          rw [hNew]
          exact ⟨st.language_eq_initial, r.language_preserved.trans st.language_eq_initial⟩
    forks := st.forks }

/-- Execute one clean-exit round. -/
noncomputable def RSIAState.runExitCleanRound (st : RSIAState α)
    (exit : ExitDeclaration α) : RSIAState α :=
  let r := RSIARound.fromExitClean st.session st.config.steps exit
    st.isNerodePreserving
  { session := r.output
    config := st.config.reindex r.language_preserved.symm
    initialLanguage := st.initialLanguage
    language_eq_initial := r.language_preserved.trans st.language_eq_initial
    isNerodePreserving := r.output_isNerodePreserving st.isNerodePreserving
    rounds := st.rounds ++ [r]
    rounds_language := by
      intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      cases hx with
      | inl hOld => exact st.rounds_language x hOld
      | inr hNew =>
          rw [hNew]
          exact ⟨st.language_eq_initial, r.language_preserved.trans st.language_eq_initial⟩
    forks := st.forks }

/-- Execute one fork round and retain both its main-line round and new branch. -/
noncomputable def RSIAState.runForkRound (st : RSIAState α)
    (exit : ExitDeclaration α) : RSIAState α :=
  let fr := ForkResult.fromSession st.session st.config.steps exit
    st.isNerodePreserving
  let r := fr.round
  { session := r.output
    config := st.config.reindex r.language_preserved.symm
    initialLanguage := st.initialLanguage
    language_eq_initial := r.language_preserved.trans st.language_eq_initial
    isNerodePreserving := r.output_isNerodePreserving st.isNerodePreserving
    rounds := st.rounds ++ [r]
    rounds_language := by
      intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      cases hx with
      | inl hOld => exact st.rounds_language x hOld
      | inr hNew =>
          rw [hNew]
          exact ⟨st.language_eq_initial, r.language_preserved.trans st.language_eq_initial⟩
    forks := st.forks ++ [fr] }

/-- A continue transition preserves the current protocol language. -/
theorem RSIAState.runContinueRound_preserves_language (st : RSIAState α) :
    st.runContinueRound.session.protocolLanguage =
      st.session.protocolLanguage := by
  exact (RSIARound.fromContinue st.session st.config.steps
    st.isNerodePreserving).language_preserved

/-- A clean-exit transition preserves the current protocol language. -/
theorem RSIAState.runExitCleanRound_preserves_language (st : RSIAState α)
    (exit : ExitDeclaration α) :
    (st.runExitCleanRound exit).session.protocolLanguage =
      st.session.protocolLanguage := by
  exact (RSIARound.fromExitClean st.session st.config.steps exit
    st.isNerodePreserving).language_preserved

/-- A fork transition preserves the current main-line protocol language. -/
theorem RSIAState.runForkRound_preserves_language (st : RSIAState α)
    (exit : ExitDeclaration α) :
    (st.runForkRound exit).session.protocolLanguage =
      st.session.protocolLanguage := by
  exact (ForkResult.fromSession st.session st.config.steps exit
    st.isNerodePreserving).round.language_preserved

/-- The continue successor carries a Nerode-preservation certificate. -/
theorem RSIAState.runContinueRound_isNerodePreserving (st : RSIAState α) :
    Environment.isNerodePreserving st.runContinueRound.session := by
  exact st.runContinueRound.isNerodePreserving

/-- The clean-exit successor carries a Nerode-preservation certificate. -/
theorem RSIAState.runExitCleanRound_isNerodePreserving (st : RSIAState α)
    (exit : ExitDeclaration α) :
    Environment.isNerodePreserving (st.runExitCleanRound exit).session := by
  exact (st.runExitCleanRound exit).isNerodePreserving

/-- The fork successor carries a Nerode-preservation certificate. -/
theorem RSIAState.runForkRound_isNerodePreserving (st : RSIAState α)
    (exit : ExitDeclaration α) :
    Environment.isNerodePreserving (st.runForkRound exit).session := by
  exact (st.runForkRound exit).isNerodePreserving

/-! ### Arbitrary finite instruction streams -/

/-- Instruction selecting the Arbitration outcome for one round. -/
inductive RoundInstruction (α : Type u) where
  | continue : RoundInstruction α
  | exitClean : ExitDeclaration α → RoundInstruction α
  | exitFork : ExitDeclaration α → RoundInstruction α

/-- Execute a finite heterogeneous sequence of rounds. -/
noncomputable def RSIAState.runInstructions (st : RSIAState α) :
    List (RoundInstruction α) → RSIAState α
  | [] => st
  | instruction :: rest =>
      let next := match instruction with
        | .continue => st.runContinueRound
        | .exitClean exit => st.runExitCleanRound exit
        | .exitFork exit => st.runForkRound exit
      next.runInstructions rest

@[simp] theorem RSIAState.runInstructions_nil (st : RSIAState α) :
    st.runInstructions [] = st := by
  rfl

/-- Every finite instruction stream preserves the language at its start. -/
theorem RSIAState.runInstructions_preserves_language (st : RSIAState α)
    (instructions : List (RoundInstruction α)) :
    (st.runInstructions instructions).session.protocolLanguage =
      st.session.protocolLanguage := by
  induction instructions generalizing st with
  | nil => rfl
  | cons instruction rest ih =>
      cases instruction with
      | «continue» =>
          exact (ih st.runContinueRound).trans
            st.runContinueRound_preserves_language
      | exitClean exit =>
          exact (ih (st.runExitCleanRound exit)).trans
            (st.runExitCleanRound_preserves_language exit)
      | exitFork exit =>
          exact (ih (st.runForkRound exit)).trans
            (st.runForkRound_preserves_language exit)

/-- Every finite instruction stream retains a Nerode-preservation proof. -/
theorem RSIAState.runInstructions_isNerodePreserving (st : RSIAState α)
    (instructions : List (RoundInstruction α)) :
    Environment.isNerodePreserving
      (st.runInstructions instructions).session := by
  exact (st.runInstructions instructions).isNerodePreserving

/-- Main RSIA theorem: every mixture of continue, clean-exit, and fork rounds
preserves the protocol language of the initial state. -/
theorem RSIAState.main_theorem (st : RSIAState α)
    (instructions : List (RoundInstruction α)) :
    (st.runInstructions instructions).session.protocolLanguage =
      st.session.protocolLanguage := by
  exact st.runInstructions_preserves_language instructions

/-- The stronger execution-wide form compares with the language at engine
initialization, not merely with the immediately preceding state. -/
theorem RSIAState.main_theorem_initial (st : RSIAState α)
    (instructions : List (RoundInstruction α)) :
    (st.runInstructions instructions).session.protocolLanguage =
      st.initialLanguage := by
  exact (st.main_theorem instructions).trans st.language_eq_initial

/-! ### Connecting the existing compression package -/

/-- Build a system configuration when an existing `NerodePreservingCycle` and
an `AntiEntropyCycle` have the same compression function.  The equality is
necessary because the pre-existing `NerodePreservingCycle` stores no length
or strict-compression data. -/
def NerodePreservingCycle.toRSIAConfig
    {L : Set (UAM_Free.FreeMonoid α)}
    (npc : NerodePreservingCycle α L)
    (antiEntropy : AntiEntropyCycle α)
    (hCompress : antiEntropy.compress = npc.compress)
    (steps : List (AgentId × UAM_Free.FreeMonoid α)) : RSIAConfig α L where
  steps := steps
  antiEntropy := antiEntropy
  antiEntropy_isNerodePreserving := by
    rw [hCompress]
    exact npc.preserving

/-- Compression in a configuration assembled from a
`NerodePreservingCycle` preserves language membership. -/
theorem NerodePreservingCycle.toRSIAConfig_compress_preserves_language
    {L : Set (UAM_Free.FreeMonoid α)}
    (npc : NerodePreservingCycle α L)
    (antiEntropy : AntiEntropyCycle α)
    (hCompress : antiEntropy.compress = npc.compress)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (w : UAM_Free.FreeMonoid α) :
    (w ∈ L) =
      ((npc.toRSIAConfig antiEntropy hCompress steps).antiEntropy.compress w ∈ L) := by
  exact (npc.toRSIAConfig antiEntropy hCompress steps).compress_preserves_language w

/-! ### Stopping, exit status, and checked forks -/

/-- An agent is compatible with the current protocol state when every action in
its capability is Nerode-aligned at that state. -/
def Agent.isNerodeCompatible (s : Session α) (agent : Agent α) : Prop :=
  ∀ action ∈ agent.capability,
    ActionAligned s.protocolLanguage s.environment.current action

/-- The engine has work left exactly when an active agent has a capability that
is not aligned with the current protocol state. -/
def RSIAState.HasIncompatibleAgent (st : RSIAState α) : Prop :=
  ∃ agent ∈ st.session.agents, ¬ agent.isNerodeCompatible st.session

/-- Top-level continuation condition. -/
def RSIAState.shouldContinue (st : RSIAState α) : Prop :=
  st.HasIncompatibleAgent

/-- Stopping condition: every active agent is Nerode-compatible. -/
def RSIAState.ShouldStop (st : RSIAState α) : Prop :=
  ∀ agent ∈ st.session.agents, agent.isNerodeCompatible st.session

/-- The continuation and stopping conditions are exact logical complements. -/
theorem RSIAState.not_shouldContinue_iff_shouldStop (st : RSIAState α) :
    ¬ st.shouldContinue ↔ st.ShouldStop := by
  constructor
  · intro h agent hAgent
    by_contra hIncompatible
    exact h ⟨agent, hAgent, hIncompatible⟩
  · intro hStop hContinue
    obtain ⟨agent, hAgent, hIncompatible⟩ := hContinue
    exact hIncompatible (hStop agent hAgent)

/-- Interpret a round decision as the corresponding agent exit lifecycle state.
Clean and fork exits first enter `exiting`; archival can subsequently attach the
final branch or archive word. -/
def RSIARound.exitStatus (r : RSIARound α) : ExitStatus α :=
  match r.decision with
  | .continue => .active
  | .exitClean exit => .exiting exit
  | .exitFork exit => .exiting exit

/-- The previously standalone fork predicate specialized to the current engine
state and the declaration's proposed branch state. -/
def RSIAState.forkCondition (st : RSIAState α)
    (exit : ExitDeclaration α) : Prop :=
  ForkCondition α st.session.protocolLanguage st.session.environment.current
    exit.branchState

/-- A checked fork transition pairs the updated engine state with evidence that
the requested branch is genuinely Nerode-incompatible with the main state. -/
structure CheckedForkTransition (α : Type u) where
  before : RSIAState α
  exit : ExitDeclaration α
  forkCondition : before.forkCondition exit
  after : RSIAState α
  after_eq : after = before.runForkRound exit

/-- Execute a fork only after its `ForkCondition` has been established. -/
noncomputable def RSIAState.runCheckedForkRound (st : RSIAState α)
    (exit : ExitDeclaration α) (hFork : st.forkCondition exit) :
    CheckedForkTransition α where
  before := st
  exit := exit
  forkCondition := hFork
  after := st.runForkRound exit
  after_eq := rfl

/-- A checked fork preserves the main-line protocol language. -/
theorem RSIAState.runCheckedForkRound_preserves_language (st : RSIAState α)
    (exit : ExitDeclaration α) (hFork : st.forkCondition exit) :
    (st.runCheckedForkRound exit hFork).after.session.protocolLanguage =
      st.session.protocolLanguage := by
  exact st.runForkRound_preserves_language exit

end UAM_RSIA
