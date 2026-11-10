import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_Agent
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Session
import RequestProject.Atlas.UAM_RSIA_Exit
import RequestProject.Atlas.UAM_RSIA_Cycle
import RequestProject.Atlas.UAM_RSIA_Iteration

set_option autoImplicit false

/-!
# RSIA — fork branch dynamics

This file integrates fork arbitration into complete RSIA rounds.  It records the
main session and the independent branch, transports their language and phase
invariants, and permits both sessions to continue through further rounds.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-! ### 1. A complete round with a fork decision -/

/-- Build the full four-phase record for a fork decision. -/
noncomputable def RSIARound.fromExitFork (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) : RSIARound α :=
  let construction := s.runConstruction steps
  let verified : VerifiedConstruction α :=
    { result := construction
      aligned := executeSteps_aligned_of_nerode_preserving
        s.protocolLanguage s.environment steps hNerode }
  let compressed := verified.toCompressedSession
  let verdict := ArbitrationVerdict.exitFork compressed exit
  let consensus := PhaseRingConsensus.fromExitFork compressed exit
  { input := s
    construction := construction
    verified := verified
    compressed := compressed
    verdict := verdict
    consensus := consensus
    construction_session_eq := rfl
    verified_result_eq := rfl
    compressed_verified_eq := rfl
    verdict_source_eq := rfl
    consensus_verdict_eq := rfl
    consensus_phase_eq := rfl }

/-- A fork round preserves the input protocol language on its main output. -/
theorem RSIARound.fromExitFork_language_preserved (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) :
    (RSIARound.fromExitFork s steps exit hNerode).output.protocolLanguage =
      s.protocolLanguage := by
  exact (RSIARound.fromExitFork s steps exit hNerode).language_preserved

/-- A fork round returns its main output to Construction. -/
theorem RSIARound.fromExitFork_phase (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) :
    (RSIARound.fromExitFork s steps exit hNerode).output.phase =
      .construction := by
  exact (RSIARound.fromExitFork s steps exit hNerode).output_phase

/-! ### 2. Invariants inherited by a fork branch -/

/-- A fork branch is Nerode-preserving when its branch environment respects
    the Nerode equivalence of the inherited protocol language. -/
def ForkBranch.isNerodePreserving (fb : ForkBranch α) : Prop :=
  Environment.isNerodePreserving fb.branch

/-- The canonical branch inherits its compressed source's protocol language. -/
theorem fork_branch_preserves_source_language (cs : CompressedSession α)
    (exit : ExitDeclaration α) :
    (cs.mkForkBranch exit).branch.protocolLanguage =
      cs.verified.protocolLanguage := by
  exact ForkBranch.branch_protocolLanguage cs exit

/-- The canonical branch starts in Construction. -/
theorem fork_branch_is_construction_phase (cs : CompressedSession α)
    (exit : ExitDeclaration α) :
    (cs.mkForkBranch exit).branch.phase = .construction := by
  exact ForkBranch.branch_is_construction cs exit

/-- The canonical branch starts at the state declared by the exiting agent. -/
theorem fork_branch_env_current (cs : CompressedSession α)
    (exit : ExitDeclaration α) :
    (cs.mkForkBranch exit).branch.environment.current = exit.branchState := by
  exact ForkBranch.branch_env_current cs exit

/-! ### 3. Iteration on a fork branch -/

/-- Run `n` continue rounds on a Nerode-preserving fork branch. -/
noncomputable def ForkBranch.runNContinueRounds (fb : ForkBranch α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : fb.isNerodePreserving) (n : Nat) : Session α :=
  fb.branch.runNContinueRounds steps hNerode n

/-- Continue iteration preserves the branch language. -/
theorem fork_branch_run_preserves_language (fb : ForkBranch α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : fb.isNerodePreserving) (n : Nat) :
    (fb.runNContinueRounds steps hNerode n).protocolLanguage =
      fb.branch.protocolLanguage := by
  exact fb.branch.runNContinueRounds_preserves_language steps hNerode n

/-- Continue iteration leaves the branch Nerode-preserving. -/
theorem fork_branch_run_isNerodePreserving (fb : ForkBranch α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : fb.isNerodePreserving) (n : Nat) :
    Environment.isNerodePreserving
      (fb.runNContinueRounds steps hNerode n) := by
  exact fb.branch.runNContinueRounds_isNerodePreserving steps hNerode n

/-- Iterating a canonical branch preserves the language of its compressed
    source's verified session. -/
theorem fork_branch_run_language_eq_source (cs : CompressedSession α)
    (exit : ExitDeclaration α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : (cs.mkForkBranch exit).isNerodePreserving) (n : Nat) :
    ((cs.mkForkBranch exit).runNContinueRounds steps hNerode n).protocolLanguage =
      cs.verified.protocolLanguage := by
  exact (fork_branch_run_preserves_language (cs.mkForkBranch exit)
    steps hNerode n).trans (ForkBranch.branch_protocolLanguage cs exit)

/-- After one or more continue rounds, the branch is in Construction. -/
theorem fork_branch_run_pos_phase (fb : ForkBranch α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : fb.isNerodePreserving) (n : Nat) :
    (fb.runNContinueRounds steps hNerode (n + 1)).phase =
      .construction := by
  exact fb.branch.runNContinueRounds_pos_phase steps hNerode n

/-! ### 4. The continuing main session -/

/-- The main session after a fork round.  For a canonical fork round its
    consensus has removed the exiting agent, preserved the language, and
    returned to Construction. -/
def RSIARound.forkMainSession (r : RSIARound α) : Session α :=
  r.output

/-- The main session of a round preserves its input language. -/
theorem fork_main_session_preserves_language (r : RSIARound α) :
    r.forkMainSession.protocolLanguage = r.input.protocolLanguage := by
  exact r.language_preserved

/-- The main session of a round is in Construction. -/
theorem fork_main_session_phase (r : RSIARound α) :
    r.forkMainSession.phase = .construction := by
  exact r.output_phase

/-! ### 5. Paired fork results -/

/-- Result of a fork decision: the continuing main session and its newly
    created independent branch.  The decision equation ties the declaration
    carried by the branch to the round's arbitration verdict. -/
structure ForkResult (α : Type u) where
  round : RSIARound α
  branch : ForkBranch α
  round_is_fork : round.verdict.decision = .exitFork branch.exit

/-- Build both sides of a fork from one session and exit declaration. -/
noncomputable def ForkResult.fromSession (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) : ForkResult α :=
  let round := RSIARound.fromExitFork s steps exit hNerode
  let cs := round.compressed
  { round := round
    branch := cs.mkForkBranch exit
    round_is_fork := rfl }

/-- The canonical fork result's main session preserves the original language. -/
theorem fork_result_main_preserves_language (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) :
    (ForkResult.fromSession s steps exit hNerode).round.output.protocolLanguage =
      s.protocolLanguage := by
  exact (ForkResult.fromSession s steps exit hNerode).round.language_preserved

/-- The canonical fork result's branch preserves the original language. -/
theorem fork_result_branch_preserves_language (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) :
    (ForkResult.fromSession s steps exit hNerode).branch.branch.protocolLanguage =
      s.protocolLanguage := by
  change ((RSIARound.fromExitFork s steps exit hNerode).compressed.mkForkBranch
    exit).branch.protocolLanguage = s.protocolLanguage
  exact (ForkBranch.branch_protocolLanguage
    (RSIARound.fromExitFork s steps exit hNerode).compressed exit).trans
      (by rfl)

/-- The canonical fork result's branch starts in Construction. -/
theorem fork_result_branch_phase (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) :
    (ForkResult.fromSession s steps exit hNerode).branch.branch.phase =
      .construction := by
  exact ForkBranch.branch_is_construction
    (RSIARound.fromExitFork s steps exit hNerode).compressed exit

/-- The canonical fork result's main session is in Construction. -/
theorem fork_result_main_phase (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) :
    (ForkResult.fromSession s steps exit hNerode).round.output.phase =
      .construction := by
  exact (ForkResult.fromSession s steps exit hNerode).round.output_phase

/-! ### 6. Iterating the main session after a fork -/

/-- Run `m` continue rounds on the main session produced by a fork. -/
noncomputable def ForkResult.mainContinueAfterFork (fr : ForkResult α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving fr.round.input)
    (m : Nat) : Session α :=
  fr.round.output.runNContinueRounds steps
    (fr.round.output_isNerodePreserving hNerode) m

/-- Further main-session rounds preserve the language before the fork. -/
theorem main_continue_after_fork_preserves_language (fr : ForkResult α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving fr.round.input)
    (m : Nat) :
    (fr.mainContinueAfterFork steps hNerode m).protocolLanguage =
      fr.round.input.protocolLanguage := by
  exact (fr.round.output.runNContinueRounds_preserves_language steps
    (fr.round.output_isNerodePreserving hNerode) m).trans
      fr.round.language_preserved

/-- After one or more further rounds, the main session is in Construction. -/
theorem main_continue_after_fork_pos_phase (fr : ForkResult α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving fr.round.input)
    (m : Nat) :
    (fr.mainContinueAfterFork steps hNerode (m + 1)).phase =
      .construction := by
  exact fr.round.output.runNContinueRounds_pos_phase steps
    (fr.round.output_isNerodePreserving hNerode) m

end UAM_RSIA
