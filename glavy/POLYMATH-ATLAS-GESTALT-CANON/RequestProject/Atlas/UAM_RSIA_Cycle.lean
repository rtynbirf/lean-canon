import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Execution
import RequestProject.Atlas.UAM_RSIA_Session
import RequestProject.Atlas.UAM_RSIA_Construction
import RequestProject.Atlas.UAM_RSIA_VerifiedConstruction
import RequestProject.Atlas.UAM_RSIA_CompressedSession
import RequestProject.Atlas.UAM_RSIA_Arbitration

set_option autoImplicit false

/-!
# RSIA — integration of the four-phase cycle

This file composes Construction, Verification, Compression, and Arbitration.
The resulting consensus returns to Construction while preserving the protocol
language.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-! ### 1. Nerode-preserving environments -/

/-- A session environment is Nerode-preserving when every possible execution
state and action stay in the same Nerode class for the protocol language. -/
def Environment.isNerodePreserving (s : Session α) : Prop :=
  ∀ (env : Environment α) (σ : UAM_Free.FreeMonoid α),
    UAM_RegularLanguages.nerodeRel s.protocolLanguage
      env.current (env.apply σ)

/-- Nerode preservation transports across equality of protocol languages. -/
theorem Environment.isNerodePreserving_of_protocolLanguage_eq
    (s₁ s₂ : Session α) (hLanguage : s₁.protocolLanguage = s₂.protocolLanguage)
    (h : Environment.isNerodePreserving s₁) :
    Environment.isNerodePreserving s₂ := by
  intro env σ
  rw [← hLanguage]
  exact h env σ

/-! ### 2. A complete cycle with a continue decision -/

/-- Run all four phases and continue with the same group of agents. -/
noncomputable def Session.runRSIACycleContinue (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) :
    PhaseRingConsensus α :=
  let construction := s.runConstruction steps
  let verified : VerifiedConstruction α :=
    { result := construction
      aligned := executeSteps_aligned_of_nerode_preserving
        s.protocolLanguage s.environment steps hNerode }
  let compressed := verified.toCompressedSession
  PhaseRingConsensus.fromContinue (ArbitrationVerdict.continue compressed)

/-- A complete continue cycle preserves the input protocol language. -/
theorem Session.runRSIACycleContinue_preserves_language
    (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) :
    (s.runRSIACycleContinue steps hNerode).postSession.protocolLanguage =
      s.protocolLanguage := by
  exact (s.runRSIACycleContinue steps hNerode).language_eq

/-! ### 3. A complete cycle with a clean-exit decision -/

/-- Run all four phases and accept a clean exit. -/
noncomputable def Session.runRSIACycleExitClean (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) :
    PhaseRingConsensus α :=
  let construction := s.runConstruction steps
  let verified : VerifiedConstruction α :=
    { result := construction
      aligned := executeSteps_aligned_of_nerode_preserving
        s.protocolLanguage s.environment steps hNerode }
  let compressed := verified.toCompressedSession
  PhaseRingConsensus.fromExitClean compressed exit

/-- A complete clean-exit cycle preserves the input protocol language. -/
theorem Session.runRSIACycleExitClean_preserves_language
    (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) :
    (s.runRSIACycleExitClean steps exit hNerode).postSession.protocolLanguage =
      s.protocolLanguage := by
  exact (s.runRSIACycleExitClean steps exit hNerode).language_eq

/-! ### 4. An explicit record of every phase -/

/-- A complete RSIA round, including coherence equations connecting every
intermediate result to the preceding phase. -/
structure RSIARound (α : Type u) where
  input : Session α
  construction : ConstructionResult α
  verified : VerifiedConstruction α
  compressed : CompressedSession α
  verdict : ArbitrationVerdict α
  consensus : PhaseRingConsensus α
  construction_session_eq : construction.session = input
  verified_result_eq : verified.result = construction
  compressed_verified_eq : compressed.verified = verified
  verdict_source_eq : verdict.source = compressed
  consensus_verdict_eq : consensus.verdict = verdict
  consensus_phase_eq : consensus.postSession.phase = .construction

/-- Output session of a round. -/
def RSIARound.output (r : RSIARound α) : Session α :=
  r.consensus.postSession

/-- An integrated round returns to the Construction phase. -/
theorem RSIARound.output_phase (r : RSIARound α) :
    r.output.phase = .construction :=
  r.consensus_phase_eq

/-- Every coherent round preserves the protocol language. -/
theorem RSIARound.language_preserved (r : RSIARound α) :
    r.output.protocolLanguage = r.input.protocolLanguage := by
  rw [RSIARound.output]
  calc
    r.consensus.postSession.protocolLanguage =
        r.consensus.verdict.source.verified.protocolLanguage :=
      r.consensus.language_eq
    _ = r.verdict.source.verified.protocolLanguage := by
      rw [r.consensus_verdict_eq]
    _ = r.compressed.verified.protocolLanguage := by
      rw [r.verdict_source_eq]
    _ = r.verified.protocolLanguage := by
      rw [r.compressed_verified_eq]
    _ = r.construction.session.protocolLanguage := by
      rw [VerifiedConstruction.protocolLanguage, r.verified_result_eq]
    _ = r.input.protocolLanguage := by
      rw [r.construction_session_eq]

/-! ### 5. Canonical round constructors -/

/-- Build the full phase record for a continue decision. -/
noncomputable def RSIARound.fromContinue (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) : RSIARound α :=
  let construction := s.runConstruction steps
  let verified : VerifiedConstruction α :=
    { result := construction
      aligned := executeSteps_aligned_of_nerode_preserving
        s.protocolLanguage s.environment steps hNerode }
  let compressed := verified.toCompressedSession
  let verdict := ArbitrationVerdict.continue compressed
  let consensus := PhaseRingConsensus.fromContinue verdict
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

/-- Build the full phase record for a clean-exit decision. -/
noncomputable def RSIARound.fromExitClean (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exit : ExitDeclaration α)
    (hNerode : Environment.isNerodePreserving s) : RSIARound α :=
  let construction := s.runConstruction steps
  let verified : VerifiedConstruction α :=
    { result := construction
      aligned := executeSteps_aligned_of_nerode_preserving
        s.protocolLanguage s.environment steps hNerode }
  let compressed := verified.toCompressedSession
  let verdict := ArbitrationVerdict.exitClean compressed exit
  let consensus := PhaseRingConsensus.fromExitClean compressed exit
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

/-! ### 6. Closure of the phase ring -/

/-- Four phase advances return to the initial phase. -/
theorem phaseRing_return_to_construction :
    (Phase.construction.next).next.next.next = Phase.construction :=
  Phase.next_cycle .construction

/-- The protocol language of any complete round equals its input language. -/
theorem protocol_preserved (r : RSIARound α) :
    r.output.protocolLanguage = r.input.protocolLanguage :=
  r.language_preserved

end UAM_RSIA
