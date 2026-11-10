import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_Constrained
import RequestProject.Atlas.UAM_RSIA_NerodeBridge

set_option autoImplicit false

/-!
# Constrained RSIA capstone

This file packages a constrained hierarchical parallel system with explicit
certificates for its four load-bearing barriers.  The concrete instance uses
the nontrivial zero-star language over `Fin 4`.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- A constrained hierarchy with explicit certificates for local Nerode
preservation, anti-entropy compression, Nerode-preserving compression, and
termination from every stored current environment. -/
structure ConstrainedCapstone (α : Type u) where
  hps : ConstrainedHierarchicalParallelSystem α
  barrier_local_nerode : ∀ state ∈ hps.system.sessions,
    Environment.isLocallyNerodePreserving state.session
  barrier_anti_entropy : ∀ state ∈ hps.system.sessions,
    ∀ w : UAM_Free.FreeMonoid α, w ≠ [] →
      IsCompression w (state.config.antiEntropy.compress w)
  barrier_nerode_compress : ∀ state ∈ hps.system.sessions,
    NerodePreserving state.session.protocolLanguage
      state.config.antiEntropy.compress
  barrier_termination : ∀ state ∈ hps.system.sessions,
    ∃ n : ℕ,
      (state.config.antiEntropy.compress^[n])
        state.session.environment.current = []

/-- The designated root session. -/
def ConstrainedCapstone.rootSession (cap : ConstrainedCapstone α) : Session α :=
  (cap.hps.system.sessions.get
    ⟨cap.hps.rootLabel, cap.hps.rootLabel_in_range⟩).session

/-- The protocol language of the designated root session. -/
def ConstrainedCapstone.rootLanguage (cap : ConstrainedCapstone α) :
    Set (UAM_Free.FreeMonoid α) :=
  cap.rootSession.protocolLanguage

/-- The anti-entropy compression of the designated root state. -/
noncomputable def ConstrainedCapstone.rootCompress
    (cap : ConstrainedCapstone α) :
    UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α :=
  (cap.hps.system.sessions.get
    ⟨cap.hps.rootLabel, cap.hps.rootLabel_in_range⟩).config.antiEntropy.compress

/-- The concrete hierarchy satisfies Barrier 1. -/
theorem instConstrainedHPSFin4_barrier_1 :
    ∀ state ∈ instConstrainedHPSFin4.system.sessions,
      Environment.isLocallyNerodePreserving state.session := by
  intro state hState
  simp only [instConstrainedHPSFin4, fin4ZeroStarConstrainedParallel,
    List.mem_singleton] at hState
  subst state
  exact fin4ZeroStarSession_localNerode

/-- The concrete hierarchy satisfies Barrier 2. -/
theorem instConstrainedHPSFin4_barrier_2 :
    ∀ state ∈ instConstrainedHPSFin4.system.sessions,
      ∀ w : UAM_Free.FreeMonoid (Fin 4), w ≠ [] →
        IsCompression w (state.config.antiEntropy.compress w) := by
  intro state hState w hw
  simp only [instConstrainedHPSFin4, fin4ZeroStarConstrainedParallel,
    List.mem_singleton] at hState
  subst state
  exact fin4ZeroStarConstrainedState.config.antiEntropy.compresses_nonempty w hw

/-- The concrete hierarchy satisfies Barrier 3. -/
theorem instConstrainedHPSFin4_barrier_3 :
    ∀ state ∈ instConstrainedHPSFin4.system.sessions,
      NerodePreserving state.session.protocolLanguage
        state.config.antiEntropy.compress := by
  intro state hState
  simp only [instConstrainedHPSFin4, fin4ZeroStarConstrainedParallel,
    List.mem_singleton] at hState
  subst state
  exact fin4ZeroStarConstrainedState.config.antiEntropy_nerode

/-- The concrete hierarchy satisfies Barrier 4: its stored current word `[0]`
reaches the empty word after one compression. -/
theorem instConstrainedHPSFin4_barrier_4 :
    ∀ state ∈ instConstrainedHPSFin4.system.sessions,
      ∃ n : ℕ,
        (state.config.antiEntropy.compress^[n])
          state.session.environment.current = [] := by
  intro state hState
  simp only [instConstrainedHPSFin4, fin4ZeroStarConstrainedParallel,
    List.mem_singleton] at hState
  subst state
  use 1
  simp [fin4ZeroStarConstrainedState, fin4ZeroStarSession,
    fin4ZeroStarAntiEntropy, fin4ZeroStarCompress, Fin4ZeroStarLanguage]

/-- The concrete constrained capstone over `Fin 4` and the language `0*`. -/
noncomputable def constrainedCapstoneFin4 : ConstrainedCapstone (Fin 4) where
  hps := instConstrainedHPSFin4
  barrier_local_nerode := instConstrainedHPSFin4_barrier_1
  barrier_anti_entropy := instConstrainedHPSFin4_barrier_2
  barrier_nerode_compress := instConstrainedHPSFin4_barrier_3
  barrier_termination := instConstrainedHPSFin4_barrier_4

/-- The constrained capstone is inhabited over `Fin 4`. -/
theorem constrainedCapstoneFin4_nonempty :
    Nonempty (ConstrainedCapstone (Fin 4)) :=
  ⟨constrainedCapstoneFin4⟩

/-- If every component language is universal, the local invariant can be
promoted to the original globally quantified invariant. -/
theorem ConstrainedCapstone.local_implies_global_when_univ
    (cap : ConstrainedCapstone α)
    (hUniv : ∀ state ∈ cap.hps.system.sessions,
      state.session.protocolLanguage = Set.univ) :
    ∀ state ∈ cap.hps.system.sessions,
      Environment.isNerodePreserving state.session := by
  intro state hState
  exact Environment.local_implies_global_univ state.session
    (hUniv state hState) (cap.barrier_local_nerode state hState)

/-- The concrete capstone has root language `0*`, that language is not
universal, and its root compression preserves the language's Nerode classes. -/
theorem rules_unmisunderstandable_constrained :
    ∃ (cap : ConstrainedCapstone (Fin 4)),
      let root := cap.hps.system.sessions.get
        ⟨cap.hps.rootLabel, cap.hps.rootLabel_in_range⟩
      root.session.protocolLanguage = Fin4ZeroStarLanguage ∧
      root.session.protocolLanguage ≠ Set.univ ∧
      NerodePreserving Fin4ZeroStarLanguage
        root.config.antiEntropy.compress := by
  refine ⟨constrainedCapstoneFin4, ?_⟩
  change fin4ZeroStarSession.protocolLanguage = Fin4ZeroStarLanguage ∧
    fin4ZeroStarSession.protocolLanguage ≠ Set.univ ∧
    NerodePreserving Fin4ZeroStarLanguage fin4ZeroStarAntiEntropy.compress
  rw [fin4ZeroStarSession, Session.protocolLanguage, fin4ZeroProtocol_language]
  exact ⟨rfl, Fin4ZeroStarLanguage_nontrivial.2,
    fin4ZeroStarAntiEntropy_nerode⟩

/-- The semantic rule condition is definitionally the Nerode-preservation
condition for the concrete compression. -/
theorem constrained_rules_unmisunderstandable_iff_nerode :
    RuleUnmisunderstandable Fin4ZeroStarLanguage
      fin4ZeroStarAntiEntropy.compress ↔
      NerodePreserving Fin4ZeroStarLanguage
        fin4ZeroStarAntiEntropy.compress := by
  rfl

/-- Rules are unmisunderstandable for the concrete nontrivial language. -/
theorem constrained_rules_unmisunderstandable :
    RuleUnmisunderstandable Fin4ZeroStarLanguage
      fin4ZeroStarAntiEntropy.compress :=
  fin4ZeroStarAntiEntropy_nerode

/-- The concrete root language is not empty. -/
theorem constrainedCapstoneFin4_language_inhabited :
    ∅ ≠ constrainedCapstoneFin4.rootLanguage := by
  change ∅ ≠ fin4ZeroStarSession.protocolLanguage
  rw [fin4ZeroStarSession, Session.protocolLanguage, fin4ZeroProtocol_language]
  exact Ne.symm Fin4ZeroStarLanguage_nontrivial.1

/-- The concrete root language is neither empty nor universal. -/
theorem constrainedCapstoneFin4_language_nontrivial :
    constrainedCapstoneFin4.rootLanguage ≠ ∅ ∧
      constrainedCapstoneFin4.rootLanguage ≠ Set.univ := by
  change fin4ZeroStarSession.protocolLanguage ≠ ∅ ∧
    fin4ZeroStarSession.protocolLanguage ≠ Set.univ
  rw [fin4ZeroStarSession, Session.protocolLanguage, fin4ZeroProtocol_language]
  exact Fin4ZeroStarLanguage_nontrivial

/-- Barrier 4 immediately provides termination for any component of any
constrained capstone. -/
theorem ConstrainedCapstone.termination_general
    (cap : ConstrainedCapstone α) (state : ConstrainedRSIAState α)
    (hState : state ∈ cap.hps.system.sessions) :
    ∃ n : ℕ,
      (state.config.antiEntropy.compress^[n])
        state.session.environment.current = [] :=
  cap.barrier_termination state hState

end UAM_RSIA
