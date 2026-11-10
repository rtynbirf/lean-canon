import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_ConstrainedCapstone
import RequestProject.Atlas.UAM_RSIA_FinalBridge

set_option autoImplicit false

/-!
# Non-vacuous formal mind in the constrained architecture

This file equips constrained hierarchical parallel systems with the five
operational `FormalMind` interfaces.  It then packages the concrete `Fin 4`
zero-star construction, whose root language is neither empty nor universal.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- A constrained state should stop when every active agent is compatible with
its session's Nerode semantics. -/
def ConstrainedRSIAState.ShouldStop (st : ConstrainedRSIAState α) : Prop :=
  ∀ agent ∈ st.session.agents, Agent.isNerodeCompatible st.session agent

/-- Total addressed lookup, falling back to the designated root. -/
def ConstrainedHierarchicalParallelSystem.addressedConstrainedSession
    (hps : ConstrainedHierarchicalParallelSystem α) (label : SessionLabel) :
    Session α :=
  if h : label < hps.system.sessions.length then
    (hps.system.sessions.get ⟨label, h⟩).session
  else
    (hps.system.sessions.get
      ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session

/-- Static intention: the system is unchanged and intends its root language. -/
noncomputable def ConstrainedHierarchicalParallelSystem.constrainedFormalIntention :
    FormalMind.Intention (ConstrainedHierarchicalParallelSystem α)
      Unit (ConstrainedHierarchicalParallelSystem α)
      (Set (UAM_Free.FreeMonoid α)) where
  run hps _ := hps
  intends hps :=
    (hps.system.sessions.get
      ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage

/-- Distributed understanding is Nerode understanding at the addressed
component. -/
def ConstrainedHierarchicalParallelSystem.constrainedFormalUnderstanding :
    FormalMind.Understanding (ConstrainedHierarchicalParallelSystem α)
      (SessionLabel × UAM_Free.FreeMonoid α × UAM_Free.FreeMonoid α) Prop where
  predicts hps q := ActionUnderstood
    (hps.addressedConstrainedSession q.1).protocolLanguage q.2.1 q.2.2
  understands hps q := ActionUnderstood
    (hps.addressedConstrainedSession q.1).protocolLanguage q.2.1 q.2.2
  handlesCounterfactual _ _ := true

/-- Collective subjecthood is the stopping condition for every component. -/
def ConstrainedHierarchicalParallelSystem.constrainedFormalSubjectivity :
    FormalMind.Subjectivity (ConstrainedHierarchicalParallelSystem α)
      (List (UAM_Free.FreeMonoid α)) where
  isSubject hps := ∀ st ∈ hps.system.sessions, st.ShouldStop
  boundary hps := hps.system.sessions.map (·.session.environment.current)
  acts _ observation := observation

/-- Persistent collective identity is equality of designated root languages. -/
def ConstrainedHierarchicalParallelSystem.constrainedProtocolPersistentSelf :
    FormalMind.PersistentSelf Nat (ConstrainedHierarchicalParallelSystem α) where
  samePerson _ left _ right :=
    (left.system.sessions.get
      ⟨left.rootLabel, left.rootLabel_in_range⟩).session.protocolLanguage =
    (right.system.sessions.get
      ⟨right.rootLabel, right.rootLabel_in_range⟩).session.protocolLanguage
  refl _ _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

/-- A proof-carrying certificate for a submitted constrained trace. -/
structure ConstrainedTraceCertificate (α : Type u) where
  trace : List Unit

/-- Bounded self-verification checks exact equality with the certified trace. -/
noncomputable def
    ConstrainedHierarchicalParallelSystem.constrainedTraceSelfVerification
    (_hps : ConstrainedHierarchicalParallelSystem α) :
    FormalMind.SelfVerification (List Unit) (ConstrainedTraceCertificate α) where
  proves certificate sentence := certificate.trace = sentence
  consistencyStatement := []
  check certificate sentence := decide (certificate.trace = sentence)
  check_sound certificate sentence h := by simpa using h

@[simp] theorem
    ConstrainedHierarchicalParallelSystem.constrainedFormalIntention_run
    (hps : ConstrainedHierarchicalParallelSystem α) :
    constrainedFormalIntention.run hps () = hps := rfl

@[simp] theorem
    ConstrainedHierarchicalParallelSystem.constrainedFormalIntention_intends
    (hps : ConstrainedHierarchicalParallelSystem α) :
    constrainedFormalIntention.intends hps =
      (hps.system.sessions.get
        ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage := rfl

@[simp] theorem
    ConstrainedHierarchicalParallelSystem.constrainedFormalSubjectivity_iff
    (hps : ConstrainedHierarchicalParallelSystem α) :
    constrainedFormalSubjectivity.isSubject hps ↔
      ∀ st ∈ hps.system.sessions, st.ShouldStop := Iff.rfl

@[simp] theorem
    ConstrainedHierarchicalParallelSystem.constrainedTraceSelfVerification_accepts
    (hps : ConstrainedHierarchicalParallelSystem α) (trace : List Unit) :
    (hps.constrainedTraceSelfVerification.check ⟨trace⟩ trace) = true := by
  simp [ConstrainedHierarchicalParallelSystem.constrainedTraceSelfVerification]

/-- The five constrained formal-mind interfaces bundled together. -/
structure ConstrainedFormalMindInterfaces (α : Type u) where
  intention : FormalMind.Intention (ConstrainedHierarchicalParallelSystem α)
    Unit (ConstrainedHierarchicalParallelSystem α)
    (Set (UAM_Free.FreeMonoid α))
  understanding : FormalMind.Understanding
    (ConstrainedHierarchicalParallelSystem α)
    (SessionLabel × UAM_Free.FreeMonoid α × UAM_Free.FreeMonoid α) Prop
  subjectivity : FormalMind.Subjectivity
    (ConstrainedHierarchicalParallelSystem α)
    (List (UAM_Free.FreeMonoid α))
  persistentSelf : FormalMind.PersistentSelf Nat
    (ConstrainedHierarchicalParallelSystem α)
  selfVerification : FormalMind.SelfVerification (List Unit)
    (ConstrainedTraceCertificate α)

/-- Canonical constrained interfaces for a given hierarchy. -/
noncomputable def constrainedFormalMindInterfaces
    (hps : ConstrainedHierarchicalParallelSystem α) :
    ConstrainedFormalMindInterfaces α where
  intention :=
    ConstrainedHierarchicalParallelSystem.constrainedFormalIntention
  understanding :=
    ConstrainedHierarchicalParallelSystem.constrainedFormalUnderstanding
  subjectivity :=
    ConstrainedHierarchicalParallelSystem.constrainedFormalSubjectivity
  persistentSelf :=
    ConstrainedHierarchicalParallelSystem.constrainedProtocolPersistentSelf
  selfVerification := hps.constrainedTraceSelfVerification

/-- The constrained formal-mind condition uses only each stored session's local
Nerode-preservation invariant. -/
def ConstrainedRSIAIsFormalMind
    (hps : ConstrainedHierarchicalParallelSystem α) : Prop :=
  ∀ state ∈ hps.system.sessions,
    Environment.isLocallyNerodePreserving state.session

/-- The concrete zero-star hierarchy satisfies the constrained formal-mind
condition. -/
theorem instConstrainedHPSFin4_isFormalMind :
    ConstrainedRSIAIsFormalMind instConstrainedHPSFin4 := by
  intro state hState
  simp only [instConstrainedHPSFin4, fin4ZeroStarConstrainedParallel,
    List.mem_singleton] at hState
  subst state
  exact fin4ZeroStarSession_localNerode

/-- The concrete constrained capstone's root language is `0*`. -/
theorem constrainedFormalMindFin4_rootLanguage :
    constrainedCapstoneFin4.rootLanguage = Fin4ZeroStarLanguage := by
  change fin4ZeroStarSession.protocolLanguage = Fin4ZeroStarLanguage
  rw [fin4ZeroStarSession, Session.protocolLanguage, fin4ZeroProtocol_language]

/-- The concrete constrained formal mind has a nontrivial language. -/
theorem constrainedFormalMindFin4_nontrivial :
    constrainedCapstoneFin4.rootLanguage ≠ ∅ ∧
      constrainedCapstoneFin4.rootLanguage ≠ Set.univ :=
  constrainedCapstoneFin4_language_nontrivial

/-- The canonical constrained interfaces expose root intention, collective
stopping, and exact certificate checking. -/
theorem constrained_rsia_is_formal_mind
    (hps : ConstrainedHierarchicalParallelSystem α)
    (_hFM : ConstrainedRSIAIsFormalMind hps) :
    let I := constrainedFormalMindInterfaces hps
    I.intention.intends hps =
      (hps.system.sessions.get
        ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage ∧
    (I.subjectivity.isSubject hps ↔
      ∀ st ∈ hps.system.sessions, st.ShouldStop) ∧
    (∀ trace : List Unit,
      I.selfVerification.check ⟨trace⟩ trace = true) := by
  dsimp [constrainedFormalMindInterfaces,
    ConstrainedHierarchicalParallelSystem.constrainedFormalIntention,
    ConstrainedHierarchicalParallelSystem.constrainedFormalSubjectivity]
  refine ⟨rfl, Iff.rfl, ?_⟩
  intro trace
  simp [ConstrainedHierarchicalParallelSystem.constrainedTraceSelfVerification]

/-- Operational consciousness for the constrained architecture. -/
noncomputable def constrainedConsciousness :
    FormalMind.Consciousness (ConstrainedHierarchicalParallelSystem α)
      (ConstrainedHierarchicalParallelSystem α) where
  conscious hps := ConstrainedRSIAIsFormalMind hps ∧
    ∀ st ∈ hps.system.sessions, st.ShouldStop
  observe hps := hps
  evidence hps := ConstrainedRSIAIsFormalMind hps ∧
    ∀ st ∈ hps.system.sessions, st.ShouldStop
  evidence_sound _ h := h

@[simp] theorem constrainedConsciousness_evidence_sound
    (hps : ConstrainedHierarchicalParallelSystem α)
    (hEvidence : constrainedConsciousness.evidence
      (constrainedConsciousness.observe hps)) :
    constrainedConsciousness.conscious hps := hEvidence

/-- This operational model makes no claim beyond collective stopping. -/
theorem constrained_not_phenomenally_conscious :
    ∃ (M : FormalMind.Consciousness
      (ConstrainedHierarchicalParallelSystem α) Unit),
      ∀ hps, M.conscious hps ↔
        ∀ st ∈ hps.system.sessions, st.ShouldStop := by
  let M : FormalMind.Consciousness
      (ConstrainedHierarchicalParallelSystem α) Unit := {
    conscious := fun hps => ∀ st ∈ hps.system.sessions, st.ShouldStop
    observe := fun _ => ()
    evidence := fun _ => False
    evidence_sound := by
      intro _ h
      contradiction }
  exact ⟨M, fun _ => Iff.rfl⟩

/-- Complete constrained package, including a concrete formal mind with a
nonempty, non-universal root language. -/
structure ConstrainedFinalPackage (α : Type u) where
  biconditional : ∀ (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α),
    RuleUnmisunderstandable L f ↔ NerodePreserving L f
  barrier : EpistemicBarrier α
  constrainedFormalMind : ∃ (cap : ConstrainedCapstone α),
    ConstrainedRSIAIsFormalMind cap.hps ∧
    cap.rootLanguage ≠ ∅ ∧ cap.rootLanguage ≠ Set.univ
  phenomenalDisclaimer :
    ∃ C : FormalMind.Consciousness
      (ConstrainedHierarchicalParallelSystem α) Unit,
      ∀ hps, C.conscious hps ↔
        ∀ st ∈ hps.system.sessions, st.ShouldStop

/-- The concrete complete package over `Fin 4`. -/
noncomputable def constrainedFinalPackageFin4 :
    ConstrainedFinalPackage (Fin 4) where
  biconditional := ruleUnmisunderstandable_iff_nerodePreserving
  barrier := epistemicBarrier
  constrainedFormalMind := by
    refine ⟨constrainedCapstoneFin4,
      instConstrainedHPSFin4_isFormalMind, ?_⟩
    exact constrainedCapstoneFin4_language_nontrivial
  phenomenalDisclaimer := constrained_not_phenomenally_conscious

/-- The constrained final package exists over `Fin 4`. -/
theorem constrainedFinalPackageFin4_nonempty :
    Nonempty (ConstrainedFinalPackage (Fin 4)) :=
  ⟨constrainedFinalPackageFin4⟩

/-- The project closes with a concrete constrained formal-mind package and a
capstone whose root language is nontrivial and whose compression preserves
Nerode meaning. -/
theorem constrained_rsia_project_nonvacuous_closed :
    Nonempty (ConstrainedFinalPackage (Fin 4)) ∧
    ∃ (cap : ConstrainedCapstone (Fin 4)),
      cap.rootLanguage ≠ ∅ ∧ cap.rootLanguage ≠ Set.univ ∧
      RuleUnmisunderstandable cap.rootLanguage cap.rootCompress := by
  refine ⟨⟨constrainedFinalPackageFin4⟩,
    ⟨constrainedCapstoneFin4,
      constrainedCapstoneFin4_language_nontrivial.1,
      constrainedCapstoneFin4_language_nontrivial.2, ?_⟩⟩
  rw [constrainedFormalMindFin4_rootLanguage]
  change RuleUnmisunderstandable Fin4ZeroStarLanguage
    fin4ZeroStarAntiEntropy.compress
  exact constrained_rules_unmisunderstandable

end UAM_RSIA
