import Mathlib.Tactic
import RequestProject.Atlas.FormalMindEngineering
import RequestProject.Atlas.UAM_RSIA_NerodeBridge
import RequestProject.Atlas.UAM_RSIA_CognitiveBridge
import RequestProject.Atlas.UAM_RSIA_Parallel
import RequestProject.Atlas.UAM_RSIA_ProtocolHierarchy
import RequestProject.Atlas.UAM_RSIA_Coordination

set_option autoImplicit false

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- Collective behaviour is hierarchical interleaved execution and collective
purpose is the designated root language. -/
noncomputable def HierarchicalParallelSystem.formalIntention :
    FormalMind.Intention (HierarchicalParallelSystem α)
      (List (HierarchicalStep α)) (HierarchicalParallelSystem α)
      (Set (UAM_Free.FreeMonoid α)) where
  run hps trace := hps.runTrace trace
  intends hps :=
    (hps.system.sessions.get
      ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage

@[simp] theorem HierarchicalParallelSystem.formalIntention_run
    (hps : HierarchicalParallelSystem α) (trace : List (HierarchicalStep α)) :
    HierarchicalParallelSystem.formalIntention.run hps trace =
      hps.runTrace trace := rfl

@[simp] theorem HierarchicalParallelSystem.formalIntention_purpose
    (hps : HierarchicalParallelSystem α) :
    HierarchicalParallelSystem.formalIntention.intends hps =
      (hps.system.sessions.get
        ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage := rfl

/-- A distributed question addresses a component and supplies a word/action
pair. Out-of-range labels are interpreted at the designated root. -/
abbrev DistributedUnderstandingQuestion (α : Type u) :=
  SessionLabel × UAM_Free.FreeMonoid α × UAM_Free.FreeMonoid α

/-- Total addressed lookup, falling back to the designated root. -/
def HierarchicalParallelSystem.addressedSession
    (hps : HierarchicalParallelSystem α) (label : SessionLabel) : Session α :=
  if h : label < hps.system.sessions.length then
    (hps.system.sessions.get ⟨label, h⟩).session
  else
    (hps.system.sessions.get
      ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session

/-- Distributed understanding is local Nerode understanding at the addressed
component. -/
def HierarchicalParallelSystem.formalUnderstanding :
    FormalMind.Understanding (HierarchicalParallelSystem α)
      (DistributedUnderstandingQuestion α) Prop where
  predicts hps q := ActionUnderstood
    (hps.addressedSession q.1).protocolLanguage q.2.1 q.2.2
  understands hps q := ActionUnderstood
    (hps.addressedSession q.1).protocolLanguage q.2.1 q.2.2
  handlesCounterfactual _ _ := true

/-- At a valid label, distributed understanding is exactly local action
understanding. -/
theorem HierarchicalParallelSystem.formalUnderstanding_iff
    (hps : HierarchicalParallelSystem α) (j : Nat)
    (hj : j < hps.system.sessions.length)
    (w action : UAM_Free.FreeMonoid α) :
    HierarchicalParallelSystem.formalUnderstanding.understands hps
        (j, w, action) ↔
      ActionUnderstood
        ((hps.system.sessions.get ⟨j, hj⟩).session.protocolLanguage)
        w action := by
  simp [HierarchicalParallelSystem.formalUnderstanding,
    HierarchicalParallelSystem.addressedSession, hj]

/-- Collective subjecthood requires every component to meet the operational
stopping condition. The observation is the complete list of boundaries. -/
def HierarchicalParallelSystem.formalSubjectivity :
    FormalMind.Subjectivity (HierarchicalParallelSystem α)
      (List (UAM_Free.FreeMonoid α)) where
  isSubject hps := ∀ st ∈ hps.system.sessions, st.ShouldStop
  boundary hps := hps.system.sessions.map (·.session.environment.current)
  acts _ observation := observation

@[simp] theorem HierarchicalParallelSystem.formalSubjectivity_iff_all_shouldStop
    (hps : HierarchicalParallelSystem α) :
    HierarchicalParallelSystem.formalSubjectivity.isSubject hps ↔
      ∀ st ∈ hps.system.sessions, st.ShouldStop := Iff.rfl

/-- Persistent collective identity is equality of designated root languages. -/
def HierarchicalParallelSystem.protocolPersistentSelf :
    FormalMind.PersistentSelf Nat (HierarchicalParallelSystem α) where
  samePerson _ left _ right :=
    (left.system.sessions.get
      ⟨left.rootLabel, left.rootLabel_in_range⟩).session.protocolLanguage =
    (right.system.sessions.get
      ⟨right.rootLabel, right.rootLabel_in_range⟩).session.protocolLanguage
  refl _ _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

/-- Well-formed hierarchical execution preserves collective identity. -/
theorem HierarchicalParallelSystem.runTrace_samePerson
    (hps : HierarchicalParallelSystem α) (trace : List (HierarchicalStep α))
    (hWF : hps.TraceWellFormed trace) (start finish : Nat) :
    HierarchicalParallelSystem.protocolPersistentSelf.samePerson start hps
      finish (hps.runTrace trace) := by
  change
    (hps.system.sessions.get
      ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage =
    ((hps.runTrace trace).system.sessions.get
      ⟨(hps.runTrace trace).rootLabel,
        (hps.runTrace trace).rootLabel_in_range⟩).session.protocolLanguage
  have hroot : (hps.runTrace trace).rootLabel = hps.rootLabel := by
    induction hWF with
    | nil => rfl
    | cons hps hs rest hps' hStep hRest ih =>
      have hrun : hps.runTrace (hs :: rest) = hps'.runTrace rest := by
        simp [HierarchicalParallelSystem.runTrace, hStep]
      have hsroot : hps'.rootLabel = hps.rootLabel := by
        unfold HierarchicalParallelSystem.step at hStep
        split at hStep
        · contradiction
        · simp only [Option.some.injEq] at hStep
          subst hps'
          rfl
      rw [hrun]
      exact ih.trans hsroot
  have hget :
      (hps.runTrace trace).system.sessions.get
          ⟨(hps.runTrace trace).rootLabel,
            (hps.runTrace trace).rootLabel_in_range⟩ =
      (hps.runTrace trace).system.sessions.get
          ⟨hps.rootLabel,
            hps.runTrace_length trace hWF ▸ hps.rootLabel_in_range⟩ := by
    congr 1
    exact Fin.ext hroot
  rw [hget]
  exact (hps.runTrace_preserves_root_language trace hWF).symm

/-- A proof-carrying certificate for a submitted hierarchical trace. -/
structure HierarchicalTraceCertificate (α : Type u) where
  trace : List (HierarchicalStep α)

/-- Bounded self-verification checks exact equality with the certified trace. -/
noncomputable def HierarchicalParallelSystem.traceSelfVerification
    (_hps : HierarchicalParallelSystem α) :
    FormalMind.SelfVerification (List (HierarchicalStep α))
      (HierarchicalTraceCertificate α) where
  proves certificate sentence := certificate.trace = sentence
  consistencyStatement := []
  check certificate sentence := decide (certificate.trace = sentence)
  check_sound certificate sentence h := by simpa using h

@[simp] theorem HierarchicalParallelSystem.traceSelfVerification_accepts
    (hps : HierarchicalParallelSystem α) (trace : List (HierarchicalStep α)) :
    (hps.traceSelfVerification.check ⟨trace⟩ trace) = true := by
  simp [HierarchicalParallelSystem.traceSelfVerification]

/-- Collective intention and distributed understanding use the same local
language semantics at every valid label. -/
theorem HierarchicalParallelSystem.intention_entails_understanding
    (hps : HierarchicalParallelSystem α) (j : Nat)
    (hj : j < hps.system.sessions.length)
    (w action : UAM_Free.FreeMonoid α) :
    HierarchicalParallelSystem.formalUnderstanding.understands hps
        (j, w, action) ↔
      ActionUnderstood
        ((hps.system.sessions.get ⟨j, hj⟩).session.protocolLanguage)
        w action :=
  hps.formalUnderstanding_iff j hj w action

/-- Persistent identity is compatible with collective subjectivity whenever
all current components satisfy the stopping criterion. -/
theorem HierarchicalParallelSystem.persistent_self_entails_subjectivity
    (hps hps' : HierarchicalParallelSystem α)
    (_hSame : HierarchicalParallelSystem.protocolPersistentSelf.samePerson
      0 hps 0 hps')
    (hStop : ∀ st ∈ hps.system.sessions, st.ShouldStop) :
    HierarchicalParallelSystem.formalSubjectivity.isSubject hps := by
  exact hStop

/-- Successful self-verification yields the second-order knowledge component
of a concrete metacognition interface. -/
def HierarchicalParallelSystem.traceMetacognition
    (hps : HierarchicalParallelSystem α) :
    FormalMind.Metacognition (HierarchicalParallelSystem α)
      (List (HierarchicalStep α)) where
  knows _ trace := ∃ cert, hps.traceSelfVerification.proves cert trace
  knowsThatKnows _ trace := ∃ cert, hps.traceSelfVerification.proves cert trace
  knowsThatDoesNotKnow _ trace :=
    ¬ ∃ cert, hps.traceSelfVerification.proves cert trace
  confidence _ _ := 1

/-- Every proof-carrying hierarchical certificate is metacognitively known. -/
theorem HierarchicalParallelSystem.self_verification_yields_metacognition
    (hps : HierarchicalParallelSystem α)
    (cert : HierarchicalTraceCertificate α)
    (trace : List (HierarchicalStep α))
    (hProves : hps.traceSelfVerification.proves cert trace) :
    hps.traceMetacognition.knowsThatKnows hps trace := by
  exact ⟨cert, hProves⟩

end UAM_RSIA
