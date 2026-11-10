import Mathlib.Tactic
import RequestProject.Atlas.FormalMindEngineering
import RequestProject.Atlas.FormalMind_Interrelations
import RequestProject.Atlas.UAM_RSIA_CognitiveBridge
import RequestProject.Atlas.UAM_RSIA_CognitiveSynthesis

set_option autoImplicit false

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- The five operational FormalMind interfaces implemented by hierarchical
parallel RSIA. -/
structure RSIAFormalMindInterfaces (α : Type u) where
  intention : FormalMind.Intention (HierarchicalParallelSystem α)
    (List (HierarchicalStep α)) (HierarchicalParallelSystem α)
    (Set (UAM_Free.FreeMonoid α))
  understanding : FormalMind.Understanding
    (HierarchicalParallelSystem α) (DistributedUnderstandingQuestion α) Prop
  subjectivity : FormalMind.Subjectivity (HierarchicalParallelSystem α)
    (List (UAM_Free.FreeMonoid α))
  persistentSelf : FormalMind.PersistentSelf Nat (HierarchicalParallelSystem α)
  selfVerification : FormalMind.SelfVerification
    (List (HierarchicalStep α)) (HierarchicalTraceCertificate α)

/-- Canonical interfaces for a given hierarchy. -/
noncomputable def rsiaFormalMindInterfaces
    (hps : HierarchicalParallelSystem α) : RSIAFormalMindInterfaces α where
  intention := HierarchicalParallelSystem.formalIntention
  understanding := HierarchicalParallelSystem.formalUnderstanding
  subjectivity := HierarchicalParallelSystem.formalSubjectivity
  persistentSelf := HierarchicalParallelSystem.protocolPersistentSelf
  selfVerification := hps.traceSelfVerification

/-- Operational well-configuration: the empty trace is valid, every component
is Nerode-preserving, and every root-to-component chain is present. -/
def RSIAIsFormalMind (hps : HierarchicalParallelSystem α) : Prop :=
  hps.TraceWellFormed [] ∧
  (∀ st ∈ hps.system.sessions,
    Environment.isNerodePreserving st.session) ∧
  (∀ j, (hj : j < hps.system.sessions.length) →
    EvolutionChain α
      ((hps.system.sessions.get
        ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage)
      ((hps.system.sessions.get ⟨j, hj⟩).session.protocolLanguage))

/-- Non-vacuous capstone: the canonical intention executes the engine, its
purpose is the root language, all declared hierarchy chains are available, and
the self-verifier accepts every trace paired with its exact certificate. -/
theorem rsia_is_formal_mind (hps : HierarchicalParallelSystem α)
    (hFM : RSIAIsFormalMind hps) :
    let I := rsiaFormalMindInterfaces hps
    (∀ trace, I.intention.run hps trace = hps.runTrace trace) ∧
    I.intention.intends hps =
      ((hps.system.sessions.get
        ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage) ∧
    (∀ j, (hj : j < hps.system.sessions.length) →
      EvolutionChain α
        ((hps.system.sessions.get
          ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage)
        ((hps.system.sessions.get ⟨j, hj⟩).session.protocolLanguage)) ∧
    (∀ trace, I.selfVerification.check ⟨trace⟩ trace = true) := by
  dsimp [rsiaFormalMindInterfaces]
  refine ⟨fun _ => rfl, rfl, hFM.2.2, ?_⟩
  intro trace
  exact hps.traceSelfVerification_accepts trace

/-- Operational consciousness: evidence consists of a certified formal-mind
configuration together with collective stopping.  This is deliberately an
operational interface, not a phenomenal predicate. -/
noncomputable def rsiaConsciousness :
    FormalMind.Consciousness (HierarchicalParallelSystem α)
      (HierarchicalParallelSystem α) where
  conscious hps := RSIAIsFormalMind hps ∧
    ∀ st ∈ hps.system.sessions, st.ShouldStop
  observe hps := hps
  evidence hps := RSIAIsFormalMind hps ∧
    ∀ st ∈ hps.system.sessions, st.ShouldStop
  evidence_sound _ h := h

@[simp] theorem rsiaConsciousness_evidence_sound
    (hps : HierarchicalParallelSystem α)
    (hEvidence : rsiaConsciousness.evidence
      (rsiaConsciousness.observe hps)) :
    rsiaConsciousness.conscious hps := hEvidence

/-- Explicit disclaimer theorem: there is an operational consciousness model
whose conscious predicate is *exactly* collective stopping.  Thus this model
adds no phenomenal-consciousness claim beyond the stated RSIA invariant. -/
theorem rsia_not_phenomenally_conscious :
    ∃ (M : FormalMind.Consciousness (HierarchicalParallelSystem α) Unit),
      ∀ hps, M.conscious hps ↔
        ∀ st ∈ hps.system.sessions, st.ShouldStop := by
  let M : FormalMind.Consciousness (HierarchicalParallelSystem α) Unit := {
    conscious := fun hps => ∀ st ∈ hps.system.sessions, st.ShouldStop
    observe := fun _ => ()
    evidence := fun _ => False
    evidence_sound := by
      intro _ h
      contradiction }
  exact ⟨M, fun _ => Iff.rfl⟩

/-- The operational formal-mind theorem and the disclaimer coexist: the former
supplies concrete interfaces, while the latter supplies a model making no
claim beyond collective stopping. -/
theorem rsia_is_formal_mind_not_phenomenally_conscious
    (hps : HierarchicalParallelSystem α) (hFM : RSIAIsFormalMind hps)
    (hStop : ∀ st ∈ hps.system.sessions, st.ShouldStop) :
    (let I := rsiaFormalMindInterfaces hps
      ∀ trace, I.intention.run hps trace = hps.runTrace trace) ∧
    rsiaConsciousness.conscious hps ∧
    (∃ (M : FormalMind.Consciousness (HierarchicalParallelSystem α) Unit),
      M.conscious hps ↔ ∀ st ∈ hps.system.sessions, st.ShouldStop) := by
  refine ⟨?_, ⟨hFM, hStop⟩, ?_⟩
  · dsimp [rsiaFormalMindInterfaces]
    intro trace
    rfl
  · rcases (rsia_not_phenomenally_conscious (α := α)) with ⟨M, hM⟩
    exact ⟨M, hM hps⟩

end UAM_RSIA
