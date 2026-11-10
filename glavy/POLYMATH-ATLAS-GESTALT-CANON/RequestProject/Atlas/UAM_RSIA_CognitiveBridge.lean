import Mathlib.Tactic
import RequestProject.Atlas.FormalMindEngineering
import RequestProject.Atlas.UAM_RSIA_NerodeBridge
import RequestProject.Atlas.UAM_RSIA_VerifiedConstruction

set_option autoImplicit false

/-!
# Cognitive bridge: FormalMind and RSIA

This module gives concrete, discrete interpretations of several `FormalMind`
interfaces in the RSIA protocol engine.  The interpretations add no claim that
an automaton is phenomenally conscious: they identify the precise operational
content supplied by RSIA—protocol-relative understanding, intention,
subject-boundary behaviour, persistent protocol identity, and certified trace
verification.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- An RSIA session has an operational intention: applying an input word is its
behaviour, while its protocol language is the purpose that behaviour must
preserve. -/
def Session.formalIntention :
    FormalMind.Intention (Session α) (UAM_Free.FreeMonoid α)
      (UAM_Free.FreeMonoid α) (Set (UAM_Free.FreeMonoid α)) where
  run s action := s.environment.apply action
  intends s := s.protocolLanguage

@[simp] theorem Session.formalIntention_run (s : Session α)
    (action : UAM_Free.FreeMonoid α) :
    Session.formalIntention.run s action = s.environment.apply action := rfl

@[simp] theorem Session.formalIntention_purpose (s : Session α) :
    Session.formalIntention.intends s = s.protocolLanguage := rfl

/-- A question for the operational understanding interface consists of a
current word and a proposed action. -/
abbrev UnderstandingQuestion (α : Type u) :=
  UAM_Free.FreeMonoid α × UAM_Free.FreeMonoid α

/-- FormalMind understanding instantiated by the RSIA/Nerode semantics.  Its
answer says whether the action leaves the current word in the same observable
protocol class. -/
def Session.formalUnderstanding :
    FormalMind.Understanding (Session α) (UnderstandingQuestion α) Prop where
  predicts s question :=
    ActionUnderstood s.protocolLanguage question.1 question.2
  understands s question :=
    ActionUnderstood s.protocolLanguage question.1 question.2
  handlesCounterfactual _ _ := true

/-- In the bridge, FormalMind's understanding predicate is exactly RSIA's
protocol-relative action understanding. -/
theorem Session.formalUnderstanding_iff (s : Session α)
    (w action : UAM_Free.FreeMonoid α) :
    Session.formalUnderstanding.understands s (w, action) ↔
      ActionUnderstood s.protocolLanguage w action := by
  rfl

/-- Consequently, understanding at the live environment state is exactly
`ActionAligned`. -/
theorem Session.formalUnderstanding_iff_actionAligned (s : Session α)
    (action : UAM_Free.FreeMonoid α) :
    Session.formalUnderstanding.understands s
        (s.environment.current, action) ↔
      ActionAligned s.protocolLanguage s.environment.current action := by
  rfl

/-- The observable boundary of an RSIA state is its current stigmergic word;
acting at that boundary delegates to the session environment.  Operational
subjecthood is represented by the engine's certified stopping condition. -/
def RSIAState.formalSubjectivity :
    FormalMind.Subjectivity (RSIAState α) (UAM_Free.FreeMonoid α) where
  isSubject st := st.ShouldStop
  boundary st := st.session.environment.current
  acts st action := st.session.environment.apply action

@[simp] theorem RSIAState.formalSubjectivity_boundary (st : RSIAState α) :
    RSIAState.formalSubjectivity.boundary st =
      st.session.environment.current := rfl

/-- Operational subjecthood means that every active agent understands all of
its available protocol rules. -/
theorem RSIAState.formalSubjectivity_iff_agents_understand (st : RSIAState α) :
    RSIAState.formalSubjectivity.isSubject st ↔
      ∀ agent ∈ st.session.agents, agent.understandsRules st.session := by
  constructor
  · intro h agent hAgent
    exact (agent_understandsRules_iff_isNerodeCompatible agent st.session).mpr
      (h agent hAgent)
  · exact rules_impossible_to_misunderstand_preserves_language st

/-- Protocol identity supplies a persistent-self relation across engine time:
two states count as the same operational process exactly when they preserve the
same target language. -/
def RSIAState.protocolPersistentSelf :
    FormalMind.PersistentSelf Nat (RSIAState α) where
  samePerson _ left _ right :=
    left.initialLanguage = right.initialLanguage
  refl _ _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

/-- Any finite RSIA execution is the same protocol-relative operational self as
its starting state. -/
theorem RSIAState.runInstructions_samePerson (st : RSIAState α)
    (instructions : List (RoundInstruction α)) (start finish : Nat) :
    RSIAState.protocolPersistentSelf.samePerson start st finish
      (st.runInstructions instructions) := by
  change st.initialLanguage = (st.runInstructions instructions).initialLanguage
  induction instructions generalizing st with
  | nil => rfl
  | cons instruction rest ih =>
      cases instruction with
      | «continue» =>
          change st.initialLanguage =
            (st.runContinueRound.runInstructions rest).initialLanguage
          exact ih st.runContinueRound
      | exitClean exit =>
          change st.initialLanguage =
            ((st.runExitCleanRound exit).runInstructions rest).initialLanguage
          exact ih (st.runExitCleanRound exit)
      | exitFork exit =>
          change st.initialLanguage =
            ((st.runForkRound exit).runInstructions rest).initialLanguage
          exact ih (st.runForkRound exit)

/-- A trace certificate packages a trace together with a kernel-checked proof
that every step preserves the chosen protocol's Nerode class. -/
abbrev AlignedTraceCertificate (L : Set (UAM_Free.FreeMonoid α)) :=
  {trace : StigmergicTrace α // StigmergicTrace.aligned L trace}

/-- FormalMind self-verification instantiated by RSIA trace verification.
Certificates are proof-carrying aligned traces; the checker verifies that a
certificate is for the submitted trace. -/
noncomputable def traceSelfVerification
    (L : Set (UAM_Free.FreeMonoid α)) :
    FormalMind.SelfVerification (StigmergicTrace α)
      (AlignedTraceCertificate L) where
  proves certificate sentence := certificate.1 = sentence
  consistencyStatement := .empty
  check certificate sentence := decide (certificate.1 = sentence)
  check_sound certificate sentence h := by
    simpa using h

/-- A verified construction directly yields a successful FormalMind
certificate for its actual construction trace. -/
theorem VerifiedConstruction.formal_self_verified
    (v : VerifiedConstruction α) :
    (traceSelfVerification v.session.protocolLanguage).proves
      ⟨v.trace, v.aligned⟩ v.trace := by
  rfl

/-- The executable checker accepts the certificate extracted from a verified
construction. -/
theorem VerifiedConstruction.formal_self_check
    (v : VerifiedConstruction α) :
    (traceSelfVerification v.session.protocolLanguage).check
      ⟨v.trace, v.aligned⟩ v.trace = true := by
  simp [traceSelfVerification]

end UAM_RSIA
