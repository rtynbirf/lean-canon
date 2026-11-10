import Mathlib
import RequestProject.Atlas.FormalMindEngineering
import RequestProject.Atlas.IdealAI
import RequestProject.Atlas.Stubs_Core
import RequestProject.Atlas.Stubs_OpenProblems

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Positive interrelations between FormalMind structures

All bridges are parameterized.  Their hypotheses state the compatibility needed
between independently specified concept structures; no global principle is
postulated.
-/

namespace FormalMind.Interrelations

/-- Knowledge combines first-order knowing with a justification relation. -/
structure Knowledge (State Claim Justification : Type*) where
  metacognition : FormalMind.Metacognition State Claim
  justified : State → Claim → Justification → Prop
  knows_justified : ∀ {state claim}, metacognition.knows state claim →
    ∃ reason, justified state claim reason

/-- A confidence score is calibrated when confidence one entails knowledge and
confidence zero entails acknowledged ignorance. -/
def ConfidenceCalibrated {State Claim : Type*}
    (model : FormalMind.Metacognition State Claim) : Prop :=
  ∀ state claim,
    (model.confidence state claim = 1 → model.knows state claim) ∧
    (model.confidence state claim = 0 → model.knowsThatDoesNotKnow state claim)

/-- Uncertainty is represented by the complement of confidence. -/
def uncertainty {State Claim : Type*}
    (model : FormalMind.Metacognition State Claim) (state : State) (claim : Claim) : Rat :=
  1 - model.confidence state claim

/-- Full confidence has zero quantified uncertainty. -/
theorem uncertainty_eq_zero_of_confidence_one {State Claim : Type*}
    (model : FormalMind.Metacognition State Claim) {state : State} {claim : Claim}
    (confidence : model.confidence state claim = 1) :
    uncertainty model state claim = 0 := by
  simp [uncertainty, confidence]

/-- Knowing the claim attached to one's current observation, together with a
sound evidence bridge, yields consciousness. -/
theorem metacognition_strengthens_consciousness
    {State Observation Claim : Type*}
    (consciousness : FormalMind.Consciousness State Observation)
    (metacognition : FormalMind.Metacognition State Claim)
    (claimOf : Observation → Claim) (state : State)
    (knowsObservation : metacognition.knows state (claimOf (consciousness.observe state)))
    (knowledge_is_evidence : metacognition.knows state (claimOf (consciousness.observe state)) →
      consciousness.evidence (consciousness.observe state)) :
    consciousness.conscious state := by
  exact consciousness.evidence_sound state (knowledge_is_evidence knowsObservation)

/-- A novel product predicted by an understanding model is valuable whenever
correctly predicted novel products satisfy the supplied value criterion. -/
theorem creativity_understanding_value
    {Artifact Context System Question : Type*}
    (creativity : FormalMind.Creativity Artifact Context)
    (understanding : FormalMind.Understanding System Question Artifact)
    (context : Context) (system : System) (question : Question)
    (novel : creativity.novel context (creativity.produces context))
    (prediction : understanding.predicts system question = creativity.produces context)
    (understood : understanding.understands system question)
    (soundValue : understanding.understands system question →
      creativity.novel context (understanding.predicts system question) →
      creativity.valuable (understanding.predicts system question)) :
    creativity.valuable (creativity.produces context) := by
  rw [← prediction]
  apply soundValue understood
  rwa [prediction]

/-- A volition proposal realizes autonomous goal generation when the two goal
interfaces are compatible. -/
theorem volition_realizes_autonomous_goal
    {State Goal Action : Type*}
    (volition : FormalMind.Volition State Goal Action)
    (autonomy : FormalMind.AutonomousGoals State Goal)
    (state : State) (seed : Goal)
    (generation_agrees : autonomy.generate state seed = volition.proposesGoal state)
    (proposal_wanted : volition.wants state (volition.proposesGoal state)) :
    autonomy.generate state seed = volition.proposesGoal state ∧
      volition.wants state (autonomy.generate state seed) := by
  constructor
  · exact generation_agrees
  · rwa [generation_agrees]

/-- Objective denotation yields correspondence through a parameterized bridge
between a meaning model and a truth model. -/
theorem meaning_objectivity_implies_truth
    {Agent Symbol World : Type*}
    (meaning : FormalMind.Meaning Agent Symbol World)
    (truth : FormalMind.Truth World Symbol)
    (agent : Agent) (symbol : Symbol)
    (objective : meaning.objective symbol (meaning.denotes agent symbol))
    (objective_corresponds : ∀ world,
      meaning.objective symbol world → truth.corresponds world symbol) :
    truth.corresponds (meaning.denotes agent symbol) symbol := by
  exact objective_corresponds _ objective

/-- When experience determines observation, evidence for that experience can
be transported to the consciousness interface. -/
theorem qualia_strengthens_consciousness
    {System Experience Report Observation : Type*}
    (qualia : FormalMind.Qualia System Experience Report)
    (consciousness : FormalMind.Consciousness System Observation)
    (observationOf : Experience → Observation) (system : System)
    (observation_agrees : observationOf (qualia.experience system) =
      consciousness.observe system)
    (experience_evidence : consciousness.evidence
      (observationOf (qualia.experience system))) :
    consciousness.conscious system := by
  apply consciousness.evidence_sound system
  rwa [← observation_agrees]

/-! ## Bridges to IdealAI -/

/-- Successful IdealAI fact checking can be used as first-order metacognitive
knowledge through an explicit evidence selector. -/
theorem factCheck_to_metacognition
    (vocabulary : IdealAI.Vocabulary)
    (theory : IdealAI.Core.AxiomSet vocabulary)
    (metacognition : FormalMind.Metacognition vocabulary.System vocabulary.Claim)
    (evidenceFor : vocabulary.System → vocabulary.Claim → vocabulary.Evidence)
    (sound : ∀ state claim,
      theory.factCheck claim (evidenceFor state claim) → metacognition.knows state claim)
    {state : vocabulary.System} {claim : vocabulary.Claim}
    (checked : theory.factCheck claim (evidenceFor state claim)) :
    metacognition.knows state claim := by
  exact sound state claim checked

/-- The creativity bridge in `AxiomSet` produces exactly the recombined idea. -/
theorem theory_creativity_produces
    (vocabulary : IdealAI.Vocabulary)
    (theory : IdealAI.Core.AxiomSet vocabulary) (context : vocabulary.Context) :
    (theory.creativity).produces context = theory.creative.recombine context := by
  rfl

/-- The open IdealAI consciousness model is conscious whenever its default
observation satisfies its evidence predicate. -/
theorem openAxiomSet_evidence_conscious
    (vocabulary : IdealAI.Vocabulary)
    (theory : IdealAI.OpenProblems.OpenAxiomSet vocabulary)
    (system : vocabulary.System)
    (evidence : (theory.consciousness).evidence
      ((theory.consciousness).observe system)) :
    (theory.consciousness).conscious system := by
  exact (theory.consciousness).evidence_sound system evidence

end FormalMind.Interrelations
