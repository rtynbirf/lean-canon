import RequestProject.Atlas.FormalMindEngineering

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Канонический словарь IdealAI

Этот модуль содержит единственные канонические версии типов, которые раньше имели
параллельные имена с суффиксами `_` и `__`. Интеграционные модули используют именно
эти версии.
-/

namespace IdealAI

inductive ComputeMode
  | local | toolAssisted | distributed
  deriving DecidableEq, Repr

inductive InteractionMode
  | dialogue | autonomous | collaborative
  deriving DecidableEq, Repr

inductive TransparencyLevel
  | opaque | summary | auditable
  deriving DecidableEq, Repr

/-- Типы предметной области, общие для всех интегрированных интерфейсов. -/
structure Vocabulary where
  System : Type
  Human : Type
  Observation : Type
  defaultObservation : Observation
  Claim : Type
  Evidence : Type
  Context : Type
  Idea : Type
  Example : Type
  Query : Type
  Answer : Type
  Module : Type
  ModuleState : Type
  Time : Type
  Action : Type
  Tool : Type
  Agent : Type
  Input : Type
  Label : Type
  Goal : Type
  World : Type
  Node : Type
  Edge : Type
  Tone : Type

structure CreativeRecombination (Context Idea : Type*) where
  components : Context → List Idea
  recombine : Context → Idea

structure SemanticGraph (Node Edge : Type*) where
  vertices : Set Node
  edges : Edge → Node × Node

structure UserInterface (Input Output Tone : Type*) where
  respond : Input → Output
  tone : Input → Tone

structure InternalGoal (State Goal : Type*) where
  initialGoal : Goal
  generate : State → Goal
  retained : State → Goal → Prop

structure ObjectiveFunction (State Action Score : Type*) where
  score : State → Action → Score
  choose : State → Action

structure Domain (Object : Type*) where
  contains : Object → Prop

/-- A creative-recombination component is directly a creativity model. -/
def CreativeRecombination.toCreativity {C I : Type*}
    (R : CreativeRecombination C I) : FormalMind.Creativity I C where
  produces := R.recombine
  seenBefore := fun c i => i ∈ R.components c
  valuable := fun _ => True

/-- An internal goal generator supplies the generative part of autonomous goals. -/
def InternalGoal.toAutonomousGoals {S G : Type*} (I : InternalGoal S G) :
    FormalMind.AutonomousGoals S G where
  initialGoal := I.initialGoal
  generate := fun s _ => I.generate s
  fundamental := fun g => ∃ s, I.retained s g

/-- A user interface supplies the observable interface of a subjectivity model. -/
def UserInterface.toSubjectivity {I O T : Type*} (U : UserInterface I O T) :
    FormalMind.Subjectivity I O where
  isSubject := fun _ => True
  boundary := U.respond
  acts := fun i _ => U.respond i

end IdealAI
