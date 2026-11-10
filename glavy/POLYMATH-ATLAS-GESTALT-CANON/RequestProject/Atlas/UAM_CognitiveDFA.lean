import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_DFAEval
import RequestProject.Atlas.UAM_MonoidAction
import RequestProject.Atlas.UnifiedModel

/-!
# Finite cognitive models as deterministic automata

A finite cognitive state space equipped with encoded monoid actions gives a DFA.
The action convention agrees with the project convention `a * b` = first `a`,
then `b`.
-/

namespace UAM_CognitiveDFA
universe u

/-- The finite, DFA-relevant part of a cognitive model. -/
structure CognitiveModel (α : Type u) where
  M : Type u
  instM : Monoid M
  instFintypeM : Fintype M
  X : Type u
  instDecX : DecidableEq X
  instFintypeX : Fintype X
  instDecA : DecidableEq α
  instFintypeA : Fintype α
  action : letI := instM; UAM_MonoidAction.MonoidAction M X
  encode : α → M
  initial : X
  accepting : Set X

attribute [instance] CognitiveModel.instM CognitiveModel.instFintypeM
  CognitiveModel.instDecX CognitiveModel.instFintypeX CognitiveModel.instDecA
  CognitiveModel.instFintypeA

/-- The canonical DFA induced by a finite cognitive model. -/
def cognitiveToDFA {α : Type u} (C : CognitiveModel α) :
    UAM_DFAEval.DFA α C.X where
  δ := fun q a => C.action.act (C.encode a) q
  q₀ := C.initial
  F := C.accepting

/-- Evaluation of the induced DFA is evaluation of the encoded word action. -/
theorem cognitive_evalFrom {α : Type u} (C : CognitiveModel α)
    (q : C.X) (w : UAM_Free.FreeMonoid α) :
    (cognitiveToDFA C).evalFrom q w =
      C.action.act ((UAM_Free.FreeMonoid.lift C.encode).toFun w) q := by
  induction w generalizing q with
  | nil =>
      exact (UAM_MonoidAction.MonoidAction.act_one_apply C.action q).symm
  | cons a w ih =>
      change (cognitiveToDFA C).evalFrom ((cognitiveToDFA C).δ q a) w = _
      rw [ih]
      exact (UAM_MonoidAction.MonoidAction.act_mul_apply C.action
        (C.encode a) ((UAM_Free.FreeMonoid.lift C.encode).toFun w) q).symm

/-- A finite cognitive model and its canonical DFA accept exactly the same words. -/
theorem cognitive_model_dfa_equiv {α : Type u} (C : CognitiveModel α) :
    (cognitiveToDFA C).language =
      {w | C.action.act ((UAM_Free.FreeMonoid.lift C.encode).toFun w) C.initial ∈
        C.accepting} := by
  ext w
  change (cognitiveToDFA C).evalFrom C.initial w ∈ C.accepting ↔ _
  rw [cognitive_evalFrom]
  rfl

/-- A unified model becomes a finite cognitive model after choosing a finite
alphabet, an encoding by transformations, and an accepting set. -/
def cognitiveOfUnified {α : Type} [DecidableEq α] [Fintype α]
    (n : Nat) [NeZero n] (U : UnifiedModel.UnifiedAgentModel n)
    (encode : α → UnifiedModel.Transform n)
    (accepting : Set (UnifiedModel.State n)) : CognitiveModel α where
  M := UnifiedModel.Transform n
  instM := UAM_Action.instMonoid
  instFintypeM := inferInstance
  X := UnifiedModel.State n
  instDecX := inferInstance
  instFintypeX := inferInstance
  instDecA := inferInstance
  instFintypeA := inferInstance
  action := U.mentalAction
  encode := encode
  initial := UnifiedModel.initial n
  accepting := accepting

/-- The DFA extracted from a unified model has the expected transition rule. -/
theorem cognitiveOfUnified_transition {α : Type} [DecidableEq α] [Fintype α]
    (n : Nat) [NeZero n] (U : UnifiedModel.UnifiedAgentModel n)
    (encode : α → UnifiedModel.Transform n)
    (accepting : Set (UnifiedModel.State n))
    (q : UnifiedModel.State n) (a : α) :
    (cognitiveToDFA (cognitiveOfUnified n U encode accepting)).δ q a =
      U.mentalAction.act (encode a) q :=
  rfl

end UAM_CognitiveDFA
