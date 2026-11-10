import RequestProject.Atlas.UAM_Action
import RequestProject.Atlas.UAM_MonoidAction
import RequestProject.Atlas.UAM_Morphism
import RequestProject.Atlas.UAM_Congruence
import RequestProject.Atlas.UAM_Ideal
import RequestProject.Atlas.UAM_Cayley
import RequestProject.Atlas.FormalMindEngineering
import RequestProject.Atlas.FormalMind_Interrelations
import RequestProject.Atlas.UAM_ActionModelBridge
import RequestProject.Atlas.UnifiedModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Model ladder: four levels of concreteness

The multiplication used throughout is the project's chronological (reverse
composition) multiplication: `f * g = g ∘ f`.  The first three levels separate
three phenomena which coincide in the full model: inhabitation, nontrivial state
space, and nontrivial dynamics.  The fourth level is the existing
`UnifiedModel.UnifiedAgentModel` and is only referenced here.
-/

namespace ModelLadder

open UAM_Action

/-- The common nontrivial state space at levels L1--L3. -/
abbrev State (n : Nat) [NeZero n] := Fin (n + 2)

/-! ## L0: the trivial model -/

section L0

abbrev L0State := Unit
abbrev L0Transform := Unit

instance : Monoid L0Transform where
  one := ()
  mul _ _ := ()
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- The unique action at L0. -/
def L0Action : UAM_MonoidAction.MonoidAction L0Transform L0State where
  act := fun _ _ => ()
  one_act := by
    funext s
    cases s
    rfl
  mul_act := by
    intro f g
    cases f
    cases g
    funext s
    cases s
    rfl

/-- Minimal concrete consciousness at L0. -/
def L0Consciousness : FormalMind.Consciousness L0State L0State where
  conscious _ := True
  observe s := s
  evidence _ := True
  evidence_sound := by
    intro _ _
    trivial

/-- Minimal concrete qualia at L0, with the same observation map. -/
def L0Qualia : FormalMind.Qualia L0State L0State L0State where
  experience s := s
  report s := s

/-- Proposed goals at L0 are the states themselves. -/
def L0Volition : FormalMind.Volition L0State L0State L0State where
  chooses _ _ := ()
  wants _ _ := True
  proposesGoal s := s

/-- ✅ Observation and experience agree unconditionally at L0. -/
theorem L0_bridge_observation_agrees (s : L0State) :
    L0Qualia.experience s = L0Consciousness.observe s := rfl

/-- ✅ Every L0 action fixes every state and hence every proposed goal. -/
theorem L0_bridge_proposal_invariant (f : L0Transform) (s : L0State) :
    L0Volition.proposesGoal (L0Action.act f s) = L0Volition.proposesGoal s := by
  cases f
  cases s
  rfl

/-- ✅ The proposed-goal preservation bridge has no extra premise at L0. -/
theorem L0_action_preserves_proposed_goal (f : L0Transform)
    (left right : L0State)
    (sameResult : L0Action.act f left = L0Action.act f right) :
    L0Volition.proposesGoal left = L0Volition.proposesGoal right := by
  cases left
  cases right
  rfl

/-- Every L0 transformation is constant. -/
def L0ConstantTransforms : Set L0Transform :=
  {f | ∃ value, ∀ state, L0Action.act f state = value}

/-- ✅ Constant transformations form an ideal at L0. -/
theorem L0_constantTransforms_ideal :
    UAM_Ideal.IsIdeal L0ConstantTransforms := by
  constructor
  · exact ⟨(), ⟨(), by intro s; cases s; rfl⟩⟩
  · intro a b hb
    cases a
    cases b
    exact hb
  · intro a b hb
    cases a
    cases b
    exact hb

/-- ✅ Actions become objects extensionally at L0. -/
theorem L0_actions_become_objects (f g : L0Transform)
    (_sameAction : ∀ s, L0Action.act f s = L0Action.act g s) : f = g := by
  cases f
  cases g
  rfl

end L0

/-! ## L1: identity-only dynamics -/

section L1

variable (n : Nat) [NeZero n]

/-- The sole transformations at L1 are endomaps equal to `id`. -/
abbrev L1Transform := {f : State n → State n // f = id}

instance : Monoid (L1Transform n) where
  one := ⟨id, rfl⟩
  mul f g := ⟨g.1 ∘ f.1, by rw [f.2, g.2]; rfl⟩
  mul_assoc _ _ _ := rfl
  one_mul f := by apply Subtype.ext; rfl
  mul_one f := by apply Subtype.ext; rfl

/-- Evaluation gives the identity-only monoid action. -/
def L1Action : UAM_MonoidAction.MonoidAction (L1Transform n) (State n) where
  act := fun f s => f.1 s
  one_act := by
    funext s
    rfl
  mul_act := by
    intro f g
    funext s
    rfl

/-- Consciousness whose observation is the state itself. -/
def L1Consciousness : FormalMind.Consciousness (State n) (State n) where
  conscious s := s ≠ 0
  observe s := s
  evidence s := s ≠ 0
  evidence_sound := by
    intro _ h
    exact h

/-- Qualia whose experience is the state itself. -/
def L1Qualia : FormalMind.Qualia (State n) (State n) (State n) where
  experience s := s
  report s := s

/-- L1 volition proposes its current state. -/
def L1Volition : FormalMind.Volition (State n) (State n) (State n) where
  chooses _ goal := goal
  wants state goal := state = goal
  proposesGoal state := state

/-- ✅ Observation and experience agree unconditionally at L1. -/
theorem L1_bridge_observation_agrees (s : State n) :
    (L1Qualia n).experience s = (L1Consciousness n).observe s := rfl

/-- Every L1 transformation is pointwise the identity. -/
theorem L1_fixes_all (f : L1Transform n) (s : State n) : f.1 s = s := by
  rw [f.2]
  rfl

/-- ✅ Proposed goals are invariant under every L1 action. -/
theorem L1_bridge_proposal_invariant (f : L1Transform n) (s : State n) :
    (L1Volition n).proposesGoal ((L1Action n).act f s) =
      (L1Volition n).proposesGoal s := by
  exact L1_fixes_all n f s

/-- ✅ At L1, the existing bridge needs no user-supplied invariance premise. -/
theorem L1_action_preserves_proposed_goal (f : L1Transform n)
    (left right : State n)
    (sameResult : (L1Action n).act f left = (L1Action n).act f right) :
    (L1Volition n).proposesGoal left = (L1Volition n).proposesGoal right := by
  apply UAM_ActionModelBridge.ActionModel.action_preserves_proposed_goal
    ({ volition := L1Volition n, action := L1Action n } :
      UAM_ActionModelBridge.ActionModel
        (L1Transform n) (State n) (State n) (State n)) f left right sameResult
  intro state
  exact L1_bridge_proposal_invariant n f state

/-- Constant L1 transformations, defined extensionally. -/
def L1ConstantTransforms : Set (L1Transform n) :=
  {f | ∃ value, ∀ state, f.1 state = value}

/-- The two explicit states used to show the L1 state space is nontrivial. -/
def ladderNext : State n := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ n)⟩

@[simp] theorem zero_ne_ladderNext : (0 : State n) ≠ ladderNext n := by
  intro h
  have hv := congrArg Fin.val h
  simp [ladderNext] at hv

/-- ❌ L1 has no constant transformations: its only action is identity on a
nontrivial state space. -/
theorem L1_constantTransforms_empty : L1ConstantTransforms n = ∅ := by
  ext f
  constructor
  · rintro ⟨value, hvalue⟩
    have hzero := hvalue 0
    have hnext := hvalue (ladderNext n)
    have hfixZero := L1_fixes_all n f 0
    have hfixNext := L1_fixes_all n f (ladderNext n)
    exfalso
    apply zero_ne_ladderNext n
    rw [← hfixZero, hzero, ← hnext, hfixNext]
  · intro h
    cases h

/-- Therefore the constant-transform set at L1 cannot be an ideal: ideals are
required by `UAM_Ideal.IsIdeal` to be nonempty. -/
theorem L1_constantTransforms_not_ideal :
    ¬ UAM_Ideal.IsIdeal (L1ConstantTransforms n) := by
  intro hIdeal
  obtain ⟨f, hf⟩ := hIdeal.nonempty
  rw [L1_constantTransforms_empty n] at hf
  exact hf

/-- ✅ Equality of effects determines equality of L1 actions. -/
theorem L1_actions_become_objects (f g : L1Transform n)
    (_sameAction : ∀ s, (L1Action n).act f s = (L1Action n).act g s) : f = g := by
  apply Subtype.ext
  rw [f.2, g.2]

end L1

/-! ## L2: transformations fixing the initial state -/

section L2

variable (n : Nat) [NeZero n]

/-- L2 transformations fix the distinguished initial state. -/
abbrev L2Transform := {f : State n → State n // f 0 = 0}

instance : Monoid (L2Transform n) where
  one := ⟨id, rfl⟩
  mul f g := ⟨g.1 ∘ f.1, by simp only [Function.comp_apply, f.2, g.2]⟩
  mul_assoc _ _ _ := rfl
  one_mul f := by apply Subtype.ext; rfl
  mul_one f := by apply Subtype.ext; rfl

/-- Evaluation is an action, again using reverse composition. -/
def L2Action : UAM_MonoidAction.MonoidAction (L2Transform n) (State n) where
  act := fun f s => f.1 s
  one_act := by funext s; rfl
  mul_act := by intro f g; funext s; rfl

/-- L2 uses the same state-level observational interfaces as L1. -/
def L2Consciousness : FormalMind.Consciousness (State n) (State n) :=
  L1Consciousness n

def L2Qualia : FormalMind.Qualia (State n) (State n) (State n) :=
  L1Qualia n

def L2Volition : FormalMind.Volition (State n) (State n) (State n) :=
  L1Volition n

/-- ✅ Observation and experience agree unconditionally at L2. -/
theorem L2_bridge_observation_agrees (s : State n) :
    (L2Qualia n).experience s = (L2Consciousness n).observe s := rfl

/-- ✅ Pointwise fixedness is exactly the sufficient hypothesis for the local
proposal-invariance statement. -/
theorem L2_bridge_proposal_invariant (f : L2Transform n) (s : State n)
    (fixed : f.1 s = s) :
    (L2Volition n).proposesGoal ((L2Action n).act f s) =
      (L2Volition n).proposesGoal s := by
  exact fixed

/-- ⚠️ At L2 the preservation bridge works when global proposal invariance is
supplied; for this concrete volition, pointwise fixedness supplies it. -/
theorem L2_action_preserves_proposed_goal (f : L2Transform n)
    (left right : State n)
    (sameResult : (L2Action n).act f left = (L2Action n).act f right)
    (fixed : ∀ s, f.1 s = s) :
    (L2Volition n).proposesGoal left = (L2Volition n).proposesGoal right := by
  apply UAM_ActionModelBridge.ActionModel.action_preserves_proposed_goal
    ({ volition := L2Volition n, action := L2Action n } :
      UAM_ActionModelBridge.ActionModel
        (L2Transform n) (State n) (State n) (State n)) f left right sameResult
  intro state
  exact L2_bridge_proposal_invariant n f state (fixed state)

/-- The constant-zero map is an L2 transformation. -/
def L2Zero : L2Transform n := ⟨fun _ => 0, rfl⟩

/-- ❌ Global proposal invariance is false at L2: the constant-zero action
changes the explicit noninitial state. -/
theorem L2_global_proposal_invariance_fails :
    ∃ f : L2Transform n, ∃ s : State n,
      (L2Volition n).proposesGoal ((L2Action n).act f s) ≠
        (L2Volition n).proposesGoal s := by
  exact ⟨L2Zero n, ladderNext n, zero_ne_ladderNext n⟩

/-- Constant L2 transformations.  Fixing zero forces their value to be zero. -/
def L2ConstantTransforms : Set (L2Transform n) :=
  {f | ∃ value, ∀ state, f.1 state = value}

/-- ✅ Constant L2 transformations form a nonempty two-sided ideal. -/
theorem L2_constantTransforms_ideal :
    UAM_Ideal.IsIdeal (L2ConstantTransforms n) := by
  constructor
  · exact ⟨L2Zero n, ⟨0, by intro state; rfl⟩⟩
  · intro left right hright
    obtain ⟨value, hvalue⟩ := hright
    have hvalueZero : value = 0 := by
      rw [← hvalue 0]
      exact right.2
    exact ⟨0, by
      intro state
      change right.1 (left.1 state) = 0
      rw [hvalue (left.1 state), hvalueZero]⟩
  · intro right left hleft
    obtain ⟨value, hvalue⟩ := hleft
    have hvalueZero : value = 0 := by
      rw [← hvalue 0]
      exact left.2
    exact ⟨0, by
      intro state
      change right.1 (left.1 state) = 0
      rw [hvalue state, hvalueZero]
      exact right.2⟩

/-- ✅ Constant goals are absorbed on both sides at L2. -/
theorem L2_constant_goal_absorbed (constant : L2Transform n)
    (hconstant : constant ∈ L2ConstantTransforms n) (context : L2Transform n) :
    constant * context ∈ L2ConstantTransforms n ∧
      context * constant ∈ L2ConstantTransforms n := by
  constructor
  · exact (L2_constantTransforms_ideal n).right_absorb context constant hconstant
  · exact (L2_constantTransforms_ideal n).left_absorb context constant hconstant

/-- ✅ Equality at every state makes L2 actions equal as objects. -/
theorem L2_actions_become_objects (f g : L2Transform n)
    (sameAction : ∀ s, (L2Action n).act f s = (L2Action n).act g s) : f = g := by
  apply Subtype.ext
  funext state
  exact sameAction state

end L2

/-! ## L3: reference to the existing full model -/

/-- L3 is exactly the existing full unified package; it is not reconstructed. -/
abbrev L3Model (n : Nat) [NeZero n] := UnifiedModel.UnifiedAgentModel n

/-- The imported construction supplies every L3 reference model. -/
theorem L3_reference_exists (n : Nat) [NeZero n] : Nonempty (L3Model n) :=
  UnifiedModel.unified_model_exists n

/-! ## The embedding chain -/

/-- L0 embeds into L1 as its unique identity transformation. -/
def embedL0L1 (n : Nat) [NeZero n] :
    UAM_Morphism.MonoidMorphism L0Transform (L1Transform n) where
  toFun := fun _ => ⟨id, rfl⟩
  map_one := rfl
  map_mul := by intro a b; cases a; cases b; rfl

/-- The L0-to-L1 morphism is injective. -/
theorem embedL0L1_injective (n : Nat) [NeZero n] :
    Function.Injective (embedL0L1 n).toFun := by
  intro a b _
  cases a
  cases b
  rfl

/-- L1 embeds into L2 by forgetting the stronger identity proof. -/
def embedL1L2 (n : Nat) [NeZero n] :
    UAM_Morphism.MonoidMorphism (L1Transform n) (L2Transform n) where
  toFun := fun f => ⟨f.1, by rw [f.2]; rfl⟩
  map_one := rfl
  map_mul := by intro a b; rfl

/-- The L1-to-L2 morphism is injective. -/
theorem embedL1L2_injective (n : Nat) [NeZero n] :
    Function.Injective (embedL1L2 n).toFun := by
  intro a b h
  have hv : ((embedL1L2 n).toFun a).1 = ((embedL1L2 n).toFun b).1 :=
    congrArg (fun x : L2Transform n => x.1) h
  exact Subtype.ext hv

/-- L2 embeds into the full L3 transformation monoid by forgetting fixedness. -/
def embedL2L3 (n : Nat) [NeZero n] :
    UAM_Morphism.MonoidMorphism (L2Transform n) (UnifiedModel.Transform n) where
  toFun := fun f => f.1
  map_one := rfl
  map_mul := by intro a b; rfl

/-- The L2-to-L3 morphism is injective. -/
theorem embedL2L3_injective (n : Nat) [NeZero n] :
    Function.Injective (embedL2L3 n).toFun := by
  intro a b h
  exact Subtype.ext h

/-! ## Machine-readable bridge summary -/

/-- Summary of L0: observation, proposal preservation, a constant ideal, and
actions-as-objects all hold. -/
theorem L0_bridges :
    (∀ s, L0Qualia.experience s = L0Consciousness.observe s) ∧
    (∀ f s, L0Volition.proposesGoal (L0Action.act f s) =
      L0Volition.proposesGoal s) ∧
    UAM_Ideal.IsIdeal L0ConstantTransforms := by
  exact ⟨L0_bridge_observation_agrees, L0_bridge_proposal_invariant,
    L0_constantTransforms_ideal⟩

/-- Summary of L1: observation and proposals are invariant, while the constant
set is empty and hence not an ideal. -/
theorem L1_bridges (n : Nat) [NeZero n] :
    (∀ s, (L1Qualia n).experience s = (L1Consciousness n).observe s) ∧
    (∀ f s, (L1Volition n).proposesGoal ((L1Action n).act f s) =
      (L1Volition n).proposesGoal s) ∧
    ¬ UAM_Ideal.IsIdeal (L1ConstantTransforms n) := by
  exact ⟨L1_bridge_observation_agrees n, L1_bridge_proposal_invariant n,
    L1_constantTransforms_not_ideal n⟩

/-- Summary of L2: observations agree and constants form an ideal, but global
proposal invariance has a concrete counterexample. -/
theorem L2_bridges (n : Nat) [NeZero n] :
    (∀ s, (L2Qualia n).experience s = (L2Consciousness n).observe s) ∧
    UAM_Ideal.IsIdeal (L2ConstantTransforms n) ∧
    (∃ f : L2Transform n, ∃ s : State n,
      (L2Volition n).proposesGoal ((L2Action n).act f s) ≠
        (L2Volition n).proposesGoal s) := by
  exact ⟨L2_bridge_observation_agrees n, L2_constantTransforms_ideal n,
    L2_global_proposal_invariance_fails n⟩

/-- The whole ladder exists: the three explicit actions, the imported L3 model,
and the three injective monoid morphisms are packaged together. -/
structure Ladder (n : Nat) [NeZero n] where
  l0Action : UAM_MonoidAction.MonoidAction L0Transform L0State
  l1Action : UAM_MonoidAction.MonoidAction (L1Transform n) (State n)
  l2Action : UAM_MonoidAction.MonoidAction (L2Transform n) (State n)
  l3Model : L3Model n
  l0_l1 : UAM_Morphism.MonoidMorphism L0Transform (L1Transform n)
  l1_l2 : UAM_Morphism.MonoidMorphism (L1Transform n) (L2Transform n)
  l2_l3 : UAM_Morphism.MonoidMorphism (L2Transform n) (UnifiedModel.Transform n)
  l0_l1_injective : Function.Injective l0_l1.toFun
  l1_l2_injective : Function.Injective l1_l2.toFun
  l2_l3_injective : Function.Injective l2_l3.toFun

/-- Final existence theorem for all four levels and the embedding chain. -/
theorem ladder_exists (n : Nat) [NeZero n] : Nonempty (Ladder n) := by
  obtain ⟨reference⟩ := L3_reference_exists n
  exact ⟨{
    l0Action := L0Action
    l1Action := L1Action n
    l2Action := L2Action n
    l3Model := reference
    l0_l1 := embedL0L1 n
    l1_l2 := embedL1L2 n
    l2_l3 := embedL2L3 n
    l0_l1_injective := embedL0L1_injective n
    l1_l2_injective := embedL1L2_injective n
    l2_l3_injective := embedL2L3_injective n
  }⟩

end ModelLadder
