import Mathlib
import RequestProject.Atlas.FormalMindEngineering
import RequestProject.Atlas.FormalMindInterrelationships
import RequestProject.Atlas.UAM_MonoidAction
import RequestProject.Atlas.UAM_Congruence
import RequestProject.Atlas.UAM_Ideal
import RequestProject.Atlas.UAM_Cayley

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bridge between UAM and FormalMind

* monoid actions model composable state actions;
* action-kernel congruences model identity under all mental transformations;
* two-sided ideals model goal classes closed under hierarchical context;
* the canonical action/Cayley representation turns abstract actions into state
  transformations.
-/

namespace UAMFormalMind

open UAM_MonoidAction UAM_Congruence UAM_Ideal
open UAM_MonoidAction.MonoidAction

universe u

/-- A FormalMind subject equipped with composable state actions. -/
structure SubjectActionModel (Action State Observation : Type u) [Monoid Action] where
  subjectivity : FormalMind.Subjectivity State Observation
  dynamics : MonoidAction Action State

namespace SubjectActionModel

variable {Action State Observation : Type u} [Monoid Action]

/-
Doing nothing preserves every mental state.
-/
theorem one_preserves_state (model : SubjectActionModel Action State Observation)
    (state : State) : model.dynamics.act 1 state = state := by
  exact congr_fun model.dynamics.one_act state

/-
Sequential state actions compose according to the monoid product.
-/
theorem sequential_actions (model : SubjectActionModel Action State Observation)
    (first second : Action) (state : State) :
    model.dynamics.act (first * second) state =
      model.dynamics.act second (model.dynamics.act first state) := by
  exact act_mul_apply model.dynamics first second state

/-- Two state actions are identical under transformation when they induce the
same state transformation. -/
def ExtensionalEquality (model : SubjectActionModel Action State Observation)
    (left right : Action) : Prop :=
  ∀ state, model.dynamics.act left state = model.dynamics.act right state

/-
Extensional equality is exactly the action-kernel congruence.
-/
theorem extensionalEquality_iff_kernel
    (model : SubjectActionModel Action State Observation) (left right : Action) :
    model.ExtensionalEquality left right ↔
      model.dynamics.actionKernel.r left right := by
  rw [ MonoidAction.actionKernel_iff ];
  rfl

/-
Extensional equality is compatible with placing actions in arbitrary
left and right mental contexts.
-/
theorem extensionalEquality_context
    (model : SubjectActionModel Action State Observation) {left right : Action}
    (h : model.ExtensionalEquality left right) (pre post : Action) :
    model.ExtensionalEquality (pre * left * post) (pre * right * post) := by
  intro state; simp +decide [ *, mul_assoc ] ;
  simp +decide only [act_mul_apply];
  rw [ h ]

/-- Quotienting by extensional equality produces a monoid of observable
action identities. -/
abbrev ObservableAction (model : SubjectActionModel Action State Observation) :=
  QuotientMonoid model.dynamics.actionKernel

/-
Congruent actions have the same observable-action class.
-/
theorem observableAction_eq (model : SubjectActionModel Action State Observation)
    {left right : Action} (h : model.ExtensionalEquality left right) :
    (QuotientMonoid.mk left : model.ObservableAction) = QuotientMonoid.mk right := by
  rw [QuotientMonoid.mk_eq_iff]
  exact (extensionalEquality_iff_kernel model left right).mp h

end SubjectActionModel

/-! ## Hierarchical goals as ideals -/

/-- A hierarchy of goals/actions is a two-sided ideal: adding arbitrary strategic
context before or after a goal keeps it within the hierarchy. -/
structure HierarchicalGoals (Goal : Type u) [Monoid Goal] where
  goals : Set Goal
  ideal : IsIdeal goals

namespace HierarchicalGoals

variable {Goal : Type u} [Monoid Goal]

/-
Prefixing a hierarchical goal by any strategic context preserves membership.
-/
theorem prefix_closed (hierarchy : HierarchicalGoals Goal) (context : Goal)
    {goal : Goal} (h : goal ∈ hierarchy.goals) : context * goal ∈ hierarchy.goals := by
  exact hierarchy.ideal.left_absorb _ _ h

/-
Suffixing a hierarchical goal by any strategic context preserves membership.
-/
theorem suffix_closed (hierarchy : HierarchicalGoals Goal) (context : Goal)
    {goal : Goal} (h : goal ∈ hierarchy.goals) : goal * context ∈ hierarchy.goals := by
  exact hierarchy.ideal.right_absorb context goal h

/-
Every goal in a hierarchy brings its entire principal two-sided goal hierarchy
with it.
-/
theorem principalHierarchy_subset (hierarchy : HierarchicalGoals Goal)
    {goal : Goal} (h : goal ∈ hierarchy.goals) :
    principalIdeal goal ⊆ hierarchy.goals := by
  intro x hx; obtain ⟨ y, z, rfl ⟩ := hx; exact hierarchy.ideal.right_absorb _ _ ( hierarchy.ideal.left_absorb _ _ h ) ;

/-
Rees congruence identifies all goals belonging to the same collapsed
hierarchical layer.
-/
theorem same_collapsed_layer (hierarchy : HierarchicalGoals Goal)
    {left right : Goal} (hl : left ∈ hierarchy.goals) (hr : right ∈ hierarchy.goals) :
    (reesCongruence hierarchy.goals hierarchy.ideal).r left right := by
  exact Or.inl ⟨ hl, hr ⟩

end HierarchicalGoals

/-! ## Actions become transformations -/

/-- Every abstract mental-action monoid has the canonical right action on itself. -/
def canonicalMentalActions (Action : Type u) [Monoid Action] :
    MonoidAction Action Action := MonoidAction.canonical Action

/-
The canonical state action is the Cayley state transformation.
-/
theorem canonical_action_is_cayley {Action : Type u} [Monoid Action]
    (action state : Action) :
    (canonicalMentalActions Action).act action state =
      (UAM_Cayley.rho action).toFun state := by
  exact MonoidAction.canonical_eq_cayley action state

/-
Abstract actions are faithfully represented by their canonical mental-state
transformations.
-/
theorem actions_become_objects {Action : Type u} [Monoid Action]
    {left right : Action}
    (h : ∀ state, (canonicalMentalActions Action).act left state =
      (canonicalMentalActions Action).act right state) : left = right := by
  contrapose! h;
  exact ⟨ 1, by simpa [ canonicalMentalActions ] using h ⟩

end UAMFormalMind