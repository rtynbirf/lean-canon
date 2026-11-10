import Mathlib
import RequestProject.Atlas.FormalMindEngineering
import RequestProject.Atlas.UAM_MonoidAction
import RequestProject.Atlas.UAM_Congruence
import RequestProject.Atlas.UAM_Ideal
import RequestProject.Atlas.UAM_Semilattice
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Cayley
import RequestProject.Atlas.UAM_Morphism

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UAM--FormalMind bridge

The bridge uses the project's reverse composition convention: `a * b` acts by
first applying `a`, then `b`.
-/

namespace UAM_FormalMind_Bridge

open UAM_MonoidAction UAM_MonoidAction.MonoidAction
open UAM_Congruence UAM_Ideal

universe u

/-! ## Mental actions via monoid actions -/

/-- A FormalMind subject equipped with composable mental actions. -/
structure MentalActionModel (M State Goal Action : Type u) [Monoid M] where
  volition : FormalMind.Volition State Goal Action
  mentalAction : MonoidAction M State

namespace MentalActionModel

variable {M State Goal Action : Type u} [Monoid M]

/-- Doing nothing preserves every mental state. -/
theorem one_preserves_state (model : MentalActionModel M State Goal Action)
    (state : State) : model.mentalAction.act 1 state = state := by
  exact congr_fun model.mentalAction.one_act state

/-- Sequential mental actions compose according to the monoid product. -/
theorem sequential_actions (model : MentalActionModel M State Goal Action)
    (first second : M) (state : State) :
    model.mentalAction.act (first * second) state =
      model.mentalAction.act second (model.mentalAction.act first state) := by
  exact act_mul_apply model.mentalAction first second state

/-- Reachability is defined by performing one (possibly composite) mental action. -/
def Reachable (model : MentalActionModel M State Goal Action)
    (source target : State) : Prop :=
  ∃ action, model.mentalAction.act action source = target

/-- The orbit of a mental state is exactly its set of reachable states. -/
theorem orbit_eq_reachable (model : MentalActionModel M State Goal Action)
    (state : State) :
    model.mentalAction.orbit state = {target | model.Reachable state target} := by
  ext target
  rfl

/-- If a mental action preserves both states and proposing a goal is invariant
under that action, then the proposed goals are preserved. -/
theorem action_preserves_proposed_goal
    (model : MentalActionModel M State Goal Action) (mentalAction : M)
    (left right : State)
    (sameResult : model.mentalAction.act mentalAction left =
      model.mentalAction.act mentalAction right)
    (proposalInvariant : ∀ state,
      model.volition.proposesGoal (model.mentalAction.act mentalAction state) =
        model.volition.proposesGoal state) :
    model.volition.proposesGoal left = model.volition.proposesGoal right := by
  rw [← proposalInvariant left, ← proposalInvariant right, sameResult]

end MentalActionModel

/-! ## Observer identity as a congruence -/

/-- The observer cannot distinguish actions that have the same effect on every
mental state.  This is the project's own `IsCongruence`, obtained as the action
kernel. -/
def ObserverIdentity {M State : Type u} [Monoid M]
    (action : MonoidAction M State) : IsCongruence M :=
  action.actionKernel

/-- Two mental actions are identical under transformation when they induce the
same state transformation. -/
def TransformationallyIdentical {M State : Type u} [Monoid M]
    (action : MonoidAction M State) (left right : M) : Prop :=
  ∀ state, action.act left state = action.act right state

/-- Transformational identity is exactly the action-kernel congruence. -/
theorem transformationalIdentity_iff_kernel {M State : Type u} [Monoid M]
    (action : MonoidAction M State) (left right : M) :
    TransformationallyIdentical action left right ↔
      (ObserverIdentity action).r left right := by
  exact (action.actionKernel_iff left right).symm

/-- Transformational identity is compatible with placing actions in arbitrary
left and right mental contexts. -/
theorem transformationalIdentity_context {M State : Type u} [Monoid M]
    (action : MonoidAction M State) {left right : M}
    (h : TransformationallyIdentical action left right) (pre post : M) :
    TransformationallyIdentical action (pre * left * post) (pre * right * post) := by
  intro state
  simp only [act_mul_apply, act_mul_apply]
  rw [h]

/-- Observer-equivalent actions act identically on every state. -/
theorem observerIdentity_act_eq {M State : Type u} [Monoid M]
    (action : MonoidAction M State) {left right : M}
    (equivalent : (ObserverIdentity action).r left right) (state : State) :
    action.act left state = action.act right state := by
  exact (action.actionKernel_iff left right).mp equivalent state

/-- The action kernel is the congruence associated with all point stabilizers:
two actions are related exactly when they agree at every point. -/
theorem kernel_from_point_stabilizers {M State : Type u} [Monoid M]
    (action : MonoidAction M State) (left right : M) :
    (ObserverIdentity action).r left right ↔
      ∀ state, action.act left state = action.act right state := by
  exact action.actionKernel_iff left right

/-- The observational perspective is the quotient monoid by observer identity. -/
abbrev ObservationalPerspective {M State : Type u} [Monoid M]
    (action : MonoidAction M State) :=
  QuotientMonoid (ObserverIdentity action)

/-- Observer-equivalent actions become equal in the observational perspective. -/
theorem perspective_identifies {M State : Type u} [Monoid M]
    (action : MonoidAction M State) {left right : M}
    (equivalent : (ObserverIdentity action).r left right) :
    (QuotientMonoid.mk left : ObservationalPerspective action) =
    QuotientMonoid.mk right := by
  rw [QuotientMonoid.mk_eq_iff]
  exact equivalent

/-! ## Goal hierarchies as ideals -/

/-- Discarded possibilities form a two-sided ideal. -/
structure GoalHierarchy (Goal : Type u) [Monoid Goal] where
  discarded : Set Goal
  closed : IsIdeal discarded

/-- A discarded goal remains discarded after arbitrary context is appended. -/
theorem discarded_suffix {Goal : Type u} [Monoid Goal]
    (hierarchy : GoalHierarchy Goal) {goal : Goal}
    (discarded : goal ∈ hierarchy.discarded) (context : Goal) :
    goal * context ∈ hierarchy.discarded := by
  exact hierarchy.closed.right_absorb context goal discarded

/-- A discarded goal remains discarded after arbitrary context is prepended. -/
theorem discarded_prefix {Goal : Type u} [Monoid Goal]
    (hierarchy : GoalHierarchy Goal) {goal : Goal}
    (discarded : goal ∈ hierarchy.discarded) (context : Goal) :
    context * goal ∈ hierarchy.discarded := by
  exact hierarchy.closed.left_absorb context goal discarded

/-- Every goal in a hierarchy brings its entire principal ideal with it. -/
theorem principalHierarchy_subset {Goal : Type u} [Monoid Goal]
    (hierarchy : GoalHierarchy Goal) {goal : Goal}
    (h : goal ∈ hierarchy.discarded) :
    principalIdeal goal ⊆ hierarchy.discarded := by
  intro x hx
  obtain ⟨y, z, rfl⟩ := hx
  exact hierarchy.closed.right_absorb _ _ (hierarchy.closed.left_absorb _ _ h)

/-- All discarded goals are identified in the Rees quotient. -/
theorem same_collapsed_layer {Goal : Type u} [Monoid Goal]
    (hierarchy : GoalHierarchy Goal) {left right : Goal}
    (hl : left ∈ hierarchy.discarded) (hr : right ∈ hierarchy.discarded) :
    (reesCongruence hierarchy.discarded hierarchy.closed).r left right := by
  exact Or.inl ⟨hl, hr⟩

/-- The Rees quotient is the reduced decision space obtained by collapsing all
discarded goals. -/
abbrev ReducedDecisionSpace {Goal : Type u} [Monoid Goal]
    (hierarchy : GoalHierarchy Goal) :=
  QuotientMonoid (reesCongruence hierarchy.discarded hierarchy.closed)

/-- All discarded proposals are represented by one goal in the reduced decision
space. -/
theorem quotient_preserves_discarded_proposal
    {State Goal Action : Type u} [Monoid Goal]
    (volition : FormalMind.Volition State Goal Action)
    (hierarchy : GoalHierarchy Goal) {left right : State}
    (leftDiscarded : volition.proposesGoal left ∈ hierarchy.discarded)
    (rightDiscarded : volition.proposesGoal right ∈ hierarchy.discarded) :
    (QuotientMonoid.mk (volition.proposesGoal left) :
      ReducedDecisionSpace hierarchy) =
    QuotientMonoid.mk (volition.proposesGoal right) := by
  rw [QuotientMonoid.mk_eq_iff]
  exact Or.inl ⟨leftDiscarded, rightDiscarded⟩

/-! ## Idempotent confidence assessments -/

/-- In a semilattice, multiplication is the meet of two confidence assessments. -/
theorem confidence_meet {M : Type u} [Monoid M]
    (semilattice : UAM_Semilattice.IsSemilattice M) (left right : M) :
    left * right * left = left * right ∧
      left * right * right = left * right ∧
      ∀ assessment, assessment * left = assessment →
        assessment * right = assessment →
        assessment * (left * right) = assessment := by
  exact UAM_Semilattice.semilattice_meet semilattice left right

/-- An idempotent confidence assessment is fixed after being applied twice. -/
theorem fixed_assessment {M : Type u} [Monoid M] (assessment : M)
    (idempotent : UAM_Idempotent.IsIdempotent assessment) :
    assessment * assessment = assessment := by
  exact idempotent

/-- `algLe` records right-reachability between confidence assessments. -/
theorem confidence_algLe_iff {M : Type u} [Monoid M] (left right : M) :
    UAM_Directionality.algLe left right ↔ ∃ context, left * context = right := by
  rfl

/-! ## Cayley universality -/

/-- The canonical mental action is the Cayley state transformation. -/
theorem canonical_action_is_cayley {M : Type u} [Monoid M]
    (action state : M) :
    (MonoidAction.canonical M).act action state =
      (UAM_Cayley.rho action).toFun state := by
  exact MonoidAction.canonical_eq_cayley action state

/-- Every monoid of mental actions embeds injectively into the project's monoid
of state transformations. -/
theorem cayley_mental_model {M : Type u} [Monoid M] :
    ∃ representation : UAM_Morphism.MonoidMorphism M (UAM_Cayley.Transform M),
      Function.Injective representation.toFun := by
  exact UAM_Cayley.cayley_embedding

/-- Abstract actions are faithfully represented by their canonical mental-state
transformations. -/
theorem actions_become_objects {M : Type u} [Monoid M]
    {left right : M}
    (h : ∀ state, (MonoidAction.canonical M).act left state =
      (MonoidAction.canonical M).act right state) : left = right := by
  have : (UAM_Cayley.rho left).toFun 1 = (UAM_Cayley.rho right).toFun 1 := by
    rw [← canonical_action_is_cayley, ← canonical_action_is_cayley, h]
  rwa [UAM_Cayley.rho_one, UAM_Cayley.rho_one] at this

end UAM_FormalMind_Bridge