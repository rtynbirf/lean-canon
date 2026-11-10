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
# Action-model bridge

The bridge uses the project's reverse composition convention: `a * b` acts by
first applying `a`, then `b`.
-/

namespace UAM_ActionModelBridge

open UAM_MonoidAction UAM_MonoidAction.MonoidAction
open UAM_Congruence UAM_Ideal

universe u

/-- Volition together with a monoid of composable state transformations. -/
structure ActionModel (M State Goal Action : Type u) [Monoid M] where
  volition : FormalMind.Volition State Goal Action
  action : MonoidAction M State

namespace ActionModel

variable {M State Goal Action : Type u} [Monoid M]

/-- Doing nothing preserves every state. -/
theorem one_preserves_state (model : ActionModel M State Goal Action)
    (state : State) : model.action.act 1 state = state := by
  exact congr_fun model.action.one_act state

/-- Sequential actions compose according to the monoid product. -/
theorem sequential_actions (model : ActionModel M State Goal Action)
    (first second : M) (state : State) :
    model.action.act (first * second) state =
      model.action.act second (model.action.act first state) := by
  exact act_mul_apply model.action first second state

/-- Reachability is defined by performing one possibly composite action. -/
def Reachable (model : ActionModel M State Goal Action)
    (source target : State) : Prop :=
  ∃ action, model.action.act action source = target

/-- The orbit of a state is exactly its set of reachable states. -/
theorem orbit_eq_reachable (model : ActionModel M State Goal Action)
    (state : State) :
    model.action.orbit state = {target | model.Reachable state target} := by
  ext target
  rfl

/-- If an action gives equal results and goal proposal is invariant under it,
then the proposed goals are equal. -/
theorem action_preserves_proposed_goal
    (model : ActionModel M State Goal Action) (action : M)
    (left right : State)
    (sameResult : model.action.act action left =
      model.action.act action right)
    (proposalInvariant : ∀ state,
      model.volition.proposesGoal (model.action.act action state) =
        model.volition.proposesGoal state) :
    model.volition.proposesGoal left = model.volition.proposesGoal right := by
  rw [← proposalInvariant left, ← proposalInvariant right, sameResult]

end ActionModel

/-! ## Extensional equality of actions -/

/-- Two actions are extensionally equal when they induce the same state
transformation. -/
def ExtensionalEquality {M State : Type u} [Monoid M]
    (action : MonoidAction M State) (left right : M) : Prop :=
  ∀ state, action.act left state = action.act right state

/-- Extensional equality is exactly membership in the action kernel. -/
theorem extensionalEquality_iff_kernel {M State : Type u} [Monoid M]
    (action : MonoidAction M State) (left right : M) :
    ExtensionalEquality action left right ↔ action.actionKernel.r left right := by
  exact (action.actionKernel_iff left right).symm

/-- Extensional equality is compatible with arbitrary action contexts. -/
theorem extensionalEquality_context {M State : Type u} [Monoid M]
    (action : MonoidAction M State) {left right : M}
    (h : ExtensionalEquality action left right) (pre post : M) :
    ExtensionalEquality action (pre * left * post) (pre * right * post) := by
  intro state
  simp only [act_mul_apply]
  rw [h]

/-! ## Ideal structures -/

/-- A distinguished collection closed under context on both sides. -/
structure IdealStructure (Goal : Type u) [Monoid Goal] where
  carrier : Set Goal
  isIdeal : IsIdeal carrier

/-- An ideal element remains in the ideal after context is appended. -/
theorem ideal_suffix {Goal : Type u} [Monoid Goal]
    (ideal : IdealStructure Goal) {goal : Goal}
    (hgoal : goal ∈ ideal.carrier) (context : Goal) :
    goal * context ∈ ideal.carrier := by
  exact ideal.isIdeal.right_absorb context goal hgoal

/-- An ideal element remains in the ideal after context is prepended. -/
theorem ideal_prefix {Goal : Type u} [Monoid Goal]
    (ideal : IdealStructure Goal) {goal : Goal}
    (hgoal : goal ∈ ideal.carrier) (context : Goal) :
    context * goal ∈ ideal.carrier := by
  exact ideal.isIdeal.left_absorb context goal hgoal

/-- Every element of an ideal brings its principal two-sided ideal with it. -/
theorem principalIdeal_subset {Goal : Type u} [Monoid Goal]
    (ideal : IdealStructure Goal) {goal : Goal} (hgoal : goal ∈ ideal.carrier) :
    principalIdeal goal ⊆ ideal.carrier := by
  intro x hx
  obtain ⟨left, right, rfl⟩ := hx
  exact ideal.isIdeal.right_absorb right _
    (ideal.isIdeal.left_absorb left goal hgoal)

/-- Two members of the ideal lie in the same collapsed Rees class. -/
theorem same_ideal_collapsed {Goal : Type u} [Monoid Goal]
    (ideal : IdealStructure Goal) {left right : Goal}
    (hl : left ∈ ideal.carrier) (hr : right ∈ ideal.carrier) :
    (reesCongruence ideal.carrier ideal.isIdeal).r left right := by
  exact Or.inl ⟨hl, hr⟩

/-- The Rees quotient collapses the ideal to one class. -/
abbrev ReesQuotient {Goal : Type u} [Monoid Goal]
    (ideal : IdealStructure Goal) :=
  QuotientMonoid (reesCongruence ideal.carrier ideal.isIdeal)

/-- Proposals in the ideal have the same image in the Rees quotient. -/
theorem quotient_preserves_ideal_proposal
    {State Goal Action : Type u} [Monoid Goal]
    (volition : FormalMind.Volition State Goal Action)
    (ideal : IdealStructure Goal) {left right : State}
    (hl : volition.proposesGoal left ∈ ideal.carrier)
    (hr : volition.proposesGoal right ∈ ideal.carrier) :
    (QuotientMonoid.mk (volition.proposesGoal left) : ReesQuotient ideal) =
      QuotientMonoid.mk (volition.proposesGoal right) := by
  rw [QuotientMonoid.mk_eq_iff]
  exact Or.inl ⟨hl, hr⟩

/-! ## Semilattice assessments -/

/-- Multiplication is the meet for the natural absorption order. -/
theorem semilatticeMeet {M : Type u} [Monoid M]
    (semilattice : UAM_Semilattice.IsSemilattice M) (left right : M) :
    left * right * left = left * right ∧
      left * right * right = left * right ∧
      ∀ assessment, assessment * left = assessment →
        assessment * right = assessment →
        assessment * (left * right) = assessment := by
  exact UAM_Semilattice.semilattice_meet semilattice left right

/-- An idempotent assessment is fixed after being applied twice. -/
theorem fixed_assessment {M : Type u} [Monoid M] (assessment : M)
    (idempotent : UAM_Idempotent.IsIdempotent assessment) :
    assessment * assessment = assessment := by
  exact idempotent

/-- `algLe` records right-reachability between assessments. -/
theorem confidence_algLe_iff {M : Type u} [Monoid M] (left right : M) :
    UAM_Directionality.algLe left right ↔ ∃ context, left * context = right := by
  rfl

/-! ## Cayley universality -/

/-- The canonical action is the Cayley state transformation. -/
theorem canonical_action_is_cayley {M : Type u} [Monoid M]
    (action state : M) :
    (MonoidAction.canonical M).act action state =
      (UAM_Cayley.rho action).toFun state := by
  exact MonoidAction.canonical_eq_cayley action state

/-- Every action monoid embeds injectively into the project's transformation
monoid. -/
theorem cayley_representation {M : Type u} [Monoid M] :
    ∃ representation : UAM_Morphism.MonoidMorphism M (UAM_Cayley.Transform M),
      Function.Injective representation.toFun := by
  exact UAM_Cayley.cayley_embedding

/-- Equality of canonical actions implies equality of the action objects. -/
theorem actions_become_objects {M : Type u} [Monoid M] {left right : M}
    (h : ∀ state, (MonoidAction.canonical M).act left state =
      (MonoidAction.canonical M).act right state) : left = right := by
  contrapose! h
  exact ⟨1, by simpa using h⟩

end UAM_ActionModelBridge
