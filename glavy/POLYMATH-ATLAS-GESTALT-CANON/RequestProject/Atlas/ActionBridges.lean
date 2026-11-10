import Mathlib
import RequestProject.Atlas.UAM_Green
import RequestProject.Atlas.UAM_MonoidAction
import RequestProject.Atlas.UAM_Submonoid
import RequestProject.Atlas.UAM_Congruence
import RequestProject.Atlas.UAM_Ideal
import RequestProject.Atlas.UAM_Semilattice
import RequestProject.Atlas.UnifiedModel
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.Arithmetic_Rice
import RequestProject.Atlas.FormalMindEngineering
import RequestProject.Atlas.UAM_ActionCongruence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ActionBridges

universe u

/-! Action bridges organized around action-invariant state equivalence. -/

structure StateLabeling (X : Type u) (Label : Type u) where
  label : X → Label

def labelingKernel (X Label : Type u) (ann : StateLabeling X Label) :
    X → X → Prop := fun x y => ann.label x = ann.label y

theorem labelingKernel_refl (X Label : Type u) (ann : StateLabeling X Label) :
    ∀ x, labelingKernel X Label ann x x := by
  intro x
  rfl

theorem labelingKernel_symm (X Label : Type u) (ann : StateLabeling X Label) :
    ∀ x y, labelingKernel X Label ann x y → labelingKernel X Label ann y x := by
  intro x y h
  exact h.symm

theorem labelingKernel_trans (X Label : Type u) (ann : StateLabeling X Label) :
    ∀ x y z, labelingKernel X Label ann x y → labelingKernel X Label ann y z →
      labelingKernel X Label ann x z := by
  intro x y z hxy hyz
  exact hxy.trans hyz

def labelingActionCongruence {M X Label : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (ann : StateLabeling X Label)
    (hLabelInvariant : ∀ m x, ann.label (A.act m x) = ann.label x) :
    UAM_ActionCongruence.ActionCongruence M X A :=
  UAM_ActionCongruence.mkActionCongruence A (labelingKernel X Label ann)
    ⟨labelingKernel_refl X Label ann,
      fun h => labelingKernel_symm X Label ann _ _ h,
      fun h₁ h₂ => labelingKernel_trans X Label ann _ _ _ h₁ h₂⟩
    (by
      intro m x y h
      unfold labelingKernel at h ⊢
      rw [hLabelInvariant m x, hLabelInvariant m y]
      exact h)

structure ThresholdSimilarity (X : Type u) where
  similarity : X → X → Rat
  threshold : Rat
  aboveThreshold : X → X → Prop
  aboveThreshold_def : ∀ s t, aboveThreshold s t ↔ similarity s t ≥ threshold

/-- Symmetric action-preserved state equivalence converts to a action congruence. -/
def stateEquivalence_to_actionCongruence {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (E : UAM_ActionCongruence.StateEquivalence X)
    (EA : UAM_ActionCongruence.PreorderInvariant M X A E.toStatePreorder) :
    UAM_ActionCongruence.ActionCongruence M X A :=
  UAM_ActionCongruence.mkActionCongruence A E.rel
    ⟨E.refl, fun h => E.symm _ _ h, fun h₁ h₂ => E.trans _ _ _ h₁ h₂⟩ EA.preserves

/-- Conversion to state equivalence and back is the identity. -/
theorem stateEquivalence_actionCongruence_iso {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : UAM_ActionCongruence.ActionCongruence M X A) :
    stateEquivalence_to_actionCongruence A
      C.toStateEquivalence
      (UAM_ActionCongruence.ActionCongruence.toPreorderInvariant A C) = C := by
  cases C
  rfl

structure CentralElement (G : Type u) [Group G] where
  elem : G
  isCentral : ∀ g, g * elem * g⁻¹ = elem

theorem central_commutes {G : Type u} [Group G]
    (I : CentralElement G) (g : G) : g * I.elem = I.elem * g := by
  have h := I.isCentral g
  calc
    g * I.elem = (g * I.elem * g⁻¹) * g := by simp [mul_assoc]
    _ = I.elem * g := by rw [h]

structure CongruencePreservingMap (M : Type u) [Monoid M] where
  cong : UAM_Congruence.IsCongruence M
  map : M → M
  self_related : ∀ m, cong.r m (map m)
  map_preserves : ∀ a b, cong.r a b →
    cong.r (map a) (map b)

theorem map_image_stabilizes {M : Type u} [Monoid M] (W : CongruencePreservingMap M) (m : M) :
    W.cong.r (W.map (W.map m)) (W.map m) := by
  exact W.cong.symm _ _ (W.map_preserves m (W.map m) (W.self_related m))

structure GuardedPredicate (X : Type u) where
  pred : X → Prop
  safeSet : Set X
  pred_subset_safe : ∀ s, pred s → s ∈ safeSet

/-- Actions preserving a safe set form an actual submonoid. -/
def safeSetStabilizer {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (PZ : Set X) :
    UAM_Submonoid.Submonoid M where
  carrier := {m | ∀ s ∈ PZ, A.act m s ∈ PZ}
  one_mem := by
    intro s hs
    simpa using hs
  mul_mem := by
    intro a b ha hb s hs
    rw [UAM_MonoidAction.MonoidAction.act_mul_apply]
    exact hb (A.act a s) (ha s hs)

/-- The requested safe-set submonoid theorem, stated as membership closure. -/
theorem safeSetStabilizer_is_submonoid {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (PZ : Set X) :
    (1 : M) ∈ (safeSetStabilizer A PZ).carrier ∧
      ∀ a b, a ∈ (safeSetStabilizer A PZ).carrier →
        b ∈ (safeSetStabilizer A PZ).carrier →
        a * b ∈ (safeSetStabilizer A PZ).carrier := by
  exact ⟨(safeSetStabilizer A PZ).one_mem,
    fun a b ha hb => (safeSetStabilizer A PZ).mul_mem a b ha hb⟩

structure RightIdealEscape (M : Type u) [Monoid M] where
  ideal : Set M
  hRightIdeal : UAM_Ideal.IsRightIdeal ideal
  escape : M
  escape_prop : ∀ n ∈ ideal, escape * n ∉ ideal

theorem escape_not_in_ideal {M : Type u} [Monoid M]
    (res : RightIdealEscape M) : res.escape ∉ res.ideal := by
  intro h
  exact res.escape_prop res.escape h
    (res.hRightIdeal.right_absorb res.escape res.escape h)

structure StateValuation (X : Type u) where
  val : X → Rat

structure QuotientValuation (X : Type u) (R : X → X → Prop) (RM : StateValuation X) where
  invariant : ∀ {x y}, R x y → RM.val x = RM.val y

@[ext]
structure UnitInterval where
  val : Rat
  bound : 0 ≤ val ∧ val ≤ 1

abbrev QualityVector (n : Nat) := Fin n → UnitInterval

def qualityMeet {n : Nat} (a b : QualityVector n) : QualityVector n :=
  fun i => ⟨min (a i).val (b i).val,
    ⟨le_min (a i).bound.1 (b i).bound.1,
      le_trans (min_le_left _ _) (a i).bound.2⟩⟩

theorem qualityMeet_idempotent {n : Nat} (q : QualityVector n) :
    qualityMeet q q = q := by
  funext i
  apply UnitInterval.ext
  simp [qualityMeet]

structure IdempotentWrapper (M : Type u) [Monoid M] where
  elem : M
  hIdem : UAM_Idempotent.IsIdempotent elem

/-- Full-orbit information density. -/
noncomputable def informationDensity {M X : Type u} [Monoid M] [Fintype X]
    (A : UAM_MonoidAction.MonoidAction M X) (x : X) : Rat := by
  classical
  letI := Set.toFinite (UAM_MonoidAction.MonoidAction.orbit A x)
  exact ((UAM_MonoidAction.MonoidAction.orbit A x).toFinset.card : Rat) /
    (Fintype.card X : Rat)

theorem informationDensity_le_one {M X : Type u} [Monoid M] [Fintype X]
    (A : UAM_MonoidAction.MonoidAction M X) (x : X) :
    0 ≤ informationDensity A x ∧ informationDensity A x ≤ 1 := by
  classical
  letI : Nonempty X := ⟨x⟩
  letI := Set.toFinite (UAM_MonoidAction.MonoidAction.orbit A x)
  have hcard : (UAM_MonoidAction.MonoidAction.orbit A x).toFinset.card ≤
      Fintype.card X := by
    calc
      (UAM_MonoidAction.MonoidAction.orbit A x).toFinset.card ≤
          (Set.univ : Set X).toFinset.card := by
            apply Finset.card_le_card
            simp
      _ = Fintype.card X := by simp
  have hden : (0 : Rat) < (Fintype.card X : Rat) := by
    exact_mod_cast Fintype.card_pos
  change 0 ≤ ((UAM_MonoidAction.MonoidAction.orbit A x).toFinset.card : Rat) /
      (Fintype.card X : Rat) ∧
    ((UAM_MonoidAction.MonoidAction.orbit A x).toFinset.card : Rat) /
      (Fintype.card X : Rat) ≤ 1
  constructor
  · exact div_nonneg (by positivity) hden.le
  · rw [div_le_one hden]
    exact_mod_cast hcard

noncomputable def agreementIndex {n : Nat} [NeZero n]
    (f g : UnifiedModel.State n → UnifiedModel.State n) : Rat :=
  (Fintype.card {s : UnifiedModel.State n // f s = g s} : Rat) /
    (Fintype.card (UnifiedModel.State n) : Rat)

theorem agreementIndex_symmetric {n : Nat} [NeZero n]
    (f g : UnifiedModel.State n → UnifiedModel.State n) :
    agreementIndex f g = agreementIndex g f := by
  simp +decide [agreementIndex, eq_comm]

structure ProgressMeasure (M X : Type u) [Monoid M] where
  rank : X → Nat
  step : M → X → X
  improves : ∀ m x, rank (step m x) ≥ rank x

theorem progress_stabilizes {M X : Type u} [Monoid M] [Fintype X]
    (T : ProgressMeasure M X) (m : M) (x : X) :
    ∃ n, ∀ k ≥ n, T.rank ((T.step m)^[k] x) = T.rank ((T.step m)^[n] x) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ k ≥ n,
      T.rank ((T.step m)^[k] x) ≤ T.rank ((T.step m)^[n] x) := by
    have hf : Set.Finite (Set.range (fun k => T.rank ((T.step m)^[k] x))) := by
      exact Set.Finite.subset
        (Set.toFinite (Finset.image (fun y => T.rank y) Finset.univ))
        (Set.range_subset_iff.mpr (fun k =>
          Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩))
    have hm := hf.toFinset.exists_max_image (fun k => k)
      ⟨_, hf.mem_toFinset.mpr ⟨0, rfl⟩⟩
    simp +zetaDelta at *
    exact ⟨hm.choose, fun k hk => hm.choose_spec k⟩
  refine ⟨n, fun k hk => le_antisymm (hn k hk) ?_⟩
  exact Nat.le_induction (by rfl)
    (fun k hk ih => by
      simpa only [Function.iterate_succ_apply'] using
        le_trans ih (T.improves m _)) k hk

structure RiceProperty
    (E : Arithmetic_Rice.PartialComputableEnumeration) where
  pred : ℕ → Prop
  hExtensional : Arithmetic_Rice.ExtensionalProperty E pred
  hNontrivial : Arithmetic_Rice.SemanticallyNontrivial pred

theorem rice_undecidable
    (E : Arithmetic_Rice.PartialComputableEnumeration) (dist : RiceProperty E) :
    ¬ ∃ decider : ℕ → Bool,
      ∀ program, decider program = true ↔ dist.pred program :=
  Arithmetic_Rice.rice_theorem E dist.pred dist.hExtensional dist.hNontrivial

/-- A FormalMind qualia model supplies the experience labeling. -/
def qualiaLabeling {X Experience Report : Type u}
    (Q : FormalMind.Qualia X Experience Report) : StateLabeling X Experience :=
  ⟨Q.experience⟩

/-- Action-invariant experience induces a action congruence. -/
def qualiaActionCongruence {M X Experience Report : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (Q : FormalMind.Qualia X Experience Report)
    (hExperience : ∀ m x, Q.experience (A.act m x) = Q.experience x) :
    UAM_ActionCongruence.ActionCongruence M X A :=
  labelingActionCongruence A (qualiaLabeling Q) hExperience

/-- Consciousness is orbit-complete when it is preserved throughout each orbit. -/
def OrbitInvariance {M X Observation : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : FormalMind.Consciousness X Observation) : Prop :=
  ∀ x, C.conscious x → ∀ y ∈ UAM_MonoidAction.MonoidAction.orbit A x, C.conscious y

/-- An action preserving consciousness yields orbit completeness. -/
theorem action_preserves_to_orbitInvariance {M X Observation : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : FormalMind.Consciousness X Observation)
    (hPreserves : ∀ m x, C.conscious x → C.conscious (A.act m x)) :
    OrbitInvariance A C := by
  intro x hx y hy
  obtain ⟨m, rfl⟩ := hy
  exact hPreserves m x hx

/-- A valuation constant on congruence classes descends to the quotient. -/
theorem valuation_descends_to_quotient {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : UAM_ActionCongruence.ActionCongruence M X A)
    (RM : StateValuation X) (BR : QuotientValuation X C.rel RM) :
    ∃ riskOnQuotient : UAM_ActionCongruence.ActionQuotient M X A C → Rat,
      ∀ x, riskOnQuotient (UAM_ActionCongruence.quotientProj A C x) = RM.val x := by
  refine ⟨Quotient.lift RM.val (fun x y h => BR.invariant h), ?_⟩
  intro x
  rfl

/-!
## FALSE — documented counterexamples

* `R_eq f g → agreementIndex f g = 1` is false: distinct permutations can
  generate the same principal right ideal while disagreeing pointwise.
* State-output annotations do not generally define a congruence on transformations.
* Identity one-step density need not be one; its singleton orbit has density `1 / |X|`.
* Rice's theorem does not apply to the finite function space `Fin n → Fin n`.
* Congruence-preserving map stabilization requires `map_preserves`.
* Congruence lattices of arbitrary monoids need not be modular.
* A state quotient is not a monoid unless additional multiplication data exist on states.
-/


end ActionBridges
