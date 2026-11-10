import RequestProject.Atlas.ModelLadder
import RequestProject.Atlas.GreenAnatomy
import RequestProject.Atlas.Arithmetic_Rice
import RequestProject.Atlas.UAM_DirectProduct
import RequestProject.Atlas.UAM_Semilattice
import RequestProject.Atlas.UAM_FormalMind_Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Constitutional bridges

This file formalizes the fifteen algebraic principles from the constitutional
bridge specification.  Several formulas in the specification were not
mathematically valid as written.  The corrections are kept close to the
intended meaning:

* a `Rat`-valued minimum needs a top element, so minimum quality vectors use
  `WithTop Rat`;
* Green `R`-equivalence classifies kernels, not pointwise equality, so it does
  not imply reliability one;
* confidence invariance acts on both arguments;
* information density is the image of the specified action (rather than an
  orbit independent of that action);
* an invariant protected zone induces an ideal of reset actions, not an ideal
  whose carrier is the state space;
* a two-sided negative ideal is incompatible with an element that lifts every
  negative element out of it, so resilience uses a right ideal;
* Rice's theorem concerns indices of partial computable functions, not the
  finite type of total maps `Fin n → Fin n`.
-/

namespace ConstitutionBridges

universe u

open UAM_MonoidAction UAM_MonoidAction.MonoidAction

/-! ## A. Metrics and calibration -/

/-- A state annotation assigns a label to every state. -/
structure StateAnnotation (State : Type u) (Label : Type u) where
  labelOf : State → Label

/-- Two transformations are observationally equivalent for an annotation when
all transformed states receive the same labels. -/
def AnnotationEquivalent {State Label : Type u}
    (ann : StateAnnotation State Label) (f g : State → State) : Prop :=
  ∀ s, ann.labelOf (f s) = ann.labelOf (g s)

/-- Without a compatibility law for labels and arbitrary postcomposition, the
largest always-sound congruence is the action kernel (pointwise equality).
It is a subrelation of annotation equivalence. -/
def annotationCongruence {State Label : Type u}
    (_ann : StateAnnotation State Label) :
    UAM_Congruence.IsCongruence (State → State) := by
  let action : UAM_MonoidAction.MonoidAction (State → State) State := {
    act := fun f s => f s
    one_act := rfl
    mul_act := by intro f g; rfl
  }
  exact action.actionKernel

/-
The strong annotation congruence implies equality of all labels.
-/
theorem annotationCongruence_sound {State Label : Type u}
    (ann : StateAnnotation State Label) (f g : State → State)
    (h : (annotationCongruence ann).r f g) :
    AnnotationEquivalent ann f g := by
  intro s
  have heq : f s = g s :=
    ((UAM_MonoidAction.MonoidAction.actionKernel_iff
      ({ act := fun k x => k x, one_act := rfl,
         mul_act := by intro a b; rfl } :
        UAM_MonoidAction.MonoidAction (State → State) State)) f g).mp h s
  exact congrArg ann.labelOf heq

/-- The existing equality congruence is a subrelation of annotation
observational equivalence. -/
theorem trivialCongruence_le_annotationEquivalent {State Label : Type u}
    (ann : StateAnnotation State Label) (f g : State → State)
    (h : (UAM_Congruence.trivial_congruence (State → State)).r f g) :
    AnnotationEquivalent ann f g := by
  subst g
  intro s
  rfl

/-- An `n`-dimensional rational quality vector. -/
abbrev QualityVector (n : Nat) := Fin n → Rat

/-- Pointwise multiplication gives quality vectors their ordinary monoid. -/
def qualityMonoid (n : Nat) : Monoid (QualityVector n) where
  one := fun _ => 1
  mul a b := fun i => a i * b i
  mul_assoc := by intro a b c; funext i; exact mul_assoc _ _ _
  one_mul := by intro a; funext i; exact one_mul _
  mul_one := by intro a; funext i; exact mul_one _

/-- Minimum aggregation needs a genuine top element as its identity. -/
abbrev MinQualityVector (n : Nat) := Fin n → WithTop Rat

/-- Pointwise minimum monoid for quality vectors with an infinite top score. -/
def minQualityMonoid (n : Nat) : Monoid (MinQualityVector n) where
  one := fun _ => ⊤
  mul a b := fun i => min (a i) (b i)
  mul_assoc := by intro a b c; funext i; exact min_assoc _ _ _
  one_mul := by intro a; funext i; exact min_eq_right (le_top)
  mul_one := by intro a; funext i; exact min_eq_left (le_top)

/-
Minimum quality vectors form an idempotent commutative monoid.
-/
theorem quality_min_semilattice (n : Nat) :
    letI := minQualityMonoid n
    UAM_Semilattice.IsSemilattice (MinQualityVector n) := by
  constructor;
  · exact fun a b => funext fun i => min_comm _ _;
  · intro a; exact funext (fun i => min_self (a i))

/-- The project's binary direct product is extended to a finite indexed
product by the standard function type. -/
abbrev FiniteDirectProduct (n : Nat) := Fin n → Rat

/-
A quality vector is canonically the finite direct product of its rational
components.
-/
theorem quality_is_direct_product (n : Nat) :
    letI := qualityMonoid n
    Nonempty (UAM_Morphism.MonoidMorphism
      (QualityVector n) (FiniteDirectProduct n)) := by
  use fun f => f;
  exact fun _ _ => rfl

/-- Fraction of states on which two finite-state transformations agree. -/
def reliabilityIndex {n : Nat} [NeZero n]
    (f g : ModelLadder.State n → ModelLadder.State n) : Rat :=
  (Fintype.card {s : ModelLadder.State n // f s = g s} : Rat) /
    (Fintype.card (ModelLadder.State n) : Rat)

/-
Reliability is symmetric.
-/
theorem reliability_symmetric {n : Nat} [NeZero n]
    (f g : ModelLadder.State n → ModelLadder.State n) :
    reliabilityIndex f g = reliabilityIndex g f := by
  simp +decide [ reliabilityIndex, eq_comm ]

/-
Pointwise equality gives reliability one.
-/
theorem reliability_one_of_eq {n : Nat} [NeZero n]
    {f g : ModelLadder.State n → ModelLadder.State n} (h : f = g) :
    reliabilityIndex f g = 1 := by
  simp +decide [ reliabilityIndex, h ];
  norm_cast

/-
Green `R`-equivalence does not imply reliability one: distinct constant
maps have the same full kernel but agree nowhere.
-/
theorem R_eq_does_not_force_reliability_one (n : Nat) [NeZero n] :
    ∃ f g : ModelLadder.State n → ModelLadder.State n,
      UAM_Green.R_eq f g ∧ reliabilityIndex f g ≠ 1 := by
  refine' ⟨ fun _ => 0, fun _ => ModelLadder.ladderNext n, _, _ ⟩ <;> norm_num [ reliabilityIndex ];
  exact GreenAnatomy.constants_R_eq _ _

/-
The proposed multiplicative triangle lower bound is false, even on
three states.  Agreement of `f` with `g` and agreement of `g` with `h` can
occur on disjoint sets.
-/
theorem reliability_triangle_fails :
    ∃ f g h : ModelLadder.State 1 → ModelLadder.State 1,
      ¬ reliabilityIndex f h ≥ reliabilityIndex f g * reliabilityIndex g h := by
  use fun _ => 0, fun s => if s = 0 then 0 else 1, fun s => if s = 0 then 1 else 1;
  unfold reliabilityIndex; norm_num;

/-- User-calibrated confidence threshold. -/
structure CalibratedConfidence (State : Type u) where
  rawConfidence : State → State → Rat
  threshold : Rat
  isConfident : State → State → Prop
  isConfident_def : ∀ s t, isConfident s t ↔ rawConfidence s t ≥ threshold

/-
Confidence is closed under simultaneous action on both compared states.
-/
theorem calibrated_as_stabilizer {M X : Type u} [Monoid M]
    (action : UAM_MonoidAction.MonoidAction M X)
    (cal : CalibratedConfidence X)
    (h : ∀ m s t, cal.rawConfidence (action.act m s) (action.act m t) =
      cal.rawConfidence s t) :
    ∀ m s t, cal.isConfident s t →
      cal.isConfident (action.act m s) (action.act m t) := by
  exact fun m s t hst => by rw [ cal.isConfident_def ] at *; linarith [ h m s t ] ;

/-- Information density of a particular action is the fraction of the state
space occurring in its image. -/
noncomputable def informationDensity {M X : Type u} [Monoid M] [Fintype X]
    (action : UAM_MonoidAction.MonoidAction M X) (m : M) : Rat :=
  (Set.ncard (Set.range (action.act m)) : Rat) / (Fintype.card X : Rat)

/-
The identity action has density one on a nonempty finite state space.
-/
theorem density_one_of_identity {M X : Type u} [Monoid M] [Fintype X]
    [Nonempty X] (action : UAM_MonoidAction.MonoidAction M X) :
    informationDensity action 1 = 1 := by
  unfold informationDensity; simp +decide [ action.one_act ] ;

/-
The constant-zero L2 action has density `1 / |X|`.
-/
theorem density_constant {n : Nat} [NeZero n] :
    informationDensity (ModelLadder.L2Action n) (ModelLadder.L2Zero n) =
      1 / (Fintype.card (ModelLadder.State n) : Rat) := by
  unfold informationDensity; simp +decide [ ModelLadder.L2Action, ModelLadder.L2Zero ] ;

/-! ## B. Emotional and social bridges -/

/-- A reflexive and transitive resonance relation. -/
structure EmpathyModel (State : Type u) where
  resonatesWith : State → State → Prop
  reflexive : ∀ s, resonatesWith s s
  transitive : ∀ s t u, resonatesWith s t → resonatesWith t u → resonatesWith s u

/-- The always-sound empathy congruence is the action kernel.  Resonance can
add observations, but without extra action-compatibility it cannot safely
identify transformations that act differently. -/
def empathyCongruence {State M : Type u} [Monoid M]
    (_emp : EmpathyModel State)
    (action : UAM_MonoidAction.MonoidAction M State) :
    UAM_Congruence.IsCongruence M :=
  action.actionKernel

/-
Empathy congruence is subsumed by the existing observer identity.
-/
theorem empathy_subsumes_observation {n : Nat} [NeZero n]
    (emp : EmpathyModel (ModelLadder.State n))
    (qual : FormalMind.Qualia (ModelLadder.State n)
      (ModelLadder.State n) (ModelLadder.State n))
    (_hEmp : ∀ s t, emp.resonatesWith s t →
      qual.experience s = qual.experience t) :
    ∀ f g : ModelLadder.L2Transform n,
      (empathyCongruence emp (ModelLadder.L2Action n)).r f g →
      (UAM_FormalMind_Bridge.ObserverIdentity
        (ModelLadder.L2Action n)).r f g := by
  intro f g hfg
  exact hfg

/-- Vulnerability detector with a guaranteed protected zone. -/
structure VulnerabilityDetector (State : Type u) where
  isVulnerable : State → Prop
  protectedZone : Set State
  guard : ∀ s, isVulnerable s → s ∈ protectedZone

/-- Actions that reset every state into the protected zone. -/
def ProtectiveResetActions {M State : Type u} [Monoid M]
    (action : UAM_MonoidAction.MonoidAction M State)
    (det : VulnerabilityDetector State) : Set M :=
  {m | ∀ s, action.act m s ∈ det.protectedZone}

/-
If one reset action exists, reset actions form a left ideal.
-/
theorem protected_as_left_ideal {M State : Type u} [Monoid M]
    (action : UAM_MonoidAction.MonoidAction M State)
    (det : VulnerabilityDetector State)
    (hReset : (ProtectiveResetActions action det).Nonempty) :
    UAM_Ideal.IsLeftIdeal (ProtectiveResetActions action det) := by
  obtain ⟨ m, hm ⟩ := hReset;
  constructor;
  · exact ⟨ m, hm ⟩;
  · exact fun a b hb => fun s => by simpa [ action.mul_act ] using hb ( action.act a s ) ;

/-- Emotional resilience uses a right ideal of negative states.  A two-sided
ideal would contradict `liftsOut` immediately. -/
structure EmotionalResilience (M : Type u) [Monoid M] where
  negativeStates : Set M
  negativeIdeal : UAM_Ideal.IsRightIdeal negativeStates
  resilient : M
  liftsOut : ∀ n ∈ negativeStates, resilient * n ∉ negativeStates

/-
A resilient element cannot itself be negative.
-/
theorem resilient_not_negative {M : Type u} [Monoid M]
    (res : EmotionalResilience M) :
    res.resilient ∉ res.negativeStates := by
  intro h;
  obtain ⟨ m, hm ⟩ := res.negativeIdeal;
  exact res.liftsOut _ h ( hm _ _ h )

/-- A trainer whose challenges never decrease empathy. -/
structure EmpathyTrainer (State : Type u) (M : Type u) [Monoid M] where
  empathyLevel : State → Nat
  challenge : M → State → State
  improves : ∀ m s, empathyLevel (challenge m s) ≥ empathyLevel s

/-
A finite training sequence never decreases empathy.
-/
theorem empathy_training_monotone {State M : Type u} [Monoid M]
    (trainer : EmpathyTrainer State M) (steps : List M) (s : State) :
    trainer.empathyLevel
      (steps.foldl (fun state m => trainer.challenge m state) s) ≥
      trainer.empathyLevel s := by
  induction' steps using List.reverseRecOn with steps m ih;
  · rfl;
  · simpa using le_trans ih ( trainer.improves m _ )

/-! ## C. Identity and legacy -/

/-- Group-based signing identity. -/
structure CryptographicIdentity (G : Type u) [Group G] where
  publicKey : G
  sign : G → G
  verify : G → G → Prop
  sign_correct : ∀ m, verify (sign m) m
  public_matches : ∀ m, verify (sign m) m →
    sign m * publicKey = publicKey * sign m

/-
Faithful signing is injective.
-/
theorem injective_signing {G : Type u} [Group G]
    (id_ : CryptographicIdentity G)
    (hFaithful : ∀ m₁ m₂, id_.sign m₁ = id_.sign m₂ → m₁ = m₂) :
    Function.Injective id_.sign := by
  exact fun m₁ m₂ h => hFaithful m₁ m₂ h

/-
Every cryptographic identity inherits the Cayley embedding.
-/
theorem crypto_to_cayley {G : Type u} [Group G]
    (id_ : CryptographicIdentity G) :
    ∃ phi : UAM_Morphism.MonoidMorphism G (UAM_Cayley.Transform G),
      phi.toFun id_.publicKey = UAM_Cayley.rho id_.publicKey := by
  refine' ⟨ _, rfl ⟩

/-- Digital inheritance modulo a project congruence. -/
structure DigitalWill (M : Type u) [Monoid M] where
  inheritance : UAM_Congruence.IsCongruence M
  successor : M → M
  inherits : ∀ m, inheritance.r m (successor m)
  final : M
  terminal : ∀ m, inheritance.r (successor m) final → successor m = final

/-
Repeated inheritance remains in the same congruence class.
-/
theorem will_stabilizes {M : Type u} [Monoid M]
    (will : DigitalWill M) (m : M) :
    will.inheritance.r (will.successor (will.successor m))
      (will.successor m) := by
  exact will.inheritance.symm _ _ (will.inherits (will.successor m))

/-! ## D. Risk and limits -/

/-- A cognitive distortion is a nontrivial extensional property of program
indices in an acceptable partial-computable enumeration. -/
structure CognitiveDistortion
    (enumeration : Arithmetic_Rice.PartialComputableEnumeration) where
  isDistorted : Nat → Prop
  nontrivial : Arithmetic_Rice.SemanticallyNontrivial isDistorted
  extensional : Arithmetic_Rice.ExtensionalProperty enumeration isDistorted

/-
Rice's theorem rules out a total Boolean distortion detector.
-/
theorem distortion_undecidable
    (enumeration : Arithmetic_Rice.PartialComputableEnumeration)
    (dist : CognitiveDistortion enumeration) :
    ¬ (∃ detector : Nat → Bool,
      ∀ program, detector program = true ↔ dist.isDistorted program) := by
  exact fun ⟨ detector, h ⟩ => Arithmetic_Rice.rice_theorem enumeration dist.isDistorted dist.extensional dist.nontrivial ⟨ detector, h ⟩

/-- Bounded risk attached to program indices. -/
structure RiskIndex where
  riskLevel : Nat → Rat
  bounded : ∀ c, 0 ≤ riskLevel c ∧ riskLevel c ≤ 1

/-- Behavioral risk means risk is invariant under extensional program equality. -/
def BehavioralRisk
    (enumeration : Arithmetic_Rice.PartialComputableEnumeration)
    (risk : RiskIndex) : Prop :=
  ∀ {a b}, Arithmetic_Rice.ProgramExtEq enumeration.Eval a b →
    risk.riskLevel a = risk.riskLevel b

/-
A nontrivial behavioral threshold is undecidable by Rice's theorem.
-/
theorem risk_threshold_undecidable
    (enumeration : Arithmetic_Rice.PartialComputableEnumeration)
    (risk : RiskIndex)
    (hNontrivial : ∃ low high,
      risk.riskLevel low < (1 / 2 : Rat) ∧
      ¬ risk.riskLevel high < (1 / 2 : Rat))
    (hBehavioral : BehavioralRisk enumeration risk) :
    ¬ (∃ evaluator : Nat → Bool,
      ∀ c, evaluator c = true ↔ risk.riskLevel c < (1 / 2 : Rat)) := by
  apply Arithmetic_Rice.rice_theorem enumeration
    (fun c => risk.riskLevel c < (1 / 2 : Rat))
  · intro a b hab
    change risk.riskLevel a < (1 / 2 : Rat) ↔
      risk.riskLevel b < (1 / 2 : Rat)
    rw [hBehavioral hab]
  · obtain ⟨low, high, hlow, hhigh⟩ := hNontrivial
    exact ⟨low, high, hlow, hhigh⟩

/-! ## Packaging -/

/-- Package of all bridge constructions.  It exposes reusable theorem maps
rather than postulating a particular constitution or program enumeration. -/
structure BridgePackage (n : Nat) [NeZero n] where
  annotation : ∀ (_ann : StateAnnotation (ModelLadder.State n) Bool),
    UAM_Congruence.IsCongruence
      (ModelLadder.State n → ModelLadder.State n)
  reliabilitySymmetric : ∀ f g : ModelLadder.State n → ModelLadder.State n,
    reliabilityIndex f g = reliabilityIndex g f
  identityDensity : informationDensity (ModelLadder.L2Action n) 1 = 1
  empathy : ∀ (_emp : EmpathyModel (ModelLadder.State n)),
    UAM_Congruence.IsCongruence (ModelLadder.L2Transform n)
  resilience : ∀ (res : EmotionalResilience (ModelLadder.L2Transform n)),
    res.resilient ∉ res.negativeStates
  riceDistortion : ∀ (E : Arithmetic_Rice.PartialComputableEnumeration)
    (dist : CognitiveDistortion E),
    ¬ (∃ detector : Nat → Bool,
      ∀ p, detector p = true ↔ dist.isDistorted p)

/-- Requested public name for the complete constitutional bridge package.
    (Named `ConstitutionBridgePackage` rather than `ConstitutionBridges`, so that
    the declaration does not repeat its own namespace.) -/
abbrev ConstitutionBridgePackage (n : Nat) [NeZero n] := BridgePackage n

/-- All corrected constitutional bridge APIs are jointly inhabited. -/
theorem constitution_bridges_exist (n : Nat) [NeZero n] :
    Nonempty (ConstitutionBridgePackage n) := by
  refine ⟨{
    annotation := ?_
    reliabilitySymmetric := ?_
    identityDensity := ?_
    empathy := ?_
    resilience := ?_
    riceDistortion := ?_
  }⟩
  · intro ann
    exact annotationCongruence ann
  · intro f g
    exact reliability_symmetric f g
  · exact density_one_of_identity (ModelLadder.L2Action n)
  · intro emp
    exact empathyCongruence emp (ModelLadder.L2Action n)
  · intro res
    exact resilient_not_negative res
  · intro enumeration dist
    exact distortion_undecidable enumeration dist

end ConstitutionBridges