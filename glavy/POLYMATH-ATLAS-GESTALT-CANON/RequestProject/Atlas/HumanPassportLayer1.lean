import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-!
# Human Passport — Layer 1: operational core and formal predictions

The file separates mathematical consequences from empirical premises.  In
particular, observations labelled `empirical` cannot, by their label alone,
turn a distinct claim into a mechanistic one.  Predictions P1–P3 are therefore
proved from an explicit `EmpiricalPredictionModel`, whose fields are the
empirical assumptions that must be tested outside Lean.
-/

namespace HumanPassportLayer1

open Set MeasureTheory

noncomputable section

-- Claim types and evidence status

inductive ClaimKind where
  | empirical
  | structural
  | mechanistic
  | normative
  | existential
  deriving DecidableEq, Repr

inductive EvidenceStatus where
  | proposed
  | operationalized
  | preregistered
  | tested
  | replicated
  deriving DecidableEq, Repr

structure ClaimLabel where
  kind : ClaimKind
  status : EvidenceStatus
  deriving DecidableEq, Repr

def empirical_claim (c : ClaimKind) : Prop := c = .empirical

def mechanistic_claim (c : ClaimKind) : Prop := c = .mechanistic

/-- A single claim cannot be both empirical and mechanistic.  This is the
precise type-level fact behind the methodological slogan that an empirical
label does not itself establish a mechanism.  It does not deny that separate
empirical evidence can support a separately specified mechanistic model. -/
theorem no_empirical_implies_mechanistic (c : ClaimKind) :
    empirical_claim c → ¬ mechanistic_claim c := by
  intro hc hm
  cases c <;> simp [empirical_claim, mechanistic_claim] at hc hm

/-- Merely labelling some data empirical leaves the kind of an independent
claim completely unconstrained. -/
theorem empirical_label_does_not_determine_claim
    (data : ClaimLabel) (m : ClaimKind) (_hdata : data.kind = .empirical) :
    m = .mechanistic ∨ m ≠ .mechanistic := by
  exact eq_or_ne m .mechanistic

-- Macro-level observations and scope

structure SocietyObservation where
  gdpPerCapitaPPP15k : ℝ
  urbanizationPercent : ℝ
  laborFragments : ℕ
  energyGridGW : ℝ
  population : ℕ
  peaceful : Bool
  productivity : ℝ
  energyConsumptionPerCapita : ℝ
  coordinationCost : ℝ
  aiPenetration : ℝ
  automationSpeed : ℝ
  entropyPhysical : ℝ
  entropyInformation : ℝ

def inDomain (s : SocietyObservation) : Prop :=
  1 < s.gdpPerCapitaPPP15k ∧
  60 < s.urbanizationPercent ∧
  4 ≤ s.laborFragments ∧
  1 < s.energyGridGW ∧
  10_000_000 < s.population ∧
  s.peaceful = true

def sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- A smooth scope score.  This is a score, not a probability distribution. -/
def applicability (s : SocietyObservation) : ℝ :=
  sigmoid ((s.gdpPerCapitaPPP15k - 1) / 0.5) *
  sigmoid ((s.urbanizationPercent - 60) / 10) *
  sigmoid ((s.energyGridGW - 1) / 0.5) *
  (if s.peaceful then 1 else 0)

-- Temporal Adaptation Lag

def disruption_rate (t : ℝ) : ℝ := 0.1 + 0.02 * t

def adaptation_rate (t : ℝ) : ℝ := 0.05 + 0.01 * t

/-- Accumulated rate mismatch on `[0,T]`. -/
def TAL (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, (disruption_rate t - adaptation_rate t)

private theorem rateMismatch_continuous :
    Continuous (fun t : ℝ => disruption_rate t - adaptation_rate t) := by
  unfold disruption_rate adaptation_rate
  fun_prop

/-- A strict interval is required: for `T1 = T2` the desired strict conclusion
would be false even though a pointwise premise over the degenerate interval
could hold. -/
theorem TAL_monotone (T1 T2 : ℝ) (hT : T1 < T2)
    (h_rate : ∀ t ∈ Icc T1 T2, disruption_rate t > adaptation_rate t) :
    TAL T1 < TAL T2 := by
  let f : ℝ → ℝ := fun t => disruption_rate t - adaptation_rate t
  have hf : Continuous f := rateMismatch_continuous
  have hpos : 0 < ∫ t in T1..T2, f t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hf.intervalIntegrable T1 T2) _ hT
    intro t ht
    exact sub_pos.mpr (h_rate t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (μ := volume) (0 : ℝ) T1)
    (hf.intervalIntegrable (μ := volume) T1 T2)
  change TAL T1 + (∫ t in T1..T2, f t) = TAL T2 at hadd
  linarith

/-- TAL is continuous because its rate mismatch is continuous (and hence
interval-integrable on every compact interval). -/
theorem TAL_continuous (T : ℝ) : ContinuousAt TAL T := by
  have hcontinuous : Continuous TAL := by
    exact intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => rateMismatch_continuous.intervalIntegrable a b) 0
  exact hcontinuous.continuousAt

-- Information and physical entropy

/-- A continuous-density entropy functional relative to the ambient volume
measure.  This is not a discrete Shannon entropy unless the measure and support
are replaced accordingly. -/
def entropy (p : ℝ → ℝ) (support : Set ℝ) : ℝ :=
  - ∫ x in support, p x * Real.log (p x)

/-- Temporary scalar proxy.  Its name explicitly avoids claiming that a
product of three scalars is genuine multivariate mutual information. -/
def joint_mutual_information_proxy (E I K : ℝ) : ℝ := E * I * K

def complexity (E I K : ℝ) : ℝ := joint_mutual_information_proxy E I K

def entropy_phys (system : SocietyObservation) : ℝ := system.entropyPhysical

def entropy_info (system : SocietyObservation) : ℝ := system.entropyInformation

/-- Landauer lower-bound expression with all physical constants explicit.
`temperature` is absolute temperature and `kB` is Boltzmann's constant in the
chosen unit system. -/
def landauer_bound (information kB temperature : ℝ) : ℝ :=
  information * kB * temperature * Real.log 2

/-- The scalar-product proxy is not invariant under a nontrivial rescaling. -/
theorem complexity_not_scale_invariant (E I K c : ℝ) (hcne : c ≠ 1)
    (hEIK : E * I * K ≠ 0) :
    complexity (c * E) I K ≠ complexity E I K := by
  unfold complexity joint_mutual_information_proxy
  intro h
  have h' : c * (E * I * K) = 1 * (E * I * K) := by
    calc
      c * (E * I * K) = (c * E) * I * K := by ring
      _ = E * I * K := h
      _ = 1 * (E * I * K) := by ring
  exact hcne (mul_right_cancel₀ hEIK h')

-- Optimisation and predictors

structure Optimizer where
  loss : SocietyObservation → ℝ
  gradient : SocietyObservation → ℝ

def Lambda (s : SocietyObservation) : ℝ :=
  s.productivity / (s.energyConsumptionPerCapita + 1)

def K_comp (s : SocietyObservation) : ℝ :=
  s.aiPenetration / (1 - s.aiPenetration + 0.01)

def Phi (s : SocietyObservation) : ℝ :=
  s.coordinationCost * (1 + (s.laborFragments : ℝ) ^ 2)

/-- Finite-difference growth of a metric between two observations. -/
def growth_rate (metric : SocietyObservation → ℝ)
    (before after : SocietyObservation) : ℝ := metric after - metric before

/-- All nonlogical content needed by predictions P1–P3 is exposed here rather
than hidden behind unproved theorems.  A concrete study must construct this
structure from preregistered assumptions and validated data. -/
structure EmpiricalPredictionModel where
  baseline : SocietyObservation → SocietyObservation
  followup : SocietyObservation → SocietyObservation
  p1_effect : ∀ s, inDomain s → K_comp s < 0.5 →
    growth_rate Lambda s (followup s) <
      growth_rate Lambda (baseline s) (followup (baseline s))
  p2_effect : ∀ industry1 industry2,
    inDomain industry1 → inDomain industry2 →
    Phi industry1 > Phi industry2 →
    industry1.automationSpeed > industry2.automationSpeed
  p3_effect : ∀ s1 s2,
    inDomain s1 → inDomain s2 →
    Lambda s1 < Lambda s2 →
    s1.aiPenetration > s2.aiPenetration →
    growth_rate K_comp s1 (followup s1) >
      growth_rate K_comp s2 (followup s2)

/-- P1, conditional on the explicitly supplied empirical model. -/
theorem P1 (M : EmpiricalPredictionModel) (s : SocietyObservation)
    (hs : inDomain s) (hk : K_comp s < 0.5) :
    growth_rate Lambda s (M.followup s) <
      growth_rate Lambda (M.baseline s) (M.followup (M.baseline s)) :=
  M.p1_effect s hs hk

/-- P2, conditional on the explicitly supplied empirical model. -/
theorem P2 (M : EmpiricalPredictionModel) (industry1 industry2 : SocietyObservation)
    (h1 : inDomain industry1) (h2 : inDomain industry2)
    (hPhi : Phi industry1 > Phi industry2) :
    industry1.automationSpeed > industry2.automationSpeed :=
  M.p2_effect industry1 industry2 h1 h2 hPhi

/-- P3, conditional on the explicitly supplied empirical model. -/
theorem P3 (M : EmpiricalPredictionModel) (s1 s2 : SocietyObservation)
    (h1 : inDomain s1) (h2 : inDomain s2)
    (hLambda : Lambda s1 < Lambda s2)
    (hAI : s1.aiPenetration > s2.aiPenetration) :
    growth_rate K_comp s1 (M.followup s1) >
      growth_rate K_comp s2 (M.followup s2) :=
  M.p3_effect s1 s2 h1 h2 hLambda hAI

-- Verdict and protocol

inductive TestVerdict where
  | supported
  | refuted
  | inconclusive
  | outOfScope
  deriving DecidableEq, Repr

def scopedVerdict (applicable rejected decisive : Bool) : TestVerdict :=
  if !applicable then .outOfScope
  else if rejected then .refuted
  else if decisive then .supported
  else .inconclusive

structure PredictionProtocol where
  population : SocietyObservation → Prop
  exposure : SocietyObservation → ℝ
  outcome : SocietyObservation → ℝ
  lowerYear : ℕ
  upperYear : ℕ
  rejectionRegion : ℝ → Prop
  timeOrder : lowerYear < upperYear

/-- An in-scope test can never be classified as out of scope. -/
theorem scope_not_an_escape (rejected decisive : Bool) :
    scopedVerdict true rejected decisive ≠ .outOfScope := by
  cases rejected <;> cases decisive <;> simp [scopedVerdict]

-- Preserved finite-change stress test from the earlier operational core.

def tal (adaptationDuration disruptionDuration : ℝ) : ℝ :=
  adaptationDuration - disruptionDuration

def talChange
    (adaptationBefore disruptionBefore adaptationAfter disruptionAfter : ℝ) : ℝ :=
  tal adaptationAfter disruptionAfter - tal adaptationBefore disruptionBefore

def multiplicativeComplexity (energy information coordination : ℝ) : ℝ :=
  energy * information * coordination

theorem operational_core_stress_test :
    (∀ a₀ d₀ a₁ d₁ : ℝ,
      talChange a₀ d₀ a₁ d₁ = (a₁ - a₀) - (d₁ - d₀)) ∧
    (∀ a d da dd : ℝ, dd < da →
      0 < tal (a + da) (d + dd) - tal a d) ∧
    (∀ x : ℝ, ¬ (0 < x ∧ x < 0)) ∧
    (∀ E I K c : ℝ, 0 < c → c ≠ 1 → E * I * K ≠ 0 →
      multiplicativeComplexity (c * E) I K ≠
        multiplicativeComplexity E I K) ∧
    (∀ rejected decisive : Bool,
      scopedVerdict true rejected decisive ≠ .outOfScope) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a₀ d₀ a₁ d₁
    unfold talChange tal
    ring
  · intro a d da dd h
    unfold tal
    linarith
  · intro x hx
    linarith
  · intro E I K c _hc hne hnz
    exact complexity_not_scale_invariant E I K c hne hnz
  · exact scope_not_an_escape

end

end HumanPassportLayer1
