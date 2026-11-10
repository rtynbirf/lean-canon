import Mathlib

/-!
# Adaptive agents — a Mathlib-normalized core

This module formalizes the seven-layer "adaptive agent" stack of POLYMATH-ATLAS
(observation streams → variational inference → policy selection → meta-optimization →
self-reference) using **Mathlib naming conventions**: every identifier describes the
formal object it denotes, never a metaphor.

The dictionary used here (see `RENAME_LOG.md`):

| metaphorical name    | formal name in this file  | what the object actually is                       |
|----------------------|---------------------------|---------------------------------------------------|
| `Reactor`            | `StreamTransformer`       | a map `ObservationStream → ObservationStream` that preserves liveness |
| `Compressor`         | `VariationalFamily`       | a prior together with a family of posteriors      |
| `Navigator`          | `ActivePolicyAgent`       | variational family + forward model + preferences + planner |
| `HolographicMonitor` | `MetaOptimizer`           | an agent together with a self-latent and an endomap of agent space |
| `GenesisConditions`  | `AdaptivePreconditions`   | the conjunction of three preconditions C1–C3      |
| `MinimalIntelligence`| `AdaptiveAgentSpec`       | a five-condition specification                    |
| `GenesisEvent`       | `ReflexiveAdaptiveAgent`  | an agent that is a fixed point of its own meta-optimizer |
| `AliveAt` / `Alive`  | `LiveAt` / `Live`         | liveness of a stream at a time / at all times     |
| `GenesisOf`          | `SelfMap` (`Endomap`)     | an endomorphism `α → α`                           |

**No custom axioms.** In particular the existence of a fixed point of a self-map is
*not* postulated: `not_forall_exists_fixed_point_selfMap` shows the unrestricted
statement is false, and `exists_fixed_point_selfMap` gives the correct
(Knaster–Tarski) form for monotone maps on a complete lattice.
-/

namespace PolymathAtlas.AdaptiveAgent

open Finset

/-! ## L1 — observation streams and liveness -/

/-- A single observation: a channel index carrying a real value. -/
structure Observation where
  channel : ℕ
  value : ℝ

/-- A stream of observations indexed by discrete time. -/
abbrev ObservationStream := ℕ → Observation

/-- The stream carries a nonzero signal at time `t`. -/
def Active (s : ObservationStream) (t : ℕ) : Prop := (s t).value ≠ 0

/-- The stream is still going to be active at some time `≥ t`. -/
def LiveAt (s : ObservationStream) (t : ℕ) : Prop := ∃ u, t ≤ u ∧ Active s u

/-- The stream never dies out. -/
def Live (s : ObservationStream) : Prop := ∀ t, LiveAt s t

theorem liveAt_of_le {s : ObservationStream} {t t' : ℕ} (h : t' ≤ t) (hl : LiveAt s t) :
    LiveAt s t' := by
  obtain ⟨u, hu, ha⟩ := hl
  exact ⟨u, le_trans h hu, ha⟩

theorem liveAt_of_live {s : ObservationStream} (h : Live s) (t : ℕ) : LiveAt s t := h t

/-- Liveness is exactly the statement that the set of active times is infinite. -/
theorem live_iff_setOf_active_infinite {s : ObservationStream} :
    Live s ↔ {t | Active s t}.Infinite := by
  constructor
  · intro h hfin
    obtain ⟨b, hb⟩ := hfin.bddAbove
    obtain ⟨u, hu, ha⟩ := h (b + 1)
    exact Nat.not_succ_le_self b (le_trans hu (hb ha))
  · intro h t
    by_contra hc
    simp only [LiveAt, not_exists, not_and] at hc
    refine h (Set.Finite.subset (Set.finite_Iio t) ?_)
    intro u hu
    exact lt_of_not_ge fun h' => hc u h' hu

/-- **L1.** A transformer of observation streams which preserves liveness. -/
structure StreamTransformer where
  toFun : ObservationStream → ObservationStream
  live_apply : ∀ s, Live s → Live (toFun s)

namespace StreamTransformer

instance : CoeFun StreamTransformer (fun _ => ObservationStream → ObservationStream) :=
  ⟨StreamTransformer.toFun⟩

/-- The identity transformer. -/
protected def id : StreamTransformer where
  toFun := _root_.id
  live_apply _ h := h

/-- Composition of stream transformers. -/
protected def comp (T₁ T₂ : StreamTransformer) : StreamTransformer where
  toFun := T₁.toFun ∘ T₂.toFun
  live_apply s hs := T₁.live_apply _ (T₂.live_apply s hs)

@[simp] theorem id_apply (s : ObservationStream) : StreamTransformer.id s = s := rfl

@[simp] theorem comp_apply (T₁ T₂ : StreamTransformer) (s : ObservationStream) :
    T₁.comp T₂ s = T₁ (T₂ s) := rfl

theorem comp_assoc (T₁ T₂ T₃ : StreamTransformer) :
    (T₁.comp T₂).comp T₃ = T₁.comp (T₂.comp T₃) := rfl

theorem liveAt_apply (T : StreamTransformer) {s : ObservationStream} (hs : Live s) (t : ℕ) :
    LiveAt (T s) t := T.live_apply s hs t

end StreamTransformer

/-- The stream shifted forward by `t`. -/
def truncate (s : ObservationStream) (t : ℕ) : ObservationStream := fun u => s (t + u)

/-- Truncating a live stream leaves it live: liveness is a tail property. -/
theorem live_truncate_of_live {s : ObservationStream} (h : Live s) (t : ℕ) :
    Live (truncate s t) := by
  intro n
  obtain ⟨u, hu, ha⟩ := h (t + n)
  have hu' : t + n ≤ u := hu
  refine ⟨u - t, by omega, ?_⟩
  have ht : t + (u - t) = u := by omega
  simpa [truncate, Active, ht] using ha

/-! ## L2 — variational inference: relative entropy and variational families -/

section KL

variable {α : Type*} [Fintype α]

/-- Relative entropy (Kullback–Leibler divergence) of `p` from `q` on a finite type. -/
noncomputable def klDiv (p q : α → ℝ) : ℝ := ∑ a, p a * Real.log (p a / q a)

theorem klDiv_self (p : α → ℝ) (hp : ∀ a, p a ≠ 0) : klDiv p p = 0 := by
  have h : ∀ a, p a * Real.log (p a / p a) = 0 := by
    intro a
    rw [div_self (hp a), Real.log_one, mul_zero]
  simp only [klDiv, h, Finset.sum_const_zero]

/-- **Gibbs' inequality.** Relative entropy between two positive weightings whose total
mass of `q` does not exceed that of `p` is nonnegative; in particular this applies to
two probability distributions. -/
theorem klDiv_nonneg {p q : α → ℝ} (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (hsum : ∑ a, q a ≤ ∑ a, p a) : 0 ≤ klDiv p q := by
  have key : ∀ a ∈ (univ : Finset α), p a * Real.log (q a / p a) ≤ q a - p a := by
    intro a _
    have h1 : Real.log (q a / p a) ≤ q a / p a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hq a) (hp a))
    have h2 : p a * Real.log (q a / p a) ≤ p a * (q a / p a - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt (hp a))
    have hpa : p a ≠ 0 := ne_of_gt (hp a)
    have h3 : p a * (q a / p a - 1) = q a - p a := by
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hsum' : ∑ a, p a * Real.log (q a / p a) ≤ ∑ a, (q a - p a) := Finset.sum_le_sum key
  have hzero : ∑ a, (q a - p a) ≤ 0 := by
    rw [Finset.sum_sub_distrib]
    linarith
  have hlog : ∀ a, Real.log (p a / q a) = -Real.log (q a / p a) := by
    intro a
    rw [Real.log_div (ne_of_gt (hp a)) (ne_of_gt (hq a)),
      Real.log_div (ne_of_gt (hq a)) (ne_of_gt (hp a))]
    ring
  have : klDiv p q = -∑ a, p a * Real.log (q a / p a) := by
    simp only [klDiv, hlog, mul_neg, Finset.sum_neg_distrib]
  rw [this]
  linarith

end KL

/-- **L2.** A variational family: a strictly positive prior on a finite latent space
together with a strictly positive posterior for every observation. -/
structure VariationalFamily (Latent Obs : Type*) [Fintype Latent] where
  prior : Latent → ℝ
  posterior : Obs → Latent → ℝ
  prior_pos : ∀ z, 0 < prior z
  posterior_pos : ∀ o z, 0 < posterior o z
  prior_sum : ∑ z, prior z = 1
  posterior_sum : ∀ o, ∑ z, posterior o z = 1

namespace VariationalFamily

variable {Latent Obs : Type*} [Fintype Latent] (F : VariationalFamily Latent Obs)

/-- The complexity term of the variational free energy: the relative entropy of the
posterior from the prior. -/
noncomputable def complexity (o : Obs) : ℝ := klDiv (F.posterior o) F.prior

theorem complexity_nonneg (o : Obs) : 0 ≤ F.complexity o :=
  klDiv_nonneg (F.posterior_pos o) F.prior_pos (by rw [F.prior_sum, F.posterior_sum])

/-- Relative entropy between the posteriors of two observations. -/
noncomputable def posteriorDiv (o o' : Obs) : ℝ := klDiv (F.posterior o) (F.posterior o')

theorem posteriorDiv_nonneg (o o' : Obs) : 0 ≤ F.posteriorDiv o o' :=
  klDiv_nonneg (F.posterior_pos o) (F.posterior_pos o')
    (by rw [F.posterior_sum, F.posterior_sum])

@[simp] theorem posteriorDiv_self (o : Obs) : F.posteriorDiv o o = 0 :=
  klDiv_self _ fun z => ne_of_gt (F.posterior_pos o z)

end VariationalFamily

/-- A Lipschitz-style continuity bound for the posterior map, measured in relative
entropy against a distance `d` on observations. -/
structure KLContinuityBound {Latent Obs : Type*} [Fintype Latent]
    (F : VariationalFamily Latent Obs) (d : Obs → Obs → ℝ) (L : ℝ) : Prop where
  div_le : ∀ o o', F.posteriorDiv o o' ≤ L * d o o'

namespace KLContinuityBound

variable {Latent Obs : Type*} [Fintype Latent] {F : VariationalFamily Latent Obs}
  {d : Obs → Obs → ℝ} {L : ℝ}

/-- A continuity bound is necessarily nonnegative, because relative entropy is. -/
theorem mul_nonneg (h : KLContinuityBound F d L) (o o' : Obs) : 0 ≤ L * d o o' :=
  le_trans (F.posteriorDiv_nonneg o o') (h.div_le o o')

/-- If the distance is positive off the diagonal, the Lipschitz constant is nonnegative. -/
theorem nonneg_of_pos (h : KLContinuityBound F d L) {o o' : Obs} (hd : 0 < d o o') : 0 ≤ L := by
  nlinarith [h.mul_nonneg o o']

end KLContinuityBound

/-! ## L3 — active policy selection: expected free energy -/

/-- **L3.** An active-inference agent: a variational family over states, a forward model,
normalized log-preferences over states, and a planner. -/
structure ActivePolicyAgent (S A Latent : Type*) [Fintype Latent] where
  family : VariationalFamily Latent S
  forward : S → A → S
  preference : S → ℝ
  preference_nonpos : ∀ s, preference s ≤ 0
  plan : S → A

namespace ActivePolicyAgent

variable {S A Latent : Type*} [Fintype Latent] (M : ActivePolicyAgent S A Latent)

/-- Risk: the negative log-preference of the predicted outcome. -/
def risk (s : S) (a : A) : ℝ := -M.preference (M.forward s a)

theorem risk_nonneg (s : S) (a : A) : 0 ≤ M.risk s a := by
  simpa [risk] using M.preference_nonpos (M.forward s a)

/-- Ambiguity: the complexity of the posterior at the predicted outcome. -/
noncomputable def ambiguity (s : S) (a : A) : ℝ := M.family.complexity (M.forward s a)

theorem ambiguity_nonneg (s : S) (a : A) : 0 ≤ M.ambiguity s a :=
  M.family.complexity_nonneg _

/-- Expected free energy of taking action `a` in state `s`. -/
noncomputable def efe (s : S) (a : A) : ℝ := M.risk s a + M.ambiguity s a

/-- Expected free energy is nonnegative. -/
theorem efe_nonneg (s : S) (a : A) : 0 ≤ M.efe s a :=
  add_nonneg (M.risk_nonneg s a) (M.ambiguity_nonneg s a)

/-- Accumulating expected free energy along a plan never decreases below the initial
value; in particular the accumulated value stays nonnegative. -/
theorem efe_foldl_ge_init (l : List (S × A)) (init : ℝ) :
    init ≤ l.foldl (fun acc p => acc + M.efe p.1 p.2) init := by
  induction l generalizing init with
  | nil => simp
  | cons p l ih =>
      refine le_trans ?_ (ih (init + M.efe p.1 p.2))
      simpa using M.efe_nonneg p.1 p.2

theorem efe_foldl_nonneg_of_init_nonneg (l : List (S × A)) (init : ℝ) (h : 0 ≤ init) :
    0 ≤ l.foldl (fun acc p => acc + M.efe p.1 p.2) init :=
  le_trans h (M.efe_foldl_ge_init l init)

/-- The trajectory generated by the planner from a state. -/
def trajectory (x : S) : ℕ → S := fun n => (fun y => M.forward y (M.plan y))^[n] x

@[simp] theorem trajectory_zero (x : S) : M.trajectory x 0 = x := rfl

@[simp] theorem trajectory_succ (x : S) (n : ℕ) :
    M.trajectory x (n + 1) = M.forward (M.trajectory x n) (M.plan (M.trajectory x n)) :=
  Function.iterate_succ_apply' _ _ _

/-- A state fixed by the planner stays fixed forever. -/
theorem trajectory_eq_of_fixed {x : S} (h : M.forward x (M.plan x) = x) (n : ℕ) :
    M.trajectory x n = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [trajectory_succ, ih, h]

end ActivePolicyAgent

/-! ## L4 — meta-optimization and self-maps -/

/-- `SelfMap α` is an endomorphism of `α`. (The "genesis operator" is nothing but an
endomap.) -/
abbrev SelfMap (α : Type*) := α → α

/-- Alias for `SelfMap`. -/
abbrev Endomap (α : Type*) := SelfMap α

/-- The unrestricted claim "every self-map has a fixed point" is **false**: `Bool.not`
has none. This is why the fixed-point statement below is restricted to monotone maps on
a complete lattice instead of being postulated as an axiom. -/
theorem not_forall_exists_fixed_point_selfMap :
    ¬ ∀ (α : Type) (_ : Nonempty α) (f : SelfMap α), ∃ x, f x = x := by
  intro h
  obtain ⟨x, hx⟩ := h Bool ⟨true⟩ not
  cases x <;> simp at hx

/-- **Knaster–Tarski.** A monotone self-map of a complete lattice has a fixed point. -/
theorem exists_fixed_point_selfMap {α : Type*} [CompleteLattice α] (f : α →o α) :
    ∃ x, f x = x :=
  ⟨OrderHom.lfp f, OrderHom.map_lfp f⟩

/-- An idempotent self-map has a fixed point as soon as its domain is inhabited. -/
theorem exists_fixed_point_of_idempotent {α : Type*} [Nonempty α] (f : SelfMap α)
    (h : ∀ x, f (f x) = f x) : ∃ x, f x = x :=
  ⟨f (Classical.arbitrary α), h _⟩

/-- **L4.** A meta-optimizer: an active-inference agent equipped with a latent code for
itself and with an endomap of agent space (the meta-update). -/
structure MetaOptimizer (S A Latent : Type*) [Fintype Latent] where
  agent : ActivePolicyAgent S A Latent
  selfLatent : Latent
  metaUpdate : SelfMap (ActivePolicyAgent S A Latent)

/-! ## L5–L6 — preconditions and the adaptive-agent specification -/

/-- **L5.** The three preconditions C1–C3 for adaptive behaviour. -/
structure AdaptivePreconditions {S A Latent : Type*} [Fintype Latent]
    (M : ActivePolicyAgent S A Latent) (s : ObservationStream) (x : S) : Prop where
  /-- C1: the sensory stream never dies out. -/
  live : Live s
  /-- C2: the planner minimizes expected free energy at the current state. -/
  optimal : ∀ a, M.efe x (M.plan x) ≤ M.efe x a
  /-- C3: the latent code genuinely compresses — two distinct states share a posterior. -/
  compresses : ∃ y z : S, y ≠ z ∧ M.family.posterior y = M.family.posterior z

/-- Failure of C1 already refutes the preconditions. -/
theorem neg_adaptivePreconditions_of_neg_c1 {S A Latent : Type*} [Fintype Latent]
    {M : ActivePolicyAgent S A Latent} {s : ObservationStream} {x : S} (h : ¬ Live s) :
    ¬ AdaptivePreconditions M s x := fun hc => h hc.live

/-- Failure of C2 already refutes the preconditions. -/
theorem neg_adaptivePreconditions_of_neg_c2 {S A Latent : Type*} [Fintype Latent]
    {M : ActivePolicyAgent S A Latent} {s : ObservationStream} {x : S}
    (h : ¬ ∀ a, M.efe x (M.plan x) ≤ M.efe x a) : ¬ AdaptivePreconditions M s x :=
  fun hc => h hc.optimal

/-- Failure of C3 already refutes the preconditions. -/
theorem neg_adaptivePreconditions_of_neg_c3 {S A Latent : Type*} [Fintype Latent]
    {M : ActivePolicyAgent S A Latent} {s : ObservationStream} {x : S}
    (h : ¬ ∃ y z : S, y ≠ z ∧ M.family.posterior y = M.family.posterior z) :
    ¬ AdaptivePreconditions M s x := fun hc => h hc.compresses

/-- **L6.** The five-condition specification of an adaptive agent: the three
preconditions, plus effectiveness (the agent actually changes some state) and
boundedness of expected free energy. -/
structure AdaptiveAgentSpec {S A Latent : Type*} [Fintype Latent]
    (M : ActivePolicyAgent S A Latent) (s : ObservationStream) (x : S) : Prop where
  /-- C1–C3. -/
  toAdaptivePreconditions : AdaptivePreconditions M s x
  /-- C4: the policy is not inert. -/
  acts : ∃ y : S, M.forward y (M.plan y) ≠ y
  /-- C5: expected free energy stays bounded. -/
  bounded : ∃ B : ℝ, ∀ (y : S) (a : A), M.efe y a ≤ B

namespace AdaptiveAgentSpec

variable {S A Latent : Type*} [Fintype Latent] {M : ActivePolicyAgent S A Latent}
  {s : ObservationStream} {x : S}

theorem live (h : AdaptiveAgentSpec M s x) : Live s := h.toAdaptivePreconditions.live

/-- An agent satisfying the specification observes a stream that is live at every time. -/
theorem live_at (h : AdaptiveAgentSpec M s x) (t : ℕ) : LiveAt s t :=
  h.toAdaptivePreconditions.live t

/-- The bound in C5 is nonnegative, since expected free energy is. -/
theorem exists_nonneg_bound (h : AdaptiveAgentSpec M s x) [Nonempty S] [Nonempty A] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (y : S) (a : A), M.efe y a ≤ B := by
  obtain ⟨B, hB⟩ := h.bounded
  exact ⟨B, le_trans (M.efe_nonneg (Classical.arbitrary S) (Classical.arbitrary A))
    (hB _ _), hB⟩

end AdaptiveAgentSpec

/-- If the stream is dead at some time, no agent meets the specification on it. -/
theorem neg_adaptiveAgentSpec_of_neg_live_at {S A Latent : Type*} [Fintype Latent]
    {M : ActivePolicyAgent S A Latent} {s : ObservationStream} {x : S} {t : ℕ}
    (h : ¬ LiveAt s t) : ¬ AdaptiveAgentSpec M s x := fun hs => h (hs.live_at t)

/-! ## L7 — reflexive closure -/

/-- **L7.** A reflexive adaptive agent: an agent that meets the specification, is a fixed
point of its own meta-update, and distinguishes its self-latent from some other latent
(so its self-model is not degenerate). -/
structure ReflexiveAdaptiveAgent (S A Latent : Type*) [Fintype Latent]
    extends MetaOptimizer S A Latent where
  stream : ObservationStream
  state : S
  metaUpdate_fix : metaUpdate agent = agent
  spec : AdaptiveAgentSpec agent stream state
  otherLatent : Latent
  self_ne : selfLatent ≠ otherLatent

namespace ReflexiveAdaptiveAgent

variable {S A Latent : Type*} [Fintype Latent] (R : ReflexiveAdaptiveAgent S A Latent)

/-- A reflexive adaptive agent satisfies the adaptive-agent specification. -/
theorem adaptive_agent_spec : AdaptiveAgentSpec R.agent R.stream R.state := R.spec

/-- A reflexive adaptive agent satisfies the three preconditions. -/
theorem adaptive_preconditions : AdaptivePreconditions R.agent R.stream R.state :=
  R.spec.toAdaptivePreconditions

/-- Its observation stream is live at every time. -/
theorem live_at (t : ℕ) : LiveAt R.stream t := R.spec.live_at t

/-- Self-reference forces the latent space to carry at least two distinct codes: the
capacity for recursion is not vacuous. -/
theorem self_nontrivial (R : ReflexiveAdaptiveAgent S A Latent) : Nontrivial Latent :=
  ⟨⟨R.selfLatent, R.otherLatent, R.self_ne⟩⟩

/-- Its meta-update fixes the agent: the reflexive agent is a fixed point of an endomap
of agent space. -/
theorem exists_fixed_point_metaUpdate : ∃ M, R.metaUpdate M = M :=
  ⟨R.agent, R.metaUpdate_fix⟩

end ReflexiveAdaptiveAgent

end PolymathAtlas.AdaptiveAgent
