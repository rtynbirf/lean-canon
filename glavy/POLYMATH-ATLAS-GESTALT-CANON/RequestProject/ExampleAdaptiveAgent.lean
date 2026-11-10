import RequestProject.AdaptiveAgent

/-!
# A concrete adaptive agent

The definitions of `RequestProject.AdaptiveAgent` are non-vacuous: this file builds an
explicit `ReflexiveAdaptiveAgent` over `S = A = Latent = Bool` and checks every
condition of `AdaptiveAgentSpec` on it.

The agent observes a constantly active stream, uses the uniform prior and the uniform
posterior (so both its complexity and its risk vanish), flips its state at every step
(so it is not inert), and is a fixed point of the identity meta-update.
-/

namespace PolymathAtlas.AdaptiveAgent.Demo

open PolymathAtlas.AdaptiveAgent

/-- A stream which is active at every time. -/
def pulse : ObservationStream := fun _ => ⟨0, 1⟩

theorem pulse_live : Live pulse := fun t => ⟨t, le_refl t, by simp [pulse, Active]⟩

/-- The uniform distribution on `Bool`. -/
noncomputable def uniform : Bool → ℝ := fun _ => 1 / 2

theorem uniform_pos (z : Bool) : 0 < uniform z := by norm_num [uniform]

theorem uniform_sum : ∑ z : Bool, uniform z = 1 := by
  simp [uniform, Finset.sum_const]

/-- The uniform variational family: prior and posterior are both uniform, so the agent
compresses every state to the same code. -/
noncomputable def uniformFamily : VariationalFamily Bool Bool where
  prior := uniform
  posterior := fun _ => uniform
  prior_pos := uniform_pos
  posterior_pos := fun _ => uniform_pos
  prior_sum := uniform_sum
  posterior_sum := fun _ => uniform_sum

@[simp] theorem uniformFamily_complexity (o : Bool) : uniformFamily.complexity o = 0 :=
  klDiv_self _ fun z => ne_of_gt (uniform_pos z)

/-- The flipping agent: it toggles its state, has flat preferences and plans `true`. -/
noncomputable def flipAgent : ActivePolicyAgent Bool Bool Bool where
  family := uniformFamily
  forward := fun s _ => !s
  preference := fun _ => 0
  preference_nonpos := fun _ => le_refl 0
  plan := fun _ => true

@[simp] theorem flipAgent_efe (s a : Bool) : flipAgent.efe s a = 0 := by
  simp [ActivePolicyAgent.efe, ActivePolicyAgent.risk, ActivePolicyAgent.ambiguity, flipAgent]

theorem flipAgent_preconditions (x : Bool) : AdaptivePreconditions flipAgent pulse x where
  live := pulse_live
  optimal a := by simp
  compresses := ⟨false, true, by simp, rfl⟩

theorem flipAgent_spec (x : Bool) : AdaptiveAgentSpec flipAgent pulse x where
  toAdaptivePreconditions := flipAgent_preconditions x
  acts := ⟨false, by simp [flipAgent]⟩
  bounded := ⟨0, by simp⟩

/-- The full seven-layer object: a reflexive adaptive agent. -/
noncomputable def flipReflexive : ReflexiveAdaptiveAgent Bool Bool Bool where
  agent := flipAgent
  selfLatent := true
  metaUpdate := id
  stream := pulse
  state := false
  metaUpdate_fix := rfl
  spec := flipAgent_spec false
  otherLatent := false
  self_ne := by simp

theorem flipReflexive_live_at (t : ℕ) : LiveAt flipReflexive.stream t :=
  flipReflexive.live_at t

theorem flipReflexive_self_nontrivial : Nontrivial Bool :=
  ReflexiveAdaptiveAgent.self_nontrivial flipReflexive

end PolymathAtlas.AdaptiveAgent.Demo
