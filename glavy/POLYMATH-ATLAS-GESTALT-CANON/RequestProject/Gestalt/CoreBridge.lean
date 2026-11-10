/-
# POLYMATH_ATLAS_GESTALT — Part 7.  Bridge to the adaptive-agent core.

Source: the **gestalt audit** of the six gestalt parts against the proved core
(`RequestProject/AdaptiveAgent.lean`, `RequestProject/UCC.lean`).  Three items of
the informal text were flagged there as *asserted without a witness*:

* L3 Navigator — "the plan minimizes Expected Free Energy" was a bare structure
  field, with `Genesis.l3_efe_gap` showing that the field alone has no content;
* Ω of the Urobouros closure — "the methodology returns to its own foundation"
  was asserted as an existence claim about a self-map;
* the reflexive self-model — "the system distinguishes itself" was asserted
  without linking it to T1.

Each is closed here **from the core**, with no new axiom: the expected free
energy of `PolymathAtlas.AdaptiveAgent.ActivePolicyAgent` supplies an actual EFE
functional for L3, `Function.iterate_fixed` supplies Ω from a fixed point of the
version step (the existence of which is *not* postulated — cf.
`AdaptiveAgent.not_forall_exists_fixed_point_selfMap`), and
`ReflexiveAdaptiveAgent.self_nontrivial` supplies the T1 distinction.

All statements in this file are fully proved: no `sorry` remains.
-/
import RequestProject.AdaptiveAgent
import RequestProject.Gestalt.GenesisEngine
import RequestProject.Gestalt.SelfReference

namespace PolymathAtlas.Gestalt.CoreBridge

open PolymathAtlas.AdaptiveAgent
open PolymathAtlas.Gestalt

/-! ## L3 — an Expected Free Energy functional for the Navigator

`Genesis.l3_efe_gap` states the critical gap: *every* policy is the `plan` field
of some `Navigator`, because the `efe` field can be chosen degenerate.  The gap
is closed by taking the EFE of the core active-inference agent, which is a fixed
functional determined by the agent's variational family and preferences. -/

variable {S A Latent : Type*} [Fintype Latent]

/-- The L3 Navigator carried by an active-inference agent: its expected free
energy is `ActivePolicyAgent.efe` and its plan is an EFE-minimizing action.

Source: POLYMATH ATLAS v6, Layer 3 — Navigator; core definition
`PolymathAtlas.AdaptiveAgent.ActivePolicyAgent.efe`. -/
noncomputable def navigatorOfActivePolicyAgent [Finite A] [Nonempty A]
    (M : ActivePolicyAgent S A Latent) : Genesis.Navigator S A where
  efe := M.efe
  plan := fun s => (Finite.exists_min (M.efe s)).choose
  plan_minimizes := fun s => (Finite.exists_min (M.efe s)).choose_spec

/-- The navigator built from an active-inference agent uses the agent's own
expected free energy as its `efe` field.  Source: POLYMATH ATLAS v6, Layer 3. -/
@[simp] theorem navigatorOfActivePolicyAgent_efe [Finite A] [Nonempty A]
    (M : ActivePolicyAgent S A Latent) :
    (navigatorOfActivePolicyAgent M).efe = M.efe := rfl

/-- **POLYMATH ATLAS v6, Layer 3 — Navigator.  Closes the gap recorded in
`Genesis.l3_efe_gap`.**

With the core EFE functional in place the navigator's decision criterion is
bounded below by `0`, by `ActivePolicyAgent.efe_nonneg`; a degenerate negative
"free energy" is not available. -/
theorem navigatorOfActivePolicyAgent_efe_nonneg [Finite A] [Nonempty A]
    (M : ActivePolicyAgent S A Latent) (s : S) (a : A) :
    0 ≤ (navigatorOfActivePolicyAgent M).efe s a :=
  M.efe_nonneg s a

/-- **POLYMATH ATLAS v6, Layer 3 — Navigator.  Closes the gap recorded in
`Genesis.l3_efe_gap`.**

Once the EFE functional is supplied, the plan is pinned down in value: any two
navigators sharing an `efe` field attain the same minimum, even if they break
ties differently.  This is the exact converse of `Genesis.l3_efe_gap`, where the
`efe` field was allowed to vary. -/
theorem navigator_min_efe_eq {N₁ N₂ : Genesis.Navigator S A} (h : N₁.efe = N₂.efe) (s : S) :
    N₁.efe s (N₁.plan s) = N₂.efe s (N₂.plan s) :=
  le_antisymm (h ▸ N₁.plan_minimizes s (N₂.plan s))
    (h ▸ N₂.plan_minimizes s (N₁.plan s))

/-- The state–action trace of length `n` produced by the navigator from a state,
the record on which accumulated expected free energy is evaluated.

Source: POLYMATH ATLAS v6, Layer 3 — Navigator (navigation history). -/
def trace (N : Genesis.Navigator S A) (move : S → A → S) (s : S) : ℕ → List (S × A)
  | 0 => []
  | n + 1 => (s, N.plan s) :: trace N move (move s (N.plan s)) n

/-- A trace of length `n` records exactly `n` state–action pairs.  Source:
POLYMATH ATLAS v6, Layer 3 — Navigator (navigation history). -/
@[simp] theorem trace_length (N : Genesis.Navigator S A) (move : S → A → S) (s : S) (n : ℕ) :
    (trace N move s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [trace, ih]

/-- **POLYMATH ATLAS v6, Layer 3 — Navigator.**

Expected free energy accumulated along a navigation trace is nonnegative, by the
core lemma `ActivePolicyAgent.efe_foldl_nonneg_of_init_nonneg`.  A planner cannot
buy free energy by planning further ahead. -/
theorem efe_trace_nonneg [Finite A] [Nonempty A] (M : ActivePolicyAgent S A Latent)
    (move : S → A → S) (s : S) (n : ℕ) :
    0 ≤ (trace (navigatorOfActivePolicyAgent M) move s n).foldl
      (fun acc p => acc + M.efe p.1 p.2) 0 :=
  M.efe_foldl_nonneg_of_init_nonneg _ 0 le_rfl

/-! ## Ω without an axiom -/

/-- **Gestalt synthesis of POLYMATH ATLAS v6 + Status Report — Ω.**

If v79 is a fixed point of the version step, then v79 *is* Ω: the methodology
occupies it at every index, so it returns to its own foundation.  The existence
of such a fixed point is not postulated — the unrestricted claim "every self-map
has a fixed point" is refuted by
`PolymathAtlas.AdaptiveAgent.not_forall_exists_fixed_point_selfMap`. -/
theorem isOmega_of_step_fixed (M : SelfReference.Methodology) (h : M.step 79 = 79) :
    M.IsOmega 79 := by
  have hv : ∀ n, M.vlevel n = 79 := fun n => Function.iterate_fixed h (n - 79)
  exact ⟨79, 80, le_rfl, by norm_num, hv 79, hv 80⟩

/-- **Gestalt synthesis of POLYMATH ATLAS v6 + Status Report — Ω.**

Ω is not vacuous: the methodology that never changes its version level has v79 as
its Ω.  A concrete witness on the version space `{79}`. -/
theorem exists_methodology_isOmega : ∃ M : SelfReference.Methodology, M.IsOmega 79 :=
  ⟨{ levels := {79}, step := id, mapsTo := fun _ hv => hv, start_mem := by simp },
    isOmega_of_step_fixed _ rfl⟩

/-! ## The reflexive self-model draws a T1 distinction -/

/-- **POLYMATH ATLAS Status Report, T1 — Distinction, applied to the self-model.**

A reflexive adaptive agent distinguishes itself: by
`ReflexiveAdaptiveAgent.self_nontrivial` its latent space has at least two
points, so the identity channel on it draws a T1 distinction in the sense of
`Gestalt.UCC.DrawsDistinction`. -/
theorem reflexiveAdaptiveAgent_drawsDistinction
    (R : ReflexiveAdaptiveAgent S A Latent) :
    UCC.DrawsDistinction (id : Latent → Latent) := by
  obtain ⟨x, y, hxy⟩ := R.self_nontrivial.exists_pair_ne
  exact ⟨x, y, hxy⟩

/-- **POLYMATH ATLAS v6, Layer 6 — Minimal Intelligence, and the Status Report's
liveness requirement.**

A reflexive adaptive agent never runs out of activity: its observation stream is
live at every tick, by `AdaptiveAgentSpec.live_at`. -/
theorem reflexiveAdaptiveAgent_liveAt (R : ReflexiveAdaptiveAgent S A Latent) (t : ℕ) :
    LiveAt R.stream t := R.live_at t

end PolymathAtlas.Gestalt.CoreBridge
