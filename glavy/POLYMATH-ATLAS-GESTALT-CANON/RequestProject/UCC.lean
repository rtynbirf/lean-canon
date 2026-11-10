import Mathlib

/-!
# POLYMATH-ATLAS — the executable kernel: adaptive information-processing systems

This module is **self-contained**: it imports Mathlib only, and does not depend on any
other file of this project.  Everything lives in the namespace `PolymathAtlas.Core`.

## What is defined

* `Distinction α` — a non-empty two-block partition of a type into `inside` / `outside`.
* `State`         — a finite assignment of natural values to named variables,
                    modelled as `List (String × Nat)`.  States are compared **up to
                    permutation**: `s₁ ≈ s₂` is Mathlib's setoid on lists, i.e.
                    `List.Perm`.
* `Transition`    — a named partial function `State → Option State`
                    (with `Transition.id` and `Transition.comp`).
* `informationGain` — the size of the *multiset* symmetric difference of the two
                    variable-binding lists.
* `Model`         — a (partial) one-step predictor `State → Option State`.
* `Goal`          — a predicate on states (a desired attractor region).
* `feedbackError` — `informationGain` between the predicted and the observed state.
* `uccStep`       — one turn of the Universal Cognition Cycle:
                    predict → compare → update the model → choose the next state.

## What is proved

* `distinction_nontrivial`     (T1) — `d.inside ≠ d.outside`.
* `informationGain_eq_zero_iff` (T2) — `informationGain s₁ s₂ = 0 ↔ s₁ ≈ s₂`.
* `feedback_zero_of_eq`        (T3) — a correct prediction produces zero error.
* `uccStep_perfect`            (T4) — if the model already predicts `s` from `s`, the
                                observation is `s` and `s` satisfies the goal, then one
                                UCC step changes nothing: the model is unchanged, the
                                next state is `s`, it still satisfies the goal and the
                                error stays `0`.
* `ucc_eventually_cycles`      (T5) — on a finite, environment-closed state space a
                                perfect model yields a trajectory that revisits a
                                state within `|S|` steps (an explicit bound), i.e. the
                                system reaches a fixed point or a cycle.

Auxiliary results: `informationGain` is a pseudo-metric-like symmetric measure,
model update is *effective* (`uccStep_learns`), goal states are absorbing,
and a general pigeonhole lemma `exists_iterate_eq_of_finite`.

## Intentional weakenings / design choices

1. **Equality of states.**  `≈` is `List.Perm`, exactly as requested ("equality up to
   permutation").  Consequently `informationGain` is measured on *multisets* of
   bindings, not on sets of variable names: with plain sets of names T2 would be
   false (`[("x",0)]` and `[("x",1)]` have equal name sets but are not permutations),
   and with sets of bindings it would also be false (`[a,a]` vs `[a]`).  The multiset
   symmetric difference is computable and makes T2 an exact `iff`.
2. **Decidable goals.**  `uccStep` branches on the goal, so it takes an instance
   argument `[DecidablePred g]`.  This is the only addition to the signature
   requested in the task.
3. **T5** is stated for a model that is already perfect with respect to the
   environment (otherwise the model component of the system state ranges over an
   infinite space and no cycle bound exists).  The pigeonhole core
   (`exists_iterate_eq_of_finite`) is proved in full generality.
-/

namespace PolymathAtlas.Core

/-! ## 1. Distinction -/

/-- A distinction cuts a type into a non-empty `inside` and a non-empty `outside`. -/
structure Distinction (α : Type*) where
  inside : Set α
  outside : Set α
  partition : inside ∪ outside = Set.univ
  disjoint : inside ∩ outside = ∅
  nonempty_inside : inside.Nonempty
  nonempty_outside : outside.Nonempty

/-- **T1.**  A distinction is non-trivial: the two sides really differ. -/
theorem distinction_nontrivial {α : Type*} (d : Distinction α) : d.inside ≠ d.outside := by
  intro h
  obtain ⟨x, hx⟩ := d.nonempty_inside
  have : x ∈ d.inside ∩ d.outside := ⟨hx, h ▸ hx⟩
  rw [d.disjoint] at this
  exact this

/-- The outside is exactly the complement of the inside. -/
theorem Distinction.outside_eq_compl {α : Type*} (d : Distinction α) : d.outside = d.insideᶜ := by
  ext x
  constructor
  · intro hx hx'
    have : x ∈ d.inside ∩ d.outside := ⟨hx', hx⟩
    rw [d.disjoint] at this
    exact this
  · intro hx
    have : x ∈ d.inside ∪ d.outside := by rw [d.partition]; trivial
    exact this.resolve_left hx

/-! ## 2. State

A state is a finite list of named natural-number values.  Two states are equal when
one is a permutation of the other; this is Mathlib's `Setoid` structure on lists, so
`s₁ ≈ s₂` means `s₁.Perm s₂`. -/

/-- A state: a finite assignment of values to named variables. -/
abbrev State : Type := List (String × Nat)

/-- Unfolding lemma: `≈` on states is permutation of the underlying lists. -/
theorem state_equiv_iff (s₁ s₂ : State) : s₁ ≈ s₂ ↔ s₁.Perm s₂ := Iff.rfl

/-- The multiset of bindings of a state; permutation-equal states have equal multisets. -/
def bindings (s : State) : Multiset (String × Nat) := (s : Multiset (String × Nat))

theorem bindings_eq_iff (s₁ s₂ : State) : bindings s₁ = bindings s₂ ↔ s₁ ≈ s₂ :=
  Multiset.coe_eq_coe

/-! ## 3. Transition -/

/-- A named partial state transformation. -/
structure Transition where
  name : String
  apply : State → Option State

/-- The identity transition. -/
def Transition.idT : Transition where
  name := "id"
  apply := some

/-- Sequential composition of transitions (`t₂` after `t₁`). -/
def Transition.comp (t₁ t₂ : Transition) : Transition where
  name := t₁.name ++ ";" ++ t₂.name
  apply := fun s => (t₁.apply s).bind t₂.apply

@[simp] theorem Transition.idT_apply (s : State) : Transition.idT.apply s = some s := rfl

@[simp] theorem Transition.comp_apply (t₁ t₂ : Transition) (s : State) :
    (t₁.comp t₂).apply s = (t₁.apply s).bind t₂.apply := rfl

theorem Transition.comp_assoc (t₁ t₂ t₃ : Transition) (s : State) :
    ((t₁.comp t₂).comp t₃).apply s = (t₁.comp (t₂.comp t₃)).apply s := by
  simp [Transition.comp, Option.bind_assoc]

/-! ## 4. Information -/

/-- Information gain: the number of bindings by which the two states differ,
i.e. the cardinality of the symmetric difference of their multisets of bindings. -/
def informationGain (s₁ s₂ : State) : Nat :=
  Multiset.card ((bindings s₁ - bindings s₂) + (bindings s₂ - bindings s₁))

theorem informationGain_comm (s₁ s₂ : State) : informationGain s₁ s₂ = informationGain s₂ s₁ := by
  simp [informationGain, Nat.add_comm]

/-- **T2.**  Information gain vanishes exactly on equal (permutation-equal) states. -/
theorem informationGain_eq_zero_iff (s₁ s₂ : State) :
    informationGain s₁ s₂ = 0 ↔ s₁ ≈ s₂ := by
  rw [informationGain, Multiset.card_add, Nat.add_eq_zero_iff]
  simp only [Multiset.card_eq_zero, tsub_eq_zero_iff_le]
  rw [← bindings_eq_iff]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨le_of_eq h, le_of_eq h.symm⟩⟩

@[simp] theorem informationGain_self (s : State) : informationGain s s = 0 :=
  (informationGain_eq_zero_iff s s).2 (Setoid.refl s)

/-! ## 5. Model, Goal, Feedback -/

/-- A model predicts the next state (possibly failing to predict). -/
structure Model where
  predict : State → Option State

/-- A goal is a predicate on states: the desired attractor region. -/
abbrev Goal : Type := State → Prop

/-- Feedback error between a predicted and an observed state. -/
def feedbackError (predicted observed : State) : Nat := informationGain predicted observed

/-- **T3.**  No error when the prediction matches the observation. -/
theorem feedback_zero_of_eq (p o : State) (h : p ≈ o) : feedbackError p o = 0 :=
  (informationGain_eq_zero_iff p o).2 h

theorem feedback_eq_zero_iff (p o : State) : feedbackError p o = 0 ↔ p ≈ o :=
  informationGain_eq_zero_iff p o

/-- The error the model actually commits at `s` given the observation `obs`.
A missing prediction counts as a strictly positive error. -/
def predictionError (m : Model) (s obs : State) : Nat :=
  match m.predict s with
  | none => obs.length + 1
  | some p => feedbackError p obs

/-- The explicit learning rule: remember the observation as the prediction at `s`. -/
def updateModel (m : Model) (s obs : State) : Model where
  predict := fun t => if t = s then some obs else m.predict t

@[simp] theorem updateModel_predict_self (m : Model) (s obs : State) :
    (updateModel m s obs).predict s = some obs := by simp [updateModel]

/-! ## 6. The Universal Cognition Cycle -/

/-- One turn of the Universal Cognition Cycle.

1. *predict*: `m.predict s`;
2. *compare*: `predictionError m s obs`;
3. *update*: if the error is non-zero, learn `s ↦ obs`;
4. *act*: if the goal is already met at `obs`, stay there (goal states are attractors);
   otherwise move to the state the (updated) model predicts from `obs`, defaulting to
   `obs` when the model has no prediction. -/
def uccStep (m : Model) (g : Goal) [DecidablePred g] (s obs : State) : Model × State :=
  let m' := if predictionError m s obs = 0 then m else updateModel m s obs
  let next := if g obs then obs else (m'.predict obs).getD obs
  (m', next)

/-- The model component is unchanged exactly when the current prediction is already
correct. -/
theorem uccStep_model_of_error_zero (m : Model) (g : Goal) [DecidablePred g] (s obs : State)
    (h : predictionError m s obs = 0) : (uccStep m g s obs).1 = m := by
  simp [uccStep, h]

/-- Learning is effective: after a step with non-zero error the new model predicts the
observation at `s`, i.e. the error at `s` has dropped to `0`. -/
theorem uccStep_learns (m : Model) (g : Goal) [DecidablePred g] (s obs : State)
    (h : predictionError m s obs ≠ 0) :
    predictionError (uccStep m g s obs).1 s obs = 0 := by
  have : (uccStep m g s obs).1 = updateModel m s obs := by simp [uccStep, h]
  rw [predictionError, this, updateModel_predict_self]
  exact feedback_zero_of_eq _ _ (Setoid.refl obs)

/-- In every case the error at `s` after one step is zero: the cycle is a genuine
error-minimising loop. -/
theorem uccStep_error_zero (m : Model) (g : Goal) [DecidablePred g] (s obs : State) :
    predictionError (uccStep m g s obs).1 s obs = 0 := by
  by_cases h : predictionError m s obs = 0
  · rw [uccStep_model_of_error_zero m g s obs h]; exact h
  · exact uccStep_learns m g s obs h

/-- Goal states are absorbing for the state component. -/
theorem uccStep_goal_absorbing (m : Model) (g : Goal) [DecidablePred g] (s obs : State)
    (hg : g obs) : (uccStep m g s obs).2 = obs := by
  simp [uccStep, hg]

/-- **T4.**  If the model is already perfect at `s` (it predicts `s` from `s`), the
observation confirms it (`obs = s`) and `s` satisfies the goal, then one UCC step is
inert: the model is unchanged, the next state is again `s`, the goal still holds and
the error stays `0`. -/
theorem uccStep_perfect (m : Model) (g : Goal) [DecidablePred g] (s : State)
    (hpred : m.predict s = some s) (hg : g s) :
    uccStep m g s s = (m, s) ∧ g (uccStep m g s s).2 ∧
      feedbackError s (uccStep m g s s).2 = 0 := by
  have herr : predictionError m s s = 0 := by
    rw [predictionError, hpred]
    exact feedback_zero_of_eq _ _ (Setoid.refl s)
  have hstep : uccStep m g s s = (m, s) := by simp [uccStep, herr, hg]
  refine ⟨hstep, ?_, ?_⟩ <;> rw [hstep]
  · exact hg
  · exact feedback_zero_of_eq _ _ (Setoid.refl s)

/-! ## 7. T5 — finite state spaces: fixed point or cycle

The system as a whole evolves on pairs `Model × State`; the environment supplies the
observation `env s` in the state `s`. -/

/-- The closed-loop system step with environment `env`. -/
def sysStep (g : Goal) [DecidablePred g] (env : State → State) (p : Model × State) :
    Model × State :=
  uccStep p.1 g p.2 (env p.2)

/-- The state dynamics induced by a perfect model. -/
def envStep (g : Goal) [DecidablePred g] (env : State → State) (s : State) : State :=
  if g (env s) then env s else env (env s)

/-- A model is *perfect* for `env` when it predicts the environment exactly. -/
def Perfect (m : Model) (env : State → State) : Prop := ∀ t, m.predict t = some (env t)

theorem sysStep_of_perfect {m : Model} {env : State → State} (g : Goal) [DecidablePred g]
    (hp : Perfect m env) (s : State) :
    sysStep g env (m, s) = (m, envStep g env s) := by
  have herr : predictionError m s (env s) = 0 := by
    rw [predictionError, hp s]
    exact feedback_zero_of_eq _ _ (Setoid.refl (env s))
  simp only [sysStep, uccStep, envStep, herr]
  by_cases hg : g (env s) <;> simp [hg, hp (env s)]

theorem sysStep_iterate_of_perfect {m : Model} {env : State → State} (g : Goal)
    [DecidablePred g] (hp : Perfect m env) (s : State) (k : Nat) :
    (sysStep g env)^[k] (m, s) = (m, (envStep g env)^[k] s) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        sysStep_of_perfect g hp s, ih]

/-- **Pigeonhole core.**  A self-map of a finite invariant set repeats a value within
`S.card` steps. -/
theorem exists_iterate_eq_of_finite {α : Type*} [DecidableEq α] (S : Finset α) (f : α → α)
    (hclosed : ∀ x ∈ S, f x ∈ S) (s₀ : α) (h₀ : s₀ ∈ S) :
    ∃ i j, i < j ∧ j ≤ S.card ∧ f^[i] s₀ = f^[j] s₀ := by
  have hmem : ∀ k, f^[k] s₀ ∈ S := by
    intro k
    induction k with
    | zero => simpa using h₀
    | succ k ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
  have hcard : S.card < (Finset.range (S.card + 1)).card := by
    simp
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun k _ => hmem k)
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hj), heq⟩
  · exact ⟨j, i, h, by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hi), heq.symm⟩

/-- **T5.**  On a finite state space `S` that the environment cannot leave, a system
driven by a perfect model revisits a configuration after at most `S.card` steps:
the trajectory reaches a fixed point or enters a cycle, with an explicit bound in
terms of the size of the state space. -/
theorem ucc_eventually_cycles (m : Model) (g : Goal) [DecidablePred g]
    (env : State → State) (hp : Perfect m env) (S : Finset State)
    (hclosed : ∀ x ∈ S, env x ∈ S) (s₀ : State) (h₀ : s₀ ∈ S) :
    ∃ i j, i < j ∧ j ≤ S.card ∧
      (sysStep g env)^[i] (m, s₀) = (sysStep g env)^[j] (m, s₀) := by
  have hclosed' : ∀ x ∈ S, envStep g env x ∈ S := by
    intro x hx
    by_cases hg : g (env x) <;> simp only [envStep, hg, if_true, if_false]
    · exact hclosed x hx
    · exact hclosed _ (hclosed x hx)
  obtain ⟨i, j, hij, hjc, heq⟩ := exists_iterate_eq_of_finite S (envStep g env) hclosed' s₀ h₀
  refine ⟨i, j, hij, hjc, ?_⟩
  rw [sysStep_iterate_of_perfect g hp, sysStep_iterate_of_perfect g hp, heq]

/-! ## 8. Sanity checks: the theory is non-vacuous -/

section Examples

/-- A concrete distinction on `Nat`: even numbers inside, odd numbers outside. -/
def evenDistinction : Distinction Nat where
  inside := {n | Even n}
  outside := {n | ¬ Even n}
  partition := by
    ext n
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact em _
  disjoint := by ext n; simp
  nonempty_inside := ⟨0, by simp⟩
  nonempty_outside := ⟨1, by simp⟩

example : evenDistinction.inside ≠ evenDistinction.outside := distinction_nontrivial _

/-- Permutation-equal states carry the same information. -/
example : informationGain [("x", 1), ("y", 2)] [("y", 2), ("x", 1)] = 0 := by decide

/-- Two differing bindings give information gain `2`. -/
example : informationGain [("x", 1)] [("x", 2)] = 2 := by decide

/-- A model that predicts nothing learns from one observation. -/
example :
    ((uccStep ⟨fun _ => none⟩ (fun _ => False) [("x", 0)] [("x", 1)]).1).predict [("x", 0)]
      = some [("x", 1)] := by
  simp [uccStep, predictionError, updateModel]

end Examples

#print axioms distinction_nontrivial
#print axioms informationGain_eq_zero_iff
#print axioms feedback_zero_of_eq
#print axioms uccStep_perfect
#print axioms ucc_eventually_cycles

end PolymathAtlas.Core
