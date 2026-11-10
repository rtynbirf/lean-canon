import Mathlib

set_option autoImplicit false

namespace RSIAReview

abbrev Word := List Bool

/-- The language of binary words whose first symbol is `0` (`false`). -/
def startsWithZero : Set Word := {w | w.head? = some false}

/-- Right Nerode equivalence for a language. -/
def nerodeEq (L : Set Word) (u v : Word) : Prop :=
  ∀ z, u ++ z ∈ L ↔ v ++ z ∈ L

/-- For the language “starts with 0”, the empty word and the word `0`
have different right residuals. -/
theorem eps_not_nerode_zero :
    ¬ nerodeEq startsWithZero [] [false] := by
  intro h
  have hz := h []
  simp [startsWithZero] at hz

/-- The empty word and the word `1` also have different right residuals. -/
theorem eps_not_nerode_one :
    ¬ nerodeEq startsWithZero [] [true] := by
  intro h
  have hz := h [false]
  simp [startsWithZero] at hz

/-- The words `0` and `1` have different right residuals. -/
theorem zero_not_nerode_one :
    ¬ nerodeEq startsWithZero [false] [true] := by
  intro h
  have hz := h []
  simp [startsWithZero] at hz

/-- Consequently the example language has at least three Nerode classes,
not two: the initial residual, the accepting sink, and the rejecting sink. -/
theorem startsWithZero_three_pairwise_distinct_residuals :
    ¬ nerodeEq startsWithZero [] [false] ∧
    ¬ nerodeEq startsWithZero [] [true] ∧
    ¬ nerodeEq startsWithZero [false] [true] := by
  exact ⟨eps_not_nerode_zero, eps_not_nerode_one, zero_not_nerode_one⟩

/-- A tail property cannot see modifications below its cutoff. This is the
structural reason asymptotic rate conditions cannot by themselves imply a
pointwise condition or a global image-counting condition. -/
theorem tail_property_invariant_under_finite_prefix_change
    {α β : Type*} (size : α → Nat) (N : Nat) (f g : α → β) (P : α → β → Prop)
    (hfg : ∀ x, N ≤ size x → f x = g x) :
    (∀ x, N ≤ size x → P x (f x)) ↔
      (∀ x, N ≤ size x → P x (g x)) := by
  constructor
  · intro hf x hx
    rw [← hfg x hx]
    exact hf x hx
  · intro hg x hx
    rw [hfg x hx]
    exact hg x hx

/-- A small integer-valued ultrametric used to show that ultrametricity of a
space alone does not make every self-map non-expansive. -/
def toyDist (x y : Bool × Bool) : Nat :=
  if x = y then 0 else if x.1 = y.1 then 1 else 2

/-- `toyDist` obeys the strong triangle inequality. -/
theorem toyDist_strong_triangle (x y z : Bool × Bool) :
    toyDist x z ≤ max (toyDist x y) (toyDist y z) := by
  decide +revert

/-- This map moves the second coordinate into the first. -/
def toyMap (x : Bool × Bool) : Bool × Bool := (x.2, false)

/-- Despite the strong triangle inequality, `toyMap` expands one distance.
Thus the desired composition theorem needs a property of composition/the
chosen function metric, not merely ultrametricity of the codomain. -/
theorem ultrametric_does_not_force_nonexpansiveness :
    toyDist (false, false) (false, true) <
      toyDist (toyMap (false, false)) (toyMap (false, true)) := by
  decide

end RSIAReview
