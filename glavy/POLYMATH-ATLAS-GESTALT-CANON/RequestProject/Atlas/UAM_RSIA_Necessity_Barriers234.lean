import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_HaltingBarrier
import RequestProject.Atlas.UAM_RSIA_SelfReference
import RequestProject.Atlas.UAM_RSIA_PhenomenalUnprovability

set_option autoImplicit false

/-!
# Run 34: necessity for barriers 2, 3, and 4

These theorems give explicit countermodels when a load-bearing hypothesis of
the halting, self-reference, or phenomenal Rice barrier is absent.
-/

namespace UAM_RSIA

open Arithmetic_Rice Arithmetic_Godel2

section HaltingNecessity

/-- If every computation diverges, the constant-false function decides
halting. -/
theorem halting_decider_exists_if_all_diverge
    (E : PartialComputableEnumeration)
    (hAllDiverge : ∀ program input, ¬ ∃ output, E.Eval program input output) :
    ∃ decider : Nat → Nat → Bool,
      ∀ program input, decider program input = true ↔
        ∃ output, E.Eval program input output := by
  refine ⟨fun _ _ => false, ?_⟩
  intro program input
  constructor
  · intro hFalse
    exact (Bool.false_ne_true hFalse).elim
  · intro hHalts
    exact (hAllDiverge program input hHalts).elim

/-- Thus the halting undecidability conclusion is violated in an all-diverging
model. -/
theorem halting_barrier_violated_if_all_diverge
    (E : PartialComputableEnumeration)
    (hAllDiverge : ∀ program input, ¬ ∃ output, E.Eval program input output) :
    ¬ (¬ ∃ decider : Nat → Nat → Bool,
      ∀ program input, decider program input = true ↔
        ∃ output, E.Eval program input output) := by
  intro hBarrier
  exact hBarrier (halting_decider_exists_if_all_diverge E hAllDiverge)

/-- The all-diverging condition simultaneously supplies a decider and records
the missing nontrivial halting behavior. -/
theorem halting_necessity
    (E : PartialComputableEnumeration)
    (hAllDiverge : ∀ program input, ¬ ∃ output, E.Eval program input output) :
    (∃ decider : Nat → Nat → Bool,
      ∀ program input, decider program input = true ↔
        ∃ output, E.Eval program input output) ∧
    (∀ program input, ¬ ∃ output, E.Eval program input output) := by
  exact ⟨halting_decider_exists_if_all_diverge E hAllDiverge, hAllDiverge⟩

end HaltingNecessity

section SelfRefNecessity

/-- An inconsistent derivability predicate proves every proposition. -/
theorem inconsistent_proves_anything
    (D : DerivabilityConditions)
    (hInconsistent : D.Provable False) (p : Prop) :
    D.Provable p := by
  have hImplication : D.Provable (False → p) :=
    D.necessitate (fun hFalse => hFalse.elim)
  exact D.distribute hImplication hInconsistent

/-- In particular, an inconsistent theory proves its internal consistency
statement. -/
theorem inconsistent_proves_consistency
    (D : DerivabilityConditions)
    (hInconsistent : D.Provable False) :
    D.Provable (DerivabilityConditions.ConsistencyStatement D) := by
  exact inconsistent_proves_anything D hInconsistent (DerivabilityConditions.ConsistencyStatement D)

/-- Provability of contradiction directly refutes formal consistency. -/
theorem inconsistent_fails_consistency
    (D : DerivabilityConditions)
    (hInconsistent : D.Provable False) :
    ¬ DerivabilityConditions.Consistent D := by
  exact fun hConsistent => hConsistent hInconsistent

/-- Necessity for the self-reference barrier: if consistency is dropped, the
conclusion of second incompleteness can fail.  The fixed point is retained to
show that inconsistency, rather than diagonalization, is the missing
hypothesis. -/
theorem selfref_necessity
    (D : DerivabilityConditions) (G : Prop)
    (_diagonal : DerivabilityConditions.IsGodelSentence D G)
    (hInconsistent : D.Provable False) :
    D.Provable (DerivabilityConditions.ConsistencyStatement D) ∧ ¬ DerivabilityConditions.Consistent D := by
  exact ⟨inconsistent_proves_consistency D hInconsistent,
    inconsistent_fails_consistency D hInconsistent⟩

end SelfRefNecessity

section PhenomenalNecessity

/-- A universally true property is decided by the constant-true function. -/
theorem decider_exists_if_all_satisfy
    (property : Nat → Prop) (hAllTrue : ∀ code, property code) :
    ∃ decider : Nat → Bool,
      ∀ code, decider code = true ↔ property code := by
  refine ⟨fun _ => true, ?_⟩
  intro code
  constructor
  · intro _
    exact hAllTrue code
  · intro _
    rfl

/-- A universally false property is decided by the constant-false function. -/
theorem decider_exists_if_none_satisfy
    (property : Nat → Prop) (hAllFalse : ∀ code, ¬ property code) :
    ∃ decider : Nat → Bool,
      ∀ code, decider code = true ↔ property code := by
  refine ⟨fun _ => false, ?_⟩
  intro code
  constructor
  · intro hFalse
    exact (Bool.false_ne_true hFalse).elim
  · intro hProperty
    exact (hAllFalse code hProperty).elim

/-- A constant semantic property cannot have both a positive and a negative
witness. -/
theorem trivial_property_fails_nontrivial
    (property : Nat → Prop)
    (hTrivial : (∀ code, property code) ∨ (∀ code, ¬ property code)) :
    ¬ SemanticallyNontrivial property := by
  intro hNontrivial
  obtain ⟨yes, no, hYes, hNo⟩ := hNontrivial
  cases hTrivial with
  | inl hAllTrue => exact hNo (hAllTrue no)
  | inr hAllFalse => exact hAllFalse yes hYes

/-- Necessity for the phenomenal Rice barrier: a semantically constant
property has an explicit decider and fails semantic nontriviality.  The
enumeration is included to make the connection with the corresponding Rice
statement explicit; no extensionality hypothesis is needed for a constant
property. -/
theorem phenomenal_necessity
    (_E : PartialComputableEnumeration) (property : Nat → Prop)
    (hTrivial : (∀ code, property code) ∨ (∀ code, ¬ property code)) :
    (∃ decider : Nat → Bool,
      ∀ code, decider code = true ↔ property code) ∧
    ¬ SemanticallyNontrivial property := by
  constructor
  · cases hTrivial with
    | inl hAllTrue => exact decider_exists_if_all_satisfy property hAllTrue
    | inr hAllFalse => exact decider_exists_if_none_satisfy property hAllFalse
  · exact trivial_property_fails_nontrivial property hTrivial

end PhenomenalNecessity

end UAM_RSIA
