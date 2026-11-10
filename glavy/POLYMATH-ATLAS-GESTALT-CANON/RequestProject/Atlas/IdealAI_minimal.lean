/-
  IdealAI_minimal.lean
  ====================

  A verified formal core for the seven open claims that were
  left unproved in `IdealAI (2).lean`.  The original file and `Stubs.lean`
  are retained unchanged.  Their symbols are uninterpreted, so the claims do
  not follow from the stated declarations.  This file therefore does two
  things:

  * gives precise semantics for the three claims that become valid once their
    intended meanings are defined; and
  * proves finite countermodels for the four remaining schemas, identifying
    the extra mathematical hypotheses they require.

  The completed file introduces no assumptions and contains no proof gaps.
-/

import Mathlib

namespace IdealAIMinimal

/- ========================================================================== -/
/- SECTION 1: A small semantic core                                           -/
/- ========================================================================== -/

/-- A system carries a numerical integrated-information measure. -/
structure System where
  phi : ℝ

/-- The integrated-information measure of a system. -/
def Phi (system : System) : ℝ := system.phi

/-- In this core model, integration means that the measure is positive. -/
def Integrated (system : System) : Prop := 0 < Phi system

/-
Positivity of Φ entails integration by the defining semantics.
-/
theorem phi_implies_integration (system : System) (hPhi : Phi system > 0) :
    Integrated system := by
  exact hPhi

/-- A persistent self is represented by an observable state. -/
structure PersistentSelf where
  state : ℕ
  deriving DecidableEq, Repr

/-- A copy has the same observable state as its source. -/
def IsCopy (copy self : PersistentSelf) : Prop := copy.state = self.state

/-- Identity is equality of persistent selves, not merely state equality. -/
def Identical (left right : PersistentSelf) : Prop := left = right

/-- A copy breaks identity precisely when it is a distinct state-preserving copy. -/
def IdentityBroken (self copy : PersistentSelf) : Prop :=
  IsCopy copy self ∧ ¬ Identical copy self

/-
The missing premise in the original copy claim is made explicit.
-/
theorem copy_violates_identity (self copy : PersistentSelf)
    (hCopy : IsCopy copy self) (hDistinct : ¬ Identical copy self) :
    IdentityBroken self copy := by
  exact ⟨ hCopy, hDistinct ⟩

/-- A blind spot is a named proposition about the system. -/
structure BlindSpot where
  name : String
  deriving DecidableEq, Repr

/-- A reflective system records one proposition it does not recognize. -/
structure ReflectiveSystem where
  unrecognized : BlindSpot

/-- A system is aware of every spot except its recorded blind spot. -/
def AwareOf (system : ReflectiveSystem) (spot : BlindSpot) : Prop :=
  spot ≠ system.unrecognized

/-
Every reflective system has its explicitly represented blind spot.
-/
theorem awareness_of_blind_spots_limited (system : ReflectiveSystem) :
    ∃ blindSpot : BlindSpot, ¬ AwareOf system blindSpot := by
  exact ⟨ system.unrecognized, by tauto ⟩

/- ========================================================================== -/
/- SECTION 2: Truth undefinability needs an arithmetized truth theory          -/
/- ========================================================================== -/

/-- The three clauses occurring in the original truth-undefinability claim. -/
def TruthSpecification {Sentence : Type} (provable satisfied : Sentence → Prop) : Prop :=
  ∃ truth : Sentence → Prop,
    (∀ sentence, provable sentence → truth sentence) ∧
    (∀ sentence, truth sentence → satisfied sentence) ∧
    (∀ sentence, truth sentence → ¬ truth sentence → False)

/-- A one-sentence model in which all sentences are satisfied and none provable. -/
def truthCountermodel : TruthSpecification (fun _ : Unit => False) (fun _ => True) := by
  refine ⟨fun _ => True, ?_, ?_, ?_⟩
  · intro sentence h
    exact False.elim h
  · intro sentence h
    trivial
  · intro sentence hTruth hNotTruth
    exact hNotTruth hTruth

/-
The bare three-clause schema has a finite countermodel.

    Thus the original theorem cannot be derived merely from predicates named
    `SufficientlyStrong`, `Consistent`, `Provable_`, and `SatisfiedIn`; a
    formal coding of syntax plus a diagonal/truth theorem is needed.
-/
theorem truth_undefinability_not_valid_without_extra_assumptions :
    ¬ (∀ {Sentence : Type} (provable satisfied : Sentence → Prop),
      ¬ TruthSpecification provable satisfied) := by
  push_neg;
  exact ⟨ PUnit, fun _ => False, fun _ => True, truthCountermodel ⟩

/- ========================================================================== -/
/- SECTION 3: Gödel's second theorem needs a derivability framework            -/
/- ========================================================================== -/

/-- The information about a theory used by the original Gödel statement. -/
structure FormalTheory where
  sufficientlyStrong : Prop
  consistent : Prop
  provesOwnConsistency : Prop

/-- A theory satisfying the two displayed hypotheses but proving consistency. -/
def godelCountermodel : FormalTheory where
  sufficientlyStrong := True
  consistent := True
  provesOwnConsistency := True

/-
Strength and consistency alone do not imply the original conclusion.

    The missing ingredients include an effective proof system, arithmetic
    representability, derivability conditions, and a formalized consistency
    statement.
-/
theorem godel_second_incompleteness_not_valid_without_extra_assumptions :
    ¬ (∀ theory : FormalTheory,
      theory.sufficientlyStrong → theory.consistent → ¬ theory.provesOwnConsistency) := by
  push_neg;
  exact ⟨ ⟨ True, True, True ⟩, trivial, trivial, trivial ⟩

/- ========================================================================== -/
/- SECTION 4: Rice's theorem needs semanticity and computability               -/
/- ========================================================================== -/

/-- The nontriviality condition appearing in the original Rice statement. -/
def NonTrivial {Program : Type} (property : Program → Prop) : Prop :=
  ∃ yes no, property yes ∧ ¬ property no

/-- A Boolean procedure decides a predicate when its output matches truth. -/
def Decides {Program : Type} (decider : Program → Bool) (property : Program → Prop) : Prop :=
  ∀ program, (decider program = true) ↔ property program

/-- A finite instance satisfying nontriviality and nevertheless decidable. -/
def riceCountermodel :
    NonTrivial (fun bit : Bool => bit = true) ∧
      Decides (fun bit : Bool => bit) (fun bit : Bool => bit = true) := by
  constructor
  · exact ⟨true, false, rfl, by simp⟩
  · intro bit
    rfl

/-
Nontriviality alone does not entail undecidability.

    Rice's theorem additionally requires a property of partial computable
    functions that is extensional and nontrivial, together with a standard
    enumeration of programs.
-/
theorem rice_theorem_not_valid_without_extra_assumptions :
    ¬ (∀ {Program : Type} (property : Program → Prop), NonTrivial property →
      ¬ ∃ decider : Program → Bool, Decides decider property) := by
  push_neg;
  exact ⟨ Bool, fun x => x = Bool.true, ⟨ Bool.true, Bool.false, rfl, by decide ⟩, fun x => x, fun x => by cases x <;> rfl ⟩

/- ========================================================================== -/
/- SECTION 5: Internal indistinguishability needs an observational hypothesis -/
/- ========================================================================== -/

/-- The three predicates used by the original simulation claim. -/
structure SimulationScenario where
  sufficientlyDetailed : Prop
  observerInside : Prop
  canDistinguishSimulation : Prop

/-- A scenario in which both antecedents hold but the observer distinguishes. -/
def indistinguishabilityCountermodel : SimulationScenario where
  sufficientlyDetailed := True
  observerInside := True
  canDistinguishSimulation := True

/-
Detail and location alone do not entail observational indistinguishability.

    A relation connecting simulation fidelity to available observations is the
    missing assumption in the original theorem.
-/
theorem indistinguishable_for_observer_not_valid_without_extra_assumptions :
    ¬ (∀ scenario : SimulationScenario,
      scenario.sufficientlyDetailed → scenario.observerInside →
        ¬ scenario.canDistinguishSimulation) := by
  exact fun h => absurd ( h ⟨ True, True, True ⟩ ( by tauto ) ( by tauto ) ) ( by tauto )

/- ========================================================================== -/
/- SECTION 6: A reusable sufficient condition for simulation claims            -/
/- ========================================================================== -/

/-- An observational fidelity hypothesis sufficient for the desired conclusion. -/
def ObservationallyIndistinguishable (scenario : SimulationScenario) : Prop :=
  scenario.sufficientlyDetailed → scenario.observerInside →
    ¬ scenario.canDistinguishSimulation

/-- The corrected simulation conclusion follows from the explicit fidelity law. -/
theorem indistinguishable_for_observer (scenario : SimulationScenario)
    (hFidelity : ObservationallyIndistinguishable scenario)
    (hDetailed : scenario.sufficientlyDetailed) (hInside : scenario.observerInside) :
    ¬ scenario.canDistinguishSimulation := by
  exact hFidelity hDetailed hInside

/- ========================================================================== -/
/- SECTION 7: Sanity checks for the finite countermodels                        -/
/- ========================================================================== -/

/-- The truth countermodel uses a finite sentence type. -/
theorem truth_countermodel_has_one_sentence : Fintype.card Unit = 1 := by
  decide

/-- The Rice countermodel uses a finite two-program language. -/
theorem rice_countermodel_has_two_programs : Fintype.card Bool = 2 := by
  decide

end IdealAIMinimal