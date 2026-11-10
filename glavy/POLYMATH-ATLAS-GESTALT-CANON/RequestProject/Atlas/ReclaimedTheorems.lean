import Mathlib
import RequestProject.Atlas.IdealAI_Countermodels

/-!
# Reclaimed metamathematical theorems

This module replaces the four finite countermodels with corrected theorems whose
missing hypotheses are explicit.  The interfaces isolate the standard ingredients:
Gödel coding and diagonalization, Hilbert--Bernays derivability conditions, an
acceptable enumeration of partial computations, and observational fidelity.
-/

namespace IdealAI.Reclaimed

/-! ## Arithmetized syntax and the diagonal lemma -/

/-- Arithmetized syntax: sentences have numerical codes, substitution by a numeral,
and a diagonalization operation satisfying the usual substitution equation. -/
structure ArithmetizedSyntax where
  Sentence : Type
  code : Sentence → ℕ
  substituteNumeral : Sentence → ℕ → Sentence
  diagonal : Sentence → Sentence
  diagonal_eq : ∀ template,
    diagonal template = substituteNumeral template (code template)

namespace ArithmetizedSyntax

/-
The syntactic diagonal lemma, exposed as the defining coding equation.
-/
theorem diagonal_lemma (A : ArithmetizedSyntax) (template : A.Sentence) :
    A.diagonal template = A.substituteNumeral template (A.code template) := by
  exact A.diagonal_eq template

end ArithmetizedSyntax

/-- Semantic fixed points supplied by representability plus syntactic diagonalization.
Only representable predicates receive fixed points, and representability is closed
under negation.  Unlike an unrestricted semantic fixed-point field, this interface
is consistent with the undefinability conclusion. -/
structure DiagonalTheory extends ArithmetizedSyntax where
  Satisfied : Sentence → Prop
  Representable : (Sentence → Prop) → Prop
  representable_not : ∀ {predicate}, Representable predicate →
    Representable (fun sentence => ¬ predicate sentence)
  fixedPoint : ∀ predicate : Sentence → Prop, Representable predicate →
    ∃ sentence, Satisfied sentence ↔ predicate sentence

/-- A predicate defines semantic truth exactly when it agrees with satisfaction. -/
def DefinesTruth (D : DiagonalTheory) (truth : D.Sentence → Prop) : Prop :=
  ∀ sentence, truth sentence ↔ D.Satisfied sentence

/-
Tarski undefinability: no representable predicate defines semantic truth.
-/
theorem truth_undefinability (D : DiagonalTheory) :
    ¬ ∃ truth : D.Sentence → Prop, D.Representable truth ∧ DefinesTruth D truth := by
  intro h
  obtain ⟨truth, representable, htruth⟩ := h
  obtain ⟨sentence, fixed⟩ :=
    D.fixedPoint (fun sentence => ¬ truth sentence) (D.representable_not representable)
  have agrees := htruth sentence
  by_cases ht : truth sentence
  · exact (fixed.mp (agrees.mp ht)) ht
  · exact ht (agrees.mpr (fixed.mpr ht))

/-! ## Hilbert--Bernays derivability and Gödel's second theorem -/

/-- An abstract effective provability predicate satisfying the three standard
Hilbert--Bernays conditions.  `necessitate` is derivability condition 1,
`distribute` condition 2, and `positive` condition 3. -/
structure DerivabilityConditions where
  Provable : Prop → Prop
  necessitate : ∀ {p : Prop}, p → Provable p
  distribute : ∀ {p q : Prop}, Provable (p → q) → Provable p → Provable q
  positive : ∀ {p : Prop}, Provable p → Provable (Provable p)

namespace DerivabilityConditions

/-- Formal consistency is the non-provability of contradiction. -/
def Consistent (D : DerivabilityConditions) : Prop := ¬ D.Provable False

/-- The internal consistency sentence says that contradiction is not provable. -/
def ConsistencyStatement (D : DerivabilityConditions) : Prop := ¬ D.Provable False

/-- A Gödel sentence is a fixed point for its own unprovability. -/
def IsGodelSentence (D : DerivabilityConditions) (G : Prop) : Prop :=
  G ↔ ¬ D.Provable G

/-
Gödel's second incompleteness theorem in an abstract derivability framework.
-/
theorem second_incompleteness (D : DerivabilityConditions) (G : Prop)
    (diagonal : D.IsGodelSentence G) (consistent : D.Consistent) :
    ¬ D.Provable D.ConsistencyStatement := by
  intro provesConsistency
  have consistency_implies_G : D.ConsistencyStatement → G := by
    intro hConsistency
    by_contra notG
    have provesG : D.Provable G := by
      by_contra notProvesG
      exact notG (diagonal.mpr notProvesG)
    have provesProvesG : D.Provable (D.Provable G) := D.positive provesG
    have proves_notG : D.Provable (¬ G) := by
      apply D.distribute (D.necessitate (p := D.Provable G → ¬ G) (fun hPG hG => (diagonal.mp hG) hPG))
      exact provesProvesG
    have provesFalse : D.Provable False := by
      have implication : D.Provable (G → (¬ G → False)) :=
        D.necessitate (p := G → (¬ G → False)) (fun hG hnG => hnG hG)
      exact D.distribute (D.distribute implication provesG) proves_notG
    exact hConsistency provesFalse
  have provesG : D.Provable G :=
    D.distribute (D.necessitate (p := D.ConsistencyStatement → G) consistency_implies_G)
      provesConsistency
  have provesProvesG : D.Provable (D.Provable G) := D.positive provesG
  have provesNotProvesG : D.Provable (¬ D.Provable G) :=
    D.distribute (D.necessitate (p := G → ¬ D.Provable G) diagonal.mp) provesG
  have implication : D.Provable (D.Provable G → (¬ D.Provable G → False)) :=
    D.necessitate (p := D.Provable G → (¬ D.Provable G → False))
      (fun hPG hnPG => hnPG hPG)
  exact consistent (D.distribute (D.distribute implication provesProvesG) provesNotProvesG)

end DerivabilityConditions

/-! ## Partial computable functions and Rice's theorem -/

/-- Extensional equality of programs in a numbering of partial functions. -/
def ProgramExtEq (Eval : ℕ → ℕ → ℕ → Prop) (a b : ℕ) : Prop :=
  ∀ input output, Eval a input output ↔ Eval b input output

/-- An acceptable numbering with the uniform switching construction used in
Rice's theorem.  Evaluation is a deterministic graph rather than a total Lean
function, so divergence is represented by absence of an output.  The switch
construction is the standard partial-computable reduction obtained from
universality and the s-m-n theorem. -/
structure PartialComputableEnumeration where
  Eval : ℕ → ℕ → ℕ → Prop
  deterministic : ∀ {program input left right},
    Eval program input left → Eval program input right → left = right
  switch : ℕ → ℕ → ℕ → ℕ → ℕ
  switch_of_halts : ∀ {program input yes no},
    (∃ output, Eval program input output) →
      ∀ argument output, Eval (switch program input yes no) argument output ↔
        Eval yes argument output
  switch_of_diverges : ∀ {program input yes no},
    (¬ ∃ output, Eval program input output) →
      ∀ argument output, Eval (switch program input yes no) argument output ↔
        Eval no argument output
  halting_undecidable : ¬ ∃ decider : ℕ → ℕ → Bool,
    ∀ program input, decider program input = true ↔
      ∃ output, Eval program input output

/-- A semantic program property depends only on the partial function computed. -/
def ExtensionalProperty (E : PartialComputableEnumeration) (property : ℕ → Prop) : Prop :=
  ∀ {a b}, ProgramExtEq E.Eval a b → (property a ↔ property b)

/-- Nontriviality with witnesses from both semantic classes. -/
def SemanticallyNontrivial (property : ℕ → Prop) : Prop :=
  ∃ yes no, property yes ∧ ¬ property no

/-
Rice's theorem for an acceptable numbering of partial computable functions.
-/
theorem rice_theorem (E : PartialComputableEnumeration) (property : ℕ → Prop)
    (extensional : ExtensionalProperty E property)
    (nontrivial : SemanticallyNontrivial property) :
    ¬ ∃ decider : ℕ → Bool, ∀ program, decider program = true ↔ property program := by
  intro h
  obtain ⟨decider, hdec⟩ := h
  have h_halting : ¬ ∃ decider : ℕ → ℕ → Bool, ∀ program input, decider program input = true ↔ ∃ output, E.Eval program input output := by
    exact E.halting_undecidable;
  obtain ⟨yes, no, hyes, hno⟩ := nontrivial;
  apply h_halting;
  use fun program input => decider (E.switch program input yes no) = true;
  intro program input; by_cases h : ∃ output, E.Eval program input output <;> simp_all +decide ;
  · have h_ext : ProgramExtEq E.Eval (E.switch program input yes no) yes := by
      exact fun input' output' => by rw [ E.switch_of_halts h ] ;
    exact extensional h_ext |>.2 hyes;
  · convert hno using 1;
    apply extensional;
    exact fun x y => by rw [ E.switch_of_diverges ( by tauto ) ] ;

/-! ## Simulation indistinguishability -/

/-
The reclaimed simulation theorem uses the already identified observational
fidelity condition rather than detail and location alone.
-/
theorem simulation_indistinguishability
    (scenario : IdealAI.SimulationScenario)
    (fidelity : IdealAI.ObservationallyIndistinguishable scenario)
    (detailed : scenario.sufficientlyDetailed) (inside : scenario.observerInside) :
    ¬ scenario.canDistinguishSimulation := by
  exact IdealAI.indistinguishable_for_observer scenario fidelity detailed inside

end IdealAI.Reclaimed