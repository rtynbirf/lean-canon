import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RSIA_FormalMindTheorem
import RequestProject.Atlas.UAM_RSIA_Undecidability
import RequestProject.Atlas.UAM_RSIA_SelfReference
import RequestProject.Atlas.UAM_RSIA_HaltingBarrier
import RequestProject.Atlas.Arithmetic_Rice
import RequestProject.Atlas.Arithmetic_Truth

set_option autoImplicit false

/-!
# RSIA epistemic closure: phenomenal predicates

Observational extensionality and nontriviality alone do *not* imply
undecidability (for example, “the boundary is empty” is extensional,
nontrivial, and decidable).  The valid Rice conclusion additionally needs an
acceptable program numbering and semantic adequacy.  These hypotheses are
made explicit below.
-/

namespace UAM_RSIA

open Arithmetic_Rice
open Arithmetic_Truth

universe u

variable {α : Type u}

/-- A candidate phenomenal predicate on systems and finite observations. -/
def PhenomenalConsciousnessPredicate (α : Type u) :=
  HierarchicalParallelSystem α → List (UAM_Free.FreeMonoid α) → Prop

/-- Equality of the observable session boundaries. -/
def ObservationallyIndistinguishable
    (hps₁ hps₂ : HierarchicalParallelSystem α) : Prop :=
  hps₁.system.sessions.map (·.session.environment.current) =
    hps₂.system.sessions.map (·.session.environment.current)

/-- A predicate is observationally extensional when equal boundaries yield the
same answer for every supplied observation. -/
def PhenomenalConsciousnessPredicate.extensional
    (P : PhenomenalConsciousnessPredicate α) : Prop :=
  ∀ hps₁ hps₂ obs, ObservationallyIndistinguishable hps₁ hps₂ →
    (P hps₁ obs ↔ P hps₂ obs)

/-- Semantic nontriviality on actual systems. -/
def PhenomenalConsciousnessPredicate.nontrivial
    (P : PhenomenalConsciousnessPredicate α) : Prop :=
  (∃ hps obs, P hps obs) ∧ ∃ hps obs, ¬ P hps obs

/-- A computability interpretation of phenomenal test instances. -/
structure PhenomenalProgramModel (α : Type u) where
  enumeration : PartialComputableEnumeration
  decode : Nat → HierarchicalParallelSystem α × List (UAM_Free.FreeMonoid α)

/-- The semantic property of a decoded program. -/
def PhenomenalProgramModel.property (M : PhenomenalProgramModel α)
    (P : PhenomenalConsciousnessPredicate α) (code : Nat) : Prop :=
  P (M.decode code).1 (M.decode code).2

/-- Adequacy packages precisely the extensionality and nontriviality required
by Rice's theorem for the chosen effective interpretation. -/
def PhenomenalProgramModel.Adequate (M : PhenomenalProgramModel α)
    (P : PhenomenalConsciousnessPredicate α) : Prop :=
  ExtensionalProperty M.enumeration (M.property P) ∧
  SemanticallyNontrivial (M.property P)

/-- **Phenomenal undecidability barrier.**  No system-level Boolean decider can
exist for a phenomenal predicate whose program interpretation is an adequate,
nontrivial semantic property. -/
theorem phenomenal_consciousness_undecidable
    (P : PhenomenalConsciousnessPredicate α) (M : PhenomenalProgramModel α)
    (hAdequate : M.Adequate P) :
    ¬ ∃ decider : HierarchicalParallelSystem α →
        List (UAM_Free.FreeMonoid α) → Bool,
      ∀ hps obs, decider hps obs = true ↔ P hps obs := by
  intro ⟨decider, hdecider⟩
  -- Convert to a program decider
  let programDecider : Nat → Bool := fun code => decider (M.decode code).1 (M.decode code).2
  have hprogramDecider : ∀ code, programDecider code = true ↔ M.property P code := by
    intro code
    simp only [programDecider, PhenomenalProgramModel.property]
    exact hdecider _ _
  -- Apply Rice's theorem
  exact rice_theorem M.enumeration (M.property P) hAdequate.1 hAdequate.2 ⟨programDecider, hprogramDecider⟩

/-- Tarski's theorem supplies a separate undefinability boundary whenever a
candidate predicate is claimed to be a representable truth predicate for a
diagonal theory. -/
theorem phenomenal_truth_undefinable
    (theory : Arithmetic_Foundations.DiagonalTheory) :
    ¬ ∃ truth : theory.Sentence → Prop,
      theory.Representable truth ∧ DefinesTruth theory truth := by
  exact tarski_undefinability theory

/-- Run 20's operational disclaimer together with the conditional, correctly
scoped Rice barrier. -/
theorem rsia_not_phenomenally_conscious_strengthened :
    (∃ (C : FormalMind.Consciousness (HierarchicalParallelSystem α) Unit),
      ∀ hps, C.conscious hps ↔ CollectiveShouldStop hps) ∧
    ∀ (P : PhenomenalConsciousnessPredicate α)
      (M : PhenomenalProgramModel α), M.Adequate P →
      ¬ ∃ decider : HierarchicalParallelSystem α →
          List (UAM_Free.FreeMonoid α) → Bool,
        ∀ hps obs, decider hps obs = true ↔ P hps obs := by
  refine ⟨?_, fun P M hAdequate => phenomenal_consciousness_undecidable P M hAdequate⟩
  exact rsia_not_phenomenally_conscious

end UAM_RSIA
