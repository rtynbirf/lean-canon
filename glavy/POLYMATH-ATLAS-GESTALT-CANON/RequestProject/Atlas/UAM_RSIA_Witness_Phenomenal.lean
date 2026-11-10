import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_PhenomenalUnprovability
import RequestProject.Atlas.UAM_RSIA_Witness_Halting

set_option autoImplicit false

/-!
# Run 33 Track C: a conditional phenomenal witness

Adequacy below uses positive and negative decoded codes directly.  This is the
form needed to transfer semantic nontriviality to Rice's theorem; allowing an
unrelated observation witness would not suffice.
-/

namespace UAM_RSIA

open Arithmetic_Rice

universe u
variable {α : Type u}

/-- A toy decoder without an acceptable program enumeration. -/
structure ToyPhenomenalModel (α : Type u) where
  decode : Nat → HierarchicalParallelSystem α ×
    List (UAM_Free.FreeMonoid α)

/-- Explicit decoded witnesses of both truth values. -/
def ToyPhenomenalModel.Adequate
    (toy : ToyPhenomenalModel α)
    (P : PhenomenalConsciousnessPredicate α) : Prop :=
  (∃ yes, P (toy.decode yes).1 (toy.decode yes).2) ∧
  (∃ no, ¬ P (toy.decode no).1 (toy.decode no).2)

/-- A bridge to a standard phenomenal program model.  The reflection field is
exactly what turns extensional equality of programs into equality of decoded
semantic instances. -/
structure ToyPhenomenalEmbedding (α : Type u)
    (toy : ToyPhenomenalModel α) where
  model : PhenomenalProgramModel α
  decode_agrees : ∀ code, model.decode code = toy.decode code
  decode_extensional : ∀ {code₁ code₂},
    ProgramExtEq model.enumeration.Eval code₁ code₂ →
      toy.decode code₁ = toy.decode code₂

/-- An interpretation-preserving toy decoder inherits the Rice barrier. -/
theorem toy_phenomenal_barrier_under_embedding
    (toy : ToyPhenomenalModel α)
    (P : PhenomenalConsciousnessPredicate α)
    (emb : ToyPhenomenalEmbedding α toy)
    (hToyAdequate : toy.Adequate P) :
    ¬ ∃ decider : Nat → Bool,
      ∀ code, decider code = true ↔
        P (toy.decode code).1 (toy.decode code).2 := by
  have hExtensional :
      ExtensionalProperty emb.model.enumeration (emb.model.property P) := by
    intro code₁ code₂ hPrograms
    have hDecode : toy.decode code₁ = toy.decode code₂ :=
      emb.decode_extensional hPrograms
    change P (emb.model.decode code₁).1 (emb.model.decode code₁).2 ↔
      P (emb.model.decode code₂).1 (emb.model.decode code₂).2
    rw [emb.decode_agrees code₁, emb.decode_agrees code₂, hDecode]
  have hNontrivial : SemanticallyNontrivial (emb.model.property P) := by
    obtain ⟨⟨yes, hyes⟩, ⟨no, hno⟩⟩ := hToyAdequate
    refine ⟨yes, no, ?_, ?_⟩
    · change P (emb.model.decode yes).1 (emb.model.decode yes).2
      rw [emb.decode_agrees yes]
      exact hyes
    · change ¬ P (emb.model.decode no).1 (emb.model.decode no).2
      rw [emb.decode_agrees no]
      exact hno
  intro hDec
  obtain ⟨decider, hdecider⟩ := hDec
  apply rice_theorem emb.model.enumeration (emb.model.property P)
    hExtensional hNontrivial
  refine ⟨decider, ?_⟩
  intro code
  change decider code = true ↔
    P (emb.model.decode code).1 (emb.model.decode code).2
  rw [emb.decode_agrees code]
  exact hdecider code

/-- A parity decoder using two supplied operational systems. -/
def toyPhenomenalFin4
    (positive negative : HierarchicalParallelSystem (Fin 4)) :
    ToyPhenomenalModel (Fin 4) where
  decode := fun code =>
    if code % 2 = 0 then (positive, [[0]]) else (negative, [])

/-- A concrete observation predicate: the observation list is nonempty. -/
def Fin4ObservationNonempty : PhenomenalConsciousnessPredicate (Fin 4) :=
  fun _ obs => obs ≠ []

/-- The parity decoder has explicit positive and negative decoded instances. -/
theorem Fin4_toy_phenomenal_adequate
    (positive negative : HierarchicalParallelSystem (Fin 4)) :
    (toyPhenomenalFin4 positive negative).Adequate
      Fin4ObservationNonempty := by
  constructor
  · refine ⟨0, ?_⟩
    intro hEmpty
    cases hEmpty
  · refine ⟨1, ?_⟩
    intro hNonempty
    exact hNonempty rfl


end UAM_RSIA
