import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RSIA_Protocol
import RequestProject.Atlas.UAM_RSIA_ForkTree

set_option autoImplicit false

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- Refinement is reverse inclusion of accepted languages.  It is a preorder
on protocol presentations: distinct rule sets can induce the same language. -/
instance Protocol.refinementPreorder : Preorder (Protocol α) where
  le P Q := Q.language ⊆ P.language
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ hPQ hQR := Set.Subset.trans hQR hPQ

@[simp] theorem Protocol.refinement_le_iff (P Q : Protocol α) :
    P ≤ Q ↔ Q.language ⊆ P.language := Iff.rfl

/-- The refinement preorder is intentionally not claimed antisymmetric on raw
presentations; equality of languages is its induced equivalence. -/
def Protocol.languageEquiv (P Q : Protocol α) : Prop :=
  P.language = Q.language

instance Protocol.languageSetoid : Setoid (Protocol α) where
  r := Protocol.languageEquiv
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Protocol presentations quotiented by observational language equality. -/
abbrev ProtocolQuotient (α : Type u) :=
  Quotient (Protocol.languageSetoid (α := α))

/-- The accepted language of an extensional protocol class. -/
def ProtocolQuotient.language (x : ProtocolQuotient α) :
    Set (UAM_Free.FreeMonoid α) :=
  Quotient.liftOn x Protocol.language (by
    intro P Q h
    exact h)

@[simp] theorem ProtocolQuotient.language_mk (P : Protocol α) :
    ProtocolQuotient.language
      (Quotient.mk (Protocol.languageSetoid (α := α)) P :
        ProtocolQuotient α) = P.language := rfl

/-- On extensional protocol classes, refinement is an honest partial order. -/
instance ProtocolQuotient.partialOrder : PartialOrder (ProtocolQuotient α) where
  le x y := ProtocolQuotient.language y ⊆ ProtocolQuotient.language x
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ hxy hyz := Set.Subset.trans hyz hxy
  le_antisymm := by
    intro x y hxy hyx
    induction x using Quotient.ind with
    | _ P =>
      induction y using Quotient.ind with
      | _ Q =>
        apply Quotient.sound
        exact Set.Subset.antisymm hyx hxy

/-- The protocol allowing every transition. -/
def Protocol.permissive (α : Type u) : Protocol α where
  rules := Set.univ

@[simp] theorem Protocol.permissive_language :
    (Protocol.permissive α).language = Set.univ := by
  ext w
  constructor
  · intro _
    exact Set.mem_univ w
  · intro h
    clear h
    change ProtocolCompliance (Protocol.permissive α) w
    induction w with
    | nil => exact ProtocolCompliance.empty
    | cons a w ih => exact ProtocolCompliance.step ih (Set.mem_univ _)

/-- The permissive class is the least element in refinement order. -/
instance ProtocolQuotient.orderBot : OrderBot (ProtocolQuotient α) where
  bot := Quotient.mk (Protocol.languageSetoid (α := α))
    (Protocol.permissive α)
  bot_le x := by
    induction x using Quotient.ind with
    | _ P =>
      change P.language ⊆ (Protocol.permissive α).language
      rw [Protocol.permissive_language]
      exact Set.subset_univ _

/-- Compose two chains by concatenating their constructors. -/
def EvolutionChain.append
    {L₁ L₂ L₃ : Set (UAM_Free.FreeMonoid α)}
    (c₁ : EvolutionChain α L₁ L₂) (c₂ : EvolutionChain α L₂ L₃) :
    EvolutionChain α L₁ L₃ := by
  induction c₁ with
  | nil => exact c₂
  | preserve h c ih => exact EvolutionChain.preserve h (ih c₂)
  | evolve e c ih => exact EvolutionChain.evolve e (ih c₂)

@[simp] theorem EvolutionChain.append_nil_left
    {L₁ L₂ : Set (UAM_Free.FreeMonoid α)}
    (c : EvolutionChain α L₁ L₂) :
    (EvolutionChain.nil L₁).append c = c := rfl

@[simp] theorem EvolutionChain.append_nil_right
    {L₁ L₂ : Set (UAM_Free.FreeMonoid α)}
    (c : EvolutionChain α L₁ L₂) :
    c.append (EvolutionChain.nil L₂) = c := by
  induction c with
  | nil => rfl
  | preserve h c ih =>
      change EvolutionChain.preserve h (c.append (EvolutionChain.nil _)) = _
      rw [ih]
  | evolve e c ih =>
      change EvolutionChain.evolve e (c.append (EvolutionChain.nil _)) = _
      rw [ih]

@[simp] theorem EvolutionChain.append_assoc
    {L₁ L₂ L₃ L₄ : Set (UAM_Free.FreeMonoid α)}
    (c₁ : EvolutionChain α L₁ L₂) (c₂ : EvolutionChain α L₂ L₃)
    (c₃ : EvolutionChain α L₃ L₄) :
    (c₁.append c₂).append c₃ = c₁.append (c₂.append c₃) := by
  induction c₁ with
  | nil => rfl
  | preserve h c ih =>
      change EvolutionChain.preserve h ((c.append c₂).append c₃) = _
      rw [ih c₂]
  | evolve e c ih =>
      change EvolutionChain.evolve e ((c.append c₂).append c₃) = _
      rw [ih c₂]

/-- Refinements compose transitively. -/
theorem ProtocolEvolution.refinement_monotone
    (P Q R : Protocol α)
    (h₁ : Q.language ⊆ P.language) (h₂ : R.language ⊆ Q.language) :
    R.language ⊆ P.language := Set.Subset.trans h₂ h₁

/-- Extensions compose transitively in the forward inclusion direction. -/
theorem ProtocolEvolution.extension_transitive
    (P Q R : Protocol α)
    (h₁ : P.language ⊆ Q.language) (h₂ : Q.language ⊆ R.language) :
    P.language ⊆ R.language := Set.Subset.trans h₁ h₂

@[simp] theorem ProtocolEvolution.identity_preserves_language (P : Protocol α) :
    (ProtocolEvolution.identity P).parentLanguage =
      (ProtocolEvolution.identity P).childLanguage := rfl

/-- Every protocol supplies an identity path in the hierarchy. -/
def Protocol.identityChain (P : Protocol α) :
    EvolutionChain α P.language P.language := EvolutionChain.nil P.language

/-- A declared evolution supplies a one-edge hierarchy path. -/
def ProtocolEvolution.toChain (e : ProtocolEvolution α) :
    EvolutionChain α e.parentLanguage e.childLanguage :=
  EvolutionChain.evolve e (EvolutionChain.nil e.childLanguage)

end UAM_RSIA
