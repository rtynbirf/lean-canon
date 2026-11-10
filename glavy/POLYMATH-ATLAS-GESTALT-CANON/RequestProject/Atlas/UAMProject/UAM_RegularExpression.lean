import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Free
import RequestProject.Atlas.UAMProject.UAM_RegularLanguages

namespace UAMP_RegularExpression
universe u

open UAMP_Free hiding FreeMonoid
open UAMP_RegularLanguages

/-- Inductive type of regular expressions -/
inductive RegExp (α : Type u) where
  | empty_set : RegExp α           -- ∅
  | empty_str : RegExp α           -- ε
  | atom : α → RegExp α            -- single symbol
  | alt : RegExp α → RegExp α → RegExp α
  | concat : RegExp α → RegExp α → RegExp α
  | star : RegExp α → RegExp α

/-- Semantics: language of a regular expression -/
def languageOf {α : Type u} : RegExp α → Set (UAMP_Free.FreeMonoid α)
  | RegExp.empty_set => ∅
  | RegExp.empty_str => {[]}
  | RegExp.atom a => {of a}
  | RegExp.alt r s => languageOf r ∪ languageOf s
  | RegExp.concat r s =>
    {w | ∃ u v, u ++ v = w ∧ u ∈ languageOf r ∧ v ∈ languageOf s}
  | RegExp.star r => {w | ∃ S : List (UAMP_Free.FreeMonoid α),
      S.foldr (· ++ ·) [] = w ∧ ∀ s ∈ S, s ∈ languageOf r}

/-- Empty set has empty language -/
theorem languageOf_empty_set {α : Type u} :
    languageOf (RegExp.empty_set : RegExp α) = ∅ := rfl

/-- Empty string language = {[]} -/
theorem languageOf_empty_str {α : Type u} :
    languageOf (RegExp.empty_str : RegExp α) = {[]} := rfl

/-- Atom language = {of a} -/
theorem languageOf_atom {α : Type u} (a : α) :
    languageOf (RegExp.atom a) = {of a} := rfl

/-- Alt language = union -/
theorem languageOf_alt {α : Type u} (r s : RegExp α) :
    languageOf (RegExp.alt r s) = languageOf r ∪ languageOf s := rfl

/-- Concat language = pointwise concatenation -/
theorem languageOf_concat {α : Type u} (r s : RegExp α) :
    languageOf (RegExp.concat r s) =
    {w | ∃ u v, u ++ v = w ∧ u ∈ languageOf r ∧ v ∈ languageOf s} := rfl

/-- Star language = kleeneStar of inner language -/
theorem languageOf_star {α : Type u} (r : RegExp α) :
    languageOf (RegExp.star r) = kleeneStar (languageOf r) := rfl

/-- Star is reflexive transitive closure under concatenation -/
theorem star_contains_empty {α : Type u} (r : RegExp α) :
    [] ∈ languageOf (RegExp.star r) := by
  refine ⟨[], ?_⟩
  simp [List.foldr]

/-- Union of regular expressions contains both operands -/
theorem alt_subset {α : Type u} (r s : RegExp α) :
    languageOf r ⊆ languageOf (RegExp.alt r s) := fun _ h => Or.inl h

theorem alt_subset_right {α : Type u} (r s : RegExp α) :
    languageOf s ⊆ languageOf (RegExp.alt r s) := fun _ h => Or.inr h

end UAMP_RegularExpression
