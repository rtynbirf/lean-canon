import Mathlib.Tactic
import RequestProject.Atlas.UAM_Kleene
import RequestProject.Atlas.UAM_DFAEval

/-!
# The missing alphabet-finiteness hypothesis in the proposed Kleene statement

With regex atoms denoting individual letters, a finite regular expression over
an infinite alphabet can mention only finitely many letters.  A finite DFA can
nevertheless accept every word.  Thus the unrestricted statement requested for
Kleene's theorem is false; this file gives a kernel-checked counterexample.
-/

namespace UAM_KleeneCounterexample

open UAM_RegularExpression UAM_RegularExpression.RegExp UAM_RegularLanguages

/-- The finite set of letters occurring syntactically in a regular expression. -/
def RegExp.support {α : Type} [DecidableEq α] : RegExp α → Finset α
  | .empty_set => ∅
  | .empty_str => ∅
  | .atom a => {a}
  | .alt r s => support r ∪ support s
  | .concat r s => support r ∪ support s
  | .star r => support r

/-- Every letter of every word denoted by a regex occurs in its finite support. -/
theorem mem_support_of_mem_language {α : Type} [DecidableEq α]
    (r : RegExp α) (w : UAM_Free.FreeMonoid α) (hw : w ∈ languageOf r) :
    ∀ a ∈ w, a ∈ RegExp.support r := by
  revert w
  induction r with
  | empty_set =>
      intro w hw
      exact False.elim hw
  | empty_str =>
      intro w hw a ha
      have heq : w = [] := hw
      subst w
      simp at ha
  | atom b =>
      intro w hw a ha
      have heq : w = [b] := hw
      subst w
      change a ∈ [b] at ha
      have hab : a = b := by simpa using ha
      simp [RegExp.support, hab]
  | alt r s ihr ihs =>
      intro w hw a ha
      rcases hw with hr | hs
      · exact Finset.mem_union_left _ (ihr w hr a ha)
      · exact Finset.mem_union_right _ (ihs w hs a ha)
  | concat r s ihr ihs =>
      intro w hw a ha
      rcases hw with ⟨w₁, w₂, rfl, hw₁, hw₂⟩
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · exact Finset.mem_union_left _ (ihr w₁ hw₁ a ha)
      · exact Finset.mem_union_right _ (ihs w₂ hw₂ a ha)
  | star r ihr =>
      intro w hw a ha
      induction hw with
      | empty => simp at ha
      | word v hv => exact ihr v hv a ha
      | concat v₁ v₂ hv₁ hv₂ ih₁ ih₂ =>
          rw [List.mem_append] at ha
          rcases ha with ha | ha
          · exact ih₁ ha
          · exact ih₂ ha

/-- No regular expression over `Nat` denotes the universal language. -/
theorem nat_univ_not_regular :
    ¬ UAM_Kleene.IsRegularLanguage (Set.univ : Set (UAM_Free.FreeMonoid Nat)) := by
  intro h
  rcases h with ⟨r, hr⟩
  let a : Nat := if hne : (RegExp.support r).Nonempty then (RegExp.support r).max' hne + 1 else 0
  have ha_not : a ∉ RegExp.support r := by
    dsimp [a]
    split_ifs with hne
    · intro ha
      have hle := Finset.le_max' (RegExp.support r) _ ha
      exact (Nat.not_succ_le_self _ hle)
    · intro ha
      exact hne ⟨0, ha⟩
  have hword : [a] ∈ languageOf r := by
    rw [hr]
    exact Set.mem_univ [a]
  have ha_mem := mem_support_of_mem_language r [a] hword a (by simp)
  exact ha_not ha_mem

/-- The one-state DFA accepting every word over `Nat`. -/
def universalNatDFA : UAM_DFAEval.DFA Nat Unit where
  δ := fun _ _ => ()
  q₀ := ()
  F := Set.univ

/-- The one-state DFA has universal language. -/
theorem universalNatDFA_language :
    universalNatDFA.language = (Set.univ : Set (UAM_Free.FreeMonoid Nat)) := by
  ext w
  constructor
  · intro _
    exact Set.mem_univ w
  · intro _
    exact Set.mem_univ _

/-- The unrestricted DFA-to-regex implication in the proposed theorem is false. -/
theorem unrestricted_kleene_statement_false :
    ¬ (∀ L : Set (UAM_Free.FreeMonoid Nat),
      UAM_Kleene.IsRegularLanguage L ↔
        ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q)
          (A : UAM_DFAEval.DFA Nat Q), A.language = L) := by
  intro h
  have hdfa : ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q)
      (A : UAM_DFAEval.DFA Nat Q), A.language =
        (Set.univ : Set (UAM_Free.FreeMonoid Nat)) :=
    ⟨Unit, inferInstance, inferInstance, universalNatDFA, universalNatDFA_language⟩
  exact nat_univ_not_regular ((h Set.univ).2 hdfa)

end UAM_KleeneCounterexample