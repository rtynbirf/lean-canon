import Mathlib.Tactic
import RequestProject.Atlas.UAM_KleeneComplete

/-!
# Regular expressions and finite automata: language equivalence

This module presents the constructions proved in `UAM_Thompson`,
`UAM_EpsilonNFA`, `UAM_NFA`, and `UAM_KleeneComplete` as one uniform API.
For a finite alphabet it proves that the following four descriptions define
exactly the same class of languages:

* regular expressions;
* finite deterministic automata (DFA);
* finite nondeterministic automata (NFA);
* finite nondeterministic automata with epsilon transitions (ε-NFA).

The finite-alphabet assumption is necessary for the syntax used here, whose
atoms denote individual letters; see `UAM_KleeneCounterexample`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_RegexAutomataEquivalence

noncomputable section
open Classical

open UAM_DFAEval UAM_NFA UAM_EpsilonNFA
open UAM_RegularExpression UAM_RegularExpression.RegExp
open UAM_Kleene UAM_KleeneComplete UAM_Thompson

universe u

/-- Recognition by a DFA with a finite state type. -/
def IsFiniteDFARecognizable {α : Type u}
    (L : Set (UAM_Free.FreeMonoid α)) : Prop :=
  ∃ (Q : Type u) (_ : Fintype Q) (_ : DecidableEq Q)
    (A : DFA α Q), A.language = L

/-- Recognition by an NFA with a finite state type. -/
def IsFiniteNFARecognizable {α : Type u}
    (L : Set (UAM_Free.FreeMonoid α)) : Prop :=
  ∃ (Q : Type u) (_ : Fintype Q) (_ : DecidableEq Q)
    (A : NFA α Q), A.nfaLanguage = L

/-- Recognition by an epsilon-NFA with a finite state type. -/
def IsFiniteEpsilonNFARecognizable {α : Type u}
    (L : Set (UAM_Free.FreeMonoid α)) : Prop :=
  ∃ (Q : Type u) (_ : Fintype Q) (_ : DecidableEq Q)
    (A : EpsilonNFA α Q), A.epsilonLanguage = L

/-- Regular expressions and finite DFAs describe the same languages. -/
theorem regular_iff_finiteDFA {α : Type u} [Fintype α] [DecidableEq α]
    (L : Set (UAM_Free.FreeMonoid α)) :
    IsRegularLanguage L ↔ IsFiniteDFARecognizable L := by
  exact UAM_KleeneComplete.kleene_complete L

/-- Regular expressions and finite NFAs describe the same languages. -/
theorem regular_iff_finiteNFA {α : Type u} [Fintype α] [DecidableEq α]
    (L : Set (UAM_Free.FreeMonoid α)) :
    IsRegularLanguage L ↔ IsFiniteNFARecognizable L := by
  constructor
  · rintro ⟨r, rfl⟩
    let A := (thompsonNFA r).toNFA
    exact ⟨ThompsonState r, inferInstance, inferInstance, A, by
      dsimp [A]
      rw [← thompson_correct r]
      exact (thompsonNFA r).epsilonLanguage_eq_nfa_language⟩
  · rintro ⟨Q, hQ, dQ, A, rfl⟩
    have h := dfa_language_is_regular A.toDFA
    rw [← A.nfaLanguage_eq_toDFA_language]
    exact h

/-- Regular expressions and finite epsilon-NFAs describe the same languages. -/
theorem regular_iff_finiteEpsilonNFA {α : Type u} [Fintype α] [DecidableEq α]
    (L : Set (UAM_Free.FreeMonoid α)) :
    IsRegularLanguage L ↔ IsFiniteEpsilonNFARecognizable L := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨ThompsonState r, inferInstance, inferInstance, thompsonNFA r,
      thompson_correct r⟩
  · rintro ⟨Q, hQ, dQ, A, rfl⟩
    have h := (regular_iff_finiteNFA A.toNFA.nfaLanguage).2
      ⟨Q, hQ, dQ, A.toNFA, rfl⟩
    rw [← A.epsilonLanguage_eq_nfa_language]
    exact h

/-- Finite DFAs and finite NFAs recognize exactly the same languages. -/
theorem finiteDFA_iff_finiteNFA {α : Type u} [Fintype α] [DecidableEq α]
    (L : Set (UAM_Free.FreeMonoid α)) :
    IsFiniteDFARecognizable L ↔ IsFiniteNFARecognizable L := by
  rw [← regular_iff_finiteDFA L, ← regular_iff_finiteNFA L]

/-- Finite NFAs and finite epsilon-NFAs recognize exactly the same languages. -/
theorem finiteNFA_iff_finiteEpsilonNFA {α : Type u} [Fintype α] [DecidableEq α]
    (L : Set (UAM_Free.FreeMonoid α)) :
    IsFiniteNFARecognizable L ↔ IsFiniteEpsilonNFARecognizable L := by
  rw [← regular_iff_finiteNFA L, ← regular_iff_finiteEpsilonNFA L]

/-- Finite DFAs and finite epsilon-NFAs recognize exactly the same languages. -/
theorem finiteDFA_iff_finiteEpsilonNFA {α : Type u} [Fintype α] [DecidableEq α]
    (L : Set (UAM_Free.FreeMonoid α)) :
    IsFiniteDFARecognizable L ↔ IsFiniteEpsilonNFARecognizable L := by
  rw [← regular_iff_finiteDFA L, ← regular_iff_finiteEpsilonNFA L]

/-- Compiling a regular expression to a DFA and eliminating its states returns
an expression with the original denotational language. -/
theorem regex_dfa_regex_language {α : Type u} [Fintype α] [DecidableEq α]
    (r : RegExp α) :
    languageOf (dfaRegex (regexToDFA r)) = languageOf r := by
  rw [dfaRegex_language, regexToDFA_language]

/-- Eliminating the states of a finite DFA and compiling the resulting regular
expression preserves the DFA language. -/
theorem dfa_regex_dfa_language {α Q : Type u} [Fintype α] [DecidableEq α]
    [Fintype Q] [DecidableEq Q] (A : DFA α Q) :
    (regexToDFA (dfaRegex A)).language = A.language := by
  rw [regexToDFA_language, dfaRegex_language]

end
end UAM_RegexAutomataEquivalence
