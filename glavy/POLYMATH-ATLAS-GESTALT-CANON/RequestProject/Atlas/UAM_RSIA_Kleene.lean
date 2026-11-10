import Mathlib.Tactic
import RequestProject.Atlas.UAM_KleeneComplete
import RequestProject.Atlas.UAM_RSIA_System

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RSIA, Thompson construction, and Kleene's theorem

This module connects the complete RSIA protocol engine to the automata/regular-
expression equivalence.  The finiteness assumption on the Nerode quotient is
explicit: an arbitrary protocol language need not be regular.
-/

namespace UAM_RSIA

noncomputable section
open Classical

open UAM_RegularExpression UAM_RegularExpression.RegExp
open UAM_DFAEval
open UAM_KleeneComplete

universe u

/-- Compiling a regular expression by Thompson's construction and then
recovering a regular expression by state elimination preserves its language. -/
theorem regex_dfa_regex_language {α : Type u} [Fintype α] [DecidableEq α]
    (r : RegExp α) :
    languageOf (dfaRegex (regexToDFA r)) = languageOf r := by
  rw [dfaRegex_language, regexToDFA_language]

/-- A session whose Nerode quotient is finite has a regular expression for its
protocol language.  The expression is obtained by state elimination from the
canonical (minimal) attractor. -/
def Session.protocolRegex {α : Type u} [Fintype α] [DecidableEq α]
    (s : Session α) [Fintype (UAM_MyhillNerode.NerodeClass s.protocolLanguage)] :
    RegExp α :=
  dfaRegex s.attractor

/-- The expression extracted from a finite session attractor denotes exactly
its protocol language. -/
theorem Session.protocolRegex_language {α : Type u} [Fintype α]
    [DecidableEq α] (s : Session α)
    [Fintype (UAM_MyhillNerode.NerodeClass s.protocolLanguage)] :
    languageOf s.protocolRegex = s.protocolLanguage := by
  rw [Session.protocolRegex, dfaRegex_language, Session.attractor_language]

/-- Kleene's theorem specialized to an RSIA session: finiteness of the Nerode
quotient supplies both a regular expression and its Thompson-compiled DFA. -/
theorem Session.thompson_kleene_complete {α : Type u} [Fintype α]
    [DecidableEq α] (s : Session α)
    [Fintype (UAM_MyhillNerode.NerodeClass s.protocolLanguage)] :
    ∃ (r : RegExp α),
      languageOf r = s.protocolLanguage ∧
      (regexToDFA r).language = s.protocolLanguage := by
  refine ⟨s.protocolRegex, Session.protocolRegex_language s, ?_⟩
  simp [Session.protocolRegex]
  rw [regexToDFA_language, dfaRegex_language, Session.attractor_language]

/-- If a regular expression describes the current protocol, every finite RSIA
instruction stream preserves precisely the language of that expression. -/
theorem RSIAState.runInstructions_preserves_regex {α : Type u}
    (st : RSIAState α) (instructions : List (RoundInstruction α))
    (r : RegExp α) (hr : languageOf r = st.session.protocolLanguage) :
    (st.runInstructions instructions).session.protocolLanguage = languageOf r := by
  rw [RSIAState.runInstructions_preserves_language, hr]

/-- End-to-end RSIA/Kleene theorem.  Starting from a protocol with finite
Nerode quotient, state elimination yields an expression; after any mixture of
RSIA rounds its language is unchanged, and Thompson compilation of that same
expression recognizes the resulting protocol language. -/
theorem RSIAState.thompson_kleene_complete {α : Type u} [Fintype α]
    [DecidableEq α] (st : RSIAState α)
    [Fintype (UAM_MyhillNerode.NerodeClass st.session.protocolLanguage)]
    (instructions : List (RoundInstruction α)) :
    ∃ (r : RegExp α),
      languageOf r = (st.runInstructions instructions).session.protocolLanguage ∧
      (regexToDFA r).language =
        (st.runInstructions instructions).session.protocolLanguage := by
  haveI : Fintype (UAM_MyhillNerode.NerodeClass (st.runInstructions instructions).session.protocolLanguage) := by
    rw [RSIAState.runInstructions_preserves_language]
    exact inferInstance
  refine ⟨(st.runInstructions instructions).session.protocolRegex, Session.protocolRegex_language _, ?_⟩
  rw [Session.protocolRegex, regexToDFA_language, dfaRegex_language, Session.attractor_language]

end
end UAM_RSIA
