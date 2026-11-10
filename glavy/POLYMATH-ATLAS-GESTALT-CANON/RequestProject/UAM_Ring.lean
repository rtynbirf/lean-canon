import Mathlib.Tactic
import RequestProject.Atlas.UAM_KleeneComplete
import RequestProject.UAM_SubsetConstruction
import RequestProject.UAM_Minimization

/-!
# Замыкание кольца эквивалентности RegExp ↔ ε-NFA ↔ NFA ↔ DFA ↔ MinDFA

Все шесть переходов кольца собраны здесь вместе, каждый — с доказанной
теоремой корректности:

| Переход | Конструкция | Теорема |
|---------|-------------|---------|
| RegExp → ε-NFA | `UAM_Thompson.thompsonNFA` | `regexp_to_epsilonNFA` |
| ε-NFA → NFA | `epsilonRemoval` | `epsilonNFA_to_NFA` |
| NFA → DFA | `subsetConstruction` | `nfa_to_dfa` |
| DFA → MinDFA | `minimizeDFA` | `dfa_to_minDFA` |
| MinDFA → RegExp | `UAM_KleeneComplete.dfaRegex` | `dfa_to_regexp` |
| полный оборот | `regexRoundTrip` | `regexRoundTrip_language` |

Дополнительно: критерий регулярности через конечность индекса отношения
Майхилла–Нероуда (`regular_iff_finite_myhill_nerode_index`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_Ring

open UAM_DFAEval UAM_NFA UAM_EpsilonNFA UAM_RegularExpression UAM_RegularExpression.RegExp UAM_Kleene
open UAM_RegularLanguages UAM_Thompson UAM_KleeneComplete
open Classical

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ### §1. Шесть переходов -/

omit [Fintype α] [DecidableEq α] in
/-- **RegExp → ε-NFA** (конструкция Томпсона). -/
theorem regexp_to_epsilonNFA (r : RegExp α) :
    (thompsonNFA r).epsilonLanguage = languageOf r :=
  thompson_correct r

omit [Fintype α] [DecidableEq α] in
/-- **ε-NFA → NFA** (устранение ε-переходов). -/
theorem epsilonNFA_to_NFA {Q : Type u} [DecidableEq Q] (A : EpsilonNFA α Q) :
    (epsilonRemoval A).nfaLanguage = A.epsilonLanguage :=
  epsilon_removal_correct A

omit [Fintype α] [DecidableEq α] in
/-- **NFA → DFA** (подмножественное построение). -/
theorem nfa_to_dfa {Q : Type u} [DecidableEq Q] (A : NFA α Q) :
    (subsetConstruction A).language = A.nfaLanguage :=
  subset_construction_correct A

omit [Fintype α] [DecidableEq α] in
/-- **DFA → MinDFA** (минимизация через отношение Нероуда). -/
theorem dfa_to_minDFA {Q : Type u} [DecidableEq Q] (M : DFA α Q) :
    (minimizeDFA M).language = M.language :=
  minimize_correct M

/-- **DFA → RegExp** (устранение состояний). В частности, применимо к
    минимальному автомату, что и замыкает кольцо. -/
theorem dfa_to_regexp {Q : Type u} [Fintype Q] [DecidableEq Q] (M : DFA α Q) :
    languageOf (dfaRegex M) = M.language :=
  dfaRegex_language M

/-! ### §2. Полный оборот кольца -/

/-- Детерминизация регулярного выражения: Томпсон, устранение ε-переходов,
    подмножественное построение. -/
noncomputable def regexToDeterministic (r : RegExp α) :
    DFA α (Set (ThompsonState r)) :=
  subsetConstruction (epsilonRemoval (thompsonNFA r))

omit [Fintype α] [DecidableEq α] in
/-- Детерминизация регулярного выражения распознаёт его язык. -/
theorem regexToDeterministic_language (r : RegExp α) :
    (regexToDeterministic r).language = languageOf r := by
  rw [regexToDeterministic, nfa_to_dfa, epsilonNFA_to_NFA, regexp_to_epsilonNFA]

/-- Минимальный DFA регулярного выражения. -/
noncomputable def regexToMinimalDFA (r : RegExp α) :
    DFA α (MinState (regexToDeterministic r)) :=
  minimizeDFA (regexToDeterministic r)

omit [Fintype α] [DecidableEq α] in
/-- Минимальный DFA регулярного выражения распознаёт его язык. -/
theorem regexToMinimalDFA_language (r : RegExp α) :
    (regexToMinimalDFA r).language = languageOf r := by
  rw [regexToMinimalDFA, dfa_to_minDFA, regexToDeterministic_language]

/-- Полный оборот кольца: RegExp → ε-NFA → NFA → DFA → MinDFA → RegExp. -/
noncomputable def regexRoundTrip (r : RegExp α) : RegExp α :=
  dfaRegex (regexToMinimalDFA r)

/-- **Кольцо замкнуто.** Полный оборот RegExp → ε-NFA → NFA → DFA → MinDFA →
    RegExp сохраняет язык. -/
theorem regexRoundTrip_language (r : RegExp α) :
    languageOf (regexRoundTrip r) = languageOf r := by
  show languageOf (dfaRegex (regexToMinimalDFA r)) = languageOf r
  rw [dfa_to_regexp, regexToMinimalDFA_language]

/-! ### §3. Критерий регулярности -/

/-- **Регулярность ⟺ конечный индекс Майхилла–Нероуда** (над конечным
    алфавитом): язык задаётся регулярным выражением тогда и только тогда, когда
    отношение неразличимости имеет конечный индекс. -/
theorem regular_iff_finite_myhill_nerode_index (L : Set (List α)) :
    IsRegularLanguage L ↔ Nonempty (Fintype (MyhillNerodeQuot L)) := by
  rw [kleene_complete L]
  exact (myhill_nerode_finite_iff_regular L).symm

end UAM_Ring
