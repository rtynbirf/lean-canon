import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_ReverseMyhillNerode
import RequestProject.Atlas.UAM_DFAHomomorphism

/-!
# UAM — Минимальный DFA (Minimal DFA)

Минимальный (приведённый) DFA языка строится как фактор произвольного
распознающего DFA по отношению Нероуда на состояниях
(`UAM_DFAHomomorphism.quotientDFA`). Он распознаёт тот же язык и приведён
(в нём нет двух различных эквивалентных состояний).

**Замечание.** Минимальный DFA соответствует *правому* отношению Нероуда на
состояниях. Он, вообще говоря, меньше автомата, построенного по синтаксическому
моноиду (который использует *двустороннюю* синтаксическую конгруэнцию), но связан
с ним через теорему Майхилла–Нероуда: конечность синтаксического моноида
равносильна распознаваемости языка конечным DFA.
-/

namespace UAM_MinimalDFA
universe u

open UAM_DFAEval UAM_DFAHomomorphism Classical

variable {α Q : Type u} [DecidableEq Q]

/-- Минимальный DFA распознающего автомата `A`: фактор по отношению Нероуда. -/
noncomputable def minimalDFA (A : DFA α Q) :
    DFA α (Quotient (stateNerodeSetoid A)) :=
  quotientDFA A

/-- Минимальный DFA распознаёт тот же язык. -/
theorem minimalDFA_language (A : DFA α Q) :
    (minimalDFA A).language = A.language :=
  quotientDFA_language A

/-- Минимальный DFA приведён: различных Нероуд-эквивалентных состояний нет. -/
theorem minimalDFA_reduced (A : DFA α Q)
    (S₁ S₂ : Quotient (stateNerodeSetoid A))
    (h : stateNerodeRel (minimalDFA A) S₁ S₂) : S₁ = S₂ :=
  quotientDFA_reduced A S₁ S₂ h

/-- Множество состояний минимального DFA конечно, если исходный автомат конечен. -/
noncomputable instance instFintypeMinimalStates (A : DFA α Q) [Fintype Q] :
    Fintype (Quotient (stateNerodeSetoid A)) :=
  Fintype.ofSurjective (Quotient.mk (stateNerodeSetoid A))
    (fun q => Quotient.exists_rep q)

/-! ### §. Связь с синтаксическим моноидом (теорема Майхилла–Нероуда) -/

/-- **Майхилл–Нероуд (⇐):** если синтаксический моноид языка `L` конечен, то `L`
    распознаётся некоторым конечным DFA. -/
theorem myhillNerode_backward (L : Set (UAM_Free.FreeMonoid α))
    [Fintype (UAM_RegularLanguages.SyntacticMonoid L)]
    [DecidableEq (UAM_RegularLanguages.SyntacticMonoid L)] :
    ∃ (Q : Type u) (_ : Fintype Q) (_ : DecidableEq Q)
      (A : UAM_DFAEval.DFA α Q), A.language = L :=
  UAM_RegularLanguages.myhillNerode_finite_syntactic L

/-- **Майхилл–Нероуд (⇒):** если язык `L` распознаётся конечным DFA, то его
    синтаксический моноид конечен. -/
noncomputable def myhillNerode_forward {L : Set (UAM_Free.FreeMonoid α)}
    (A : DFA α Q) (hL : A.language = L) [Fintype Q] :
    Fintype (UAM_RegularLanguages.SyntacticMonoid L) :=
  UAM_ReverseMyhillNerode.fintype_syntacticMonoid_of_dfa A hL

end UAM_MinimalDFA
