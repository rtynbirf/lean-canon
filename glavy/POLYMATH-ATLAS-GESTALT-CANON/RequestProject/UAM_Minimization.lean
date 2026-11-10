import Mathlib.Tactic
import RequestProject.UAM_MyhillNerode

/-!
# Минимизация DFA через Майхилла–Нероуда

Минимизация произвольного DFA `M` — это факторизация по отношению Нероуда на
состояниях: два состояния склеиваются, если из них принимаются одни и те же
продолжения. Здесь доказано:

* `minimize_correct` — минимизация не меняет язык;
* `minimize_state_reduced` — в результате нет двух различных эквивалентных
  состояний;
* `minimize_accessible` / `minimize_reduced` — если исходный автомат достижим,
  то результат приведён (достижим и различим);
* `minimize_minimal` — никакой DFA, распознающий тот же язык, не имеет меньше
  состояний, чем результат минимизации;
* `minimize_unique_up_to_rename` — два минимальных DFA одного языка изоморфны.

Типы и базовые конструкции берутся из существующих модулей
(`UAM_DFAHomomorphism.quotientDFA`, `UAM_MinimalDFA.minimalDFA`,
`UAM_MinimalUnique`), ничего не переопределяется.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_Ring

open UAM_DFAEval UAM_DFAHomomorphism UAM_MyhillNerode UAM_MinimalUnique
open Classical

universe u

variable {α Q Q₁ Q₂ : Type u} [DecidableEq Q] [DecidableEq Q₁] [DecidableEq Q₂]

/-! ### §1. Конструкция -/

/-- Состояния минимизированного автомата: классы Нероуд-эквивалентных
    состояний исходного автомата. -/
abbrev MinState (M : DFA α Q) := Quotient (stateNerodeSetoid M)

/-- **Минимизация DFA.** Состояния — классы эквивалентности состояний по
    отношению Нероуда, переход `δ([q], a) = [δ(q, a)]`, начальное состояние
    `[q₀]`, принимающие классы — классы принимающих состояний. -/
noncomputable def minimizeDFA (M : DFA α Q) : DFA α (MinState M) :=
  UAM_MinimalDFA.minimalDFA M

/-- Вычисление в минимизированном автомате — это класс вычисления в исходном. -/
theorem minimizeDFA_eval (M : DFA α Q) (w : List α) :
    (minimizeDFA M).eval w = Quotient.mk (stateNerodeSetoid M) (M.eval w) :=
  quotientDFA_evalFrom M M.q₀ w

/-- Множество состояний минимизированного автомата конечно, если конечно
    множество состояний исходного. -/
noncomputable instance instFintypeMinState (M : DFA α Q) [Fintype Q] :
    Fintype (MinState M) :=
  UAM_MinimalDFA.instFintypeMinimalStates M

/-! ### §2. Корректность -/

/-- **Корректность минимизации:** язык не меняется. -/
theorem minimize_correct (M : DFA α Q) :
    DFALanguage (minimizeDFA M) = DFALanguage M :=
  UAM_MinimalDFA.minimalDFA_language M

/-- В минимизированном автомате различные состояния различимы. -/
theorem minimize_state_reduced (M : DFA α Q) : IsStateReduced (minimizeDFA M) :=
  fun S₁ S₂ h => UAM_MinimalDFA.minimalDFA_reduced M S₁ S₂ h

/-- Минимизация сохраняет достижимость состояний. -/
theorem minimize_accessible (M : DFA α Q) (hacc : IsAccessible M) :
    IsAccessible (minimizeDFA M) := by
  intro S
  refine Quotient.inductionOn S ?_
  intro q
  obtain ⟨w, hw⟩ := hacc q
  exact ⟨w, by rw [minimizeDFA_eval, hw]⟩

/-- Минимизация достижимого автомата даёт приведённый автомат. -/
theorem minimize_reduced (M : DFA α Q) (hacc : IsAccessible M) :
    IsReduced (minimizeDFA M) :=
  ⟨minimize_accessible M hacc, minimize_state_reduced M⟩

/-! ### §3. Минимальность -/

/-- Минимизированный достижимый автомат изоморфен каноническому автомату
    Майхилла–Нероуда своего языка. -/
noncomputable def minimizeIsoCanonical (M : DFA α Q) (hacc : IsAccessible M) :
    DFAIso (minimizeDFA M) (canonicalDFA (DFALanguage M)) :=
  reducedIsoCanonical (DFALanguage M) (minimizeDFA M) (minimize_reduced M hacc)
    (minimize_correct M)

/-- **Минимальность.** Никакой DFA, распознающий тот же язык, не может иметь
    меньше состояний, чем результат минимизации достижимого автомата. -/
theorem minimize_minimal (M : DFA α Q) [Fintype Q] (hacc : IsAccessible M)
    (N : DFA α Q₁) [Fintype Q₁] (hN : DFALanguage N = DFALanguage M) :
    Fintype.card (MinState M) ≤ Fintype.card Q₁ := by
  letI : Fintype (NerodeClass (DFALanguage M)) :=
    Fintype.ofEquiv (MinState M) (minimizeIsoCanonical M hacc).toEquiv
  rw [Fintype.card_congr (minimizeIsoCanonical M hacc).toEquiv]
  exact canonicalDFA_card_le (DFALanguage M) N hN

/-- **Единственность с точностью до переименования состояний.** Два приведённых
    (минимальных) DFA, распознающих один и тот же язык, изоморфны. -/
noncomputable def minimize_unique_up_to_rename (M₁ : DFA α Q₁) (M₂ : DFA α Q₂)
    (h₁ : IsReduced M₁) (h₂ : IsReduced M₂)
    (hL : DFALanguage M₁ = DFALanguage M₂) : DFAIso M₁ M₂ :=
  minimal_dfa_unique_up_to_iso M₁ M₂ h₁ h₂ hL

/-- Результаты минимизации двух достижимых автоматов с одним языком
    изоморфны. -/
noncomputable def minimizeDFA_unique (M₁ : DFA α Q₁) (M₂ : DFA α Q₂)
    (h₁ : IsAccessible M₁) (h₂ : IsAccessible M₂)
    (hL : DFALanguage M₁ = DFALanguage M₂) :
    DFAIso (minimizeDFA M₁) (minimizeDFA M₂) :=
  minimize_unique_up_to_rename (minimizeDFA M₁) (minimizeDFA M₂)
    (minimize_reduced M₁ h₁) (minimize_reduced M₂ h₂)
    (by rw [minimize_correct, minimize_correct, hL])

end UAM_Ring
