import Mathlib.Tactic
import RequestProject.Atlas.UAM_EpsilonNFA
import RequestProject.UAM_MyhillNerode

/-!
# Детерминизация: ε-NFA → NFA → DFA

Мост `NFA → DFA` (подмножественное построение, subset construction) и мост
`ε-NFA → NFA` (устранение ε-переходов через ε-замыкание).

Обе конструкции уже определены в архивном слое
(`UAM_NFA.NFA.toDFA`, `UAM_EpsilonNFA.EpsilonNFA.toNFA`); здесь они собраны в
единый интерфейс с теоремами корректности и с композицией
`ε-NFA → DFA`, замыкающей соответствующее ребро кольца эквивалентности.

Никакие типы не переопределяются: используются `UAM_NFA.NFA`,
`UAM_EpsilonNFA.EpsilonNFA` и `UAM_DFAEval.DFA` из существующих модулей.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_Ring

open UAM_DFAEval UAM_NFA UAM_EpsilonNFA

universe u

variable {α Q : Type u} [DecidableEq Q]

/-! ### §1. ε-замыкание и устранение ε-переходов -/

/-- ε-замыкание множества состояний ε-NFA: все состояния, достижимые из `S`
    цепочкой ε-переходов (включая само `S`). -/
def epsilonClosure (A : EpsilonNFA α Q) (S : Set Q) : Set Q :=
  A.epsilonClosure S

/-- Множество состояний содержится в своём ε-замыкании. -/
theorem subset_epsilonClosure (A : EpsilonNFA α Q) (S : Set Q) :
    S ⊆ epsilonClosure A S :=
  A.subset_closure S

/-- ε-замыкание идемпотентно. -/
theorem epsilonClosure_idem (A : EpsilonNFA α Q) (S : Set Q) :
    epsilonClosure A (epsilonClosure A S) = epsilonClosure A S :=
  A.closure_idem S

/-- Устранение ε-переходов: NFA, эквивалентный данному ε-NFA. -/
def epsilonRemoval (A : EpsilonNFA α Q) : NFA α Q := A.toNFA

/-- **Корректность устранения ε-переходов:** язык не меняется. -/
theorem epsilon_removal_correct (A : EpsilonNFA α Q) :
    (epsilonRemoval A).nfaLanguage = A.epsilonLanguage :=
  A.epsilonLanguage_eq_nfa_language

/-! ### §2. Подмножественное построение -/

open Classical in
/-- **Подмножественное построение (subset construction).** Детерминизация NFA:
    состояния строящегося DFA — подмножества множества состояний NFA,
    начальное состояние — `{q₀}`, переход — объединение переходов, принимающие
    множества — те, что пересекают множество принимающих состояний NFA. -/
noncomputable def subsetConstruction (A : NFA α Q) : DFA α (Set Q) := A.toDFA

open Classical in
/-- Состояние детерминизации после чтения слова `w` — в точности множество
    состояний NFA, достижимых по `w` из `S`. -/
theorem subsetConstruction_evalFrom (A : NFA α Q) (S : Set Q) (w : List α) :
    (subsetConstruction A).evalFrom S w = A.evalSet S w :=
  A.toDFA_evalFrom S w

open Classical in
/-- Состояние детерминизации после чтения `w` из начального состояния — это
    множество достижимых по `w` состояний NFA. -/
theorem subsetConstruction_eval (A : NFA α Q) (w : List α) :
    (subsetConstruction A).eval w = A.reachable w :=
  A.toDFA_evalFrom {A.q₀} w

open Classical in
/-- **Корректность детерминизации:** язык подмножественного построения совпадает
    с языком исходного NFA. -/
theorem subset_construction_correct (A : NFA α Q) :
    (subsetConstruction A).language = A.nfaLanguage :=
  A.nfaLanguage_eq_toDFA_language

/-! ### §3. Композиция: ε-NFA → DFA -/

open Classical in
/-- Детерминизация ε-NFA: сначала устраняются ε-переходы, затем выполняется
    подмножественное построение. -/
noncomputable def epsilonNFAToDFA (A : EpsilonNFA α Q) : DFA α (Set Q) :=
  subsetConstruction (epsilonRemoval A)

open Classical in
/-- **Корректность детерминизации ε-NFA:** полученный DFA распознаёт язык
    исходного ε-NFA. -/
theorem epsilonNFAToDFA_correct (A : EpsilonNFA α Q) :
    (epsilonNFAToDFA A).language = A.epsilonLanguage := by
  rw [epsilonNFAToDFA, subset_construction_correct, epsilon_removal_correct]

omit [DecidableEq Q] in
/-- Детерминизация конечного NFA конечна: множество состояний построенного DFA —
    это множество всех подмножеств конечного множества состояний NFA. -/
theorem finite_subsetConstruction_states [Finite Q] : Finite (Set Q) :=
  inferInstance

end UAM_Ring
