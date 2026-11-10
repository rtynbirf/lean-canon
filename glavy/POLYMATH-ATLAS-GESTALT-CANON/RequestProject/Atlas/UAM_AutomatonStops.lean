import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Reachability
import RequestProject.Atlas.UAM_Cayley
import RequestProject.Atlas.UAM_Morphism
import RequestProject.Atlas.UAM_Action
import RequestProject.Atlas.UAM_DFAEval
import RequestProject.Atlas.UAM_TransitionMonoid
import RequestProject.Atlas.UAM_Beginning
import RequestProject.Atlas.UAM_FiniteSemigroup
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_ReverseMyhillNerode

/-!
# UAM — Конечный автомат неизбежно останавливается структурно

Конечное вычисление не может быть «чистым началом»: в конечном моноиде
переходов неизбежно возникает идемпотент. Поэтому повторение некоторого
положительного числа копий любого слова даёт преобразование, повторное
применение которого уже ничего не меняет.

Здесь «остановка» означает не завершение исполнения в операционном смысле, а
структурную стабилизацию действия: преобразование становится идемпотентным.
Конечность тем самым выступает не инженерным ограничением, а математическим
принуждением к точкам стабилизации.

В исходной записи `List.replicate n w` имеет тип `List (List α)`, поскольку
`FreeMonoid α = List α`, и потому не может непосредственно быть аргументом
`actionHom`. Ниже используется типово корректное повторённое слово
`(List.replicate n w).flatten`.
-/

namespace UAM_AutomatonStops
universe u

open UAM_Idempotent UAM_Action
open UAM_DFAEval UAM_TransitionMonoid

/-! ### §1. Идемпотентное действие и повторение слова -/

/-- Слово действует идемпотентно в состоянии `q`, если второе применение слова
    не изменяет результат первого. -/
def IdempotentAction {α Q : Type u} [DecidableEq Q]
    (A : UAM_DFAEval.DFA α Q) (q : Q) (w : UAM_Free.FreeMonoid α) : Prop :=
  A.evalFrom q w = A.evalFrom (A.evalFrom q w) w

/-- Слово, полученное конкатенацией `n` копий `w`. -/
def repeatedWord {α : Type u} (w : UAM_Free.FreeMonoid α) (n : ℕ) :
    UAM_Free.FreeMonoid α :=
  (List.replicate n w).flatten

/-- После `n` повторений слово задаёт идемпотентное преобразование состояний. -/
def StabilizesAt {α Q : Type u} [DecidableEq Q]
    (A : UAM_DFAEval.DFA α Q) (w : UAM_Free.FreeMonoid α) (n : ℕ) : Prop :=
  IsIdempotent (actionHom A (repeatedWord w n))

/-! ### §2. Идемпотент в моноиде переходов -/

/-- Моноид переходов всякого конечного DFA содержит идемпотентное
    преобразование. Формально заявленное утверждение уже выполняется для
    тождественного перехода, представленного пустым словом. -/
theorem dfa_transition_monoid_has_idempotent {α Q : Type u}
    [DecidableEq Q] [Fintype Q] (A : UAM_DFAEval.DFA α Q) :
    ∃ f : Q → Q, f ∈ (UAM_TransitionMonoid.TransitionMonoid A).carrier ∧
      IsIdempotent f := by
  refine ⟨1, ?_, ?_⟩
  · refine ⟨[], ?_⟩
    exact (actionHom A).map_one
  · simp [IsIdempotent]

/-! ### §3. Степень любого действия стабилизируется -/

/-- Действие слова, повторённого `n` раз, совпадает с `n`-й степенью
    действия исходного слова. -/
theorem actionHom_repeatedWord {α Q : Type u} [DecidableEq Q]
    (A : UAM_DFAEval.DFA α Q) (w : UAM_Free.FreeMonoid α) (n : ℕ) :
    actionHom A (repeatedWord w n) = (actionHom A w) ^ n := by
  induction n with
  | zero =>
      ext q
      rfl
  | succ n ih =>
      rw [pow_succ']
      ext q
      simp only [repeatedWord, List.replicate_succ, List.flatten_cons,
        actionHom_apply, UAM_Action.mul_apply]
      rw [A.evalFrom_concat]
      exact congrFun ih (A.evalFrom q w)

/-- Для любого слова существует положительное число повторений, после которого
    соответствующее преобразование всего множества состояний идемпотентно. -/
theorem action_stabilizes {α Q : Type u}
    [DecidableEq Q] [Fintype Q] (A : UAM_DFAEval.DFA α Q)
    (w : UAM_Free.FreeMonoid α) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotent (actionHom A (repeatedWord w n)) := by
  obtain ⟨n, hn, hidem⟩ :=
    UAM_FiniteSemigroup.exists_idempotent_pow (actionHom A w)
  refine ⟨n, hn, ?_⟩
  rw [actionHom_repeatedWord]
  exact hidem

/-! ### §4. Синтаксический моноид регулярного языка -/

/-- Язык, распознаваемый конечным DFA, имеет идемпотент в своём
    синтаксическом моноиде. -/
theorem syntactic_monoid_has_idempotent {α Q : Type u}
    {L : Set (UAM_Free.FreeMonoid α)} [DecidableEq Q] [Fintype Q]
    (A : UAM_DFAEval.DFA α Q) (hL : A.language = L) :
    ∃ e : UAM_RegularLanguages.SyntacticMonoid L, IsIdempotent e := by
  letI : Fintype (UAM_RegularLanguages.SyntacticMonoid L) :=
    UAM_ReverseMyhillNerode.fintype_syntacticMonoid_of_dfa A hL
  exact UAM_FiniteSemigroup.exists_idempotent

/-! ### §5. Конечный автомат не является «чистым началом» -/

/-- Моноид преобразований конечного множества состояний не может
    удовлетворять аксиомам структуры «чистого начала». -/
theorem no_finite_dfa_is_beginning {α Q : Type u}
    [DecidableEq Q] [Fintype Q] : UAM_DFAEval.DFA α Q →
    ¬UAM_Beginning.IsBeginningStructure (Q → Q) :=
  fun _ => UAM_Beginning.finite_beginning_impossible (M := Q → Q)

/-! ### §6. Конкретная стабилизация вычисления -/

/-- Конкретная версия стабилизации: из любого состояния повторённое
    слово после первого применения приходит туда же, что и после второго. -/
theorem eval_stabilizes {α Q : Type u}
    [DecidableEq Q] [Fintype Q] (A : UAM_DFAEval.DFA α Q)
    (q : Q) (w : UAM_Free.FreeMonoid α) :
    ∃ n : ℕ, 0 < n ∧
      A.evalFrom q (repeatedWord w n) =
        A.evalFrom (A.evalFrom q (repeatedWord w n)) (repeatedWord w n) := by
  obtain ⟨n, hn, hidem⟩ := action_stabilizes A w
  refine ⟨n, hn, ?_⟩
  have hq := congrFun hidem q
  simpa only [UAM_Action.mul_apply, actionHom_apply] using hq.symm

end UAM_AutomatonStops
