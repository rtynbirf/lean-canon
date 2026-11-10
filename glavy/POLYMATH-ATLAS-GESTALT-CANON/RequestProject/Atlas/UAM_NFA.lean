import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_DFAEval

/-!
# UAM — Layer (Application): Недетерминированные конечные автоматы (NFA)

Недетерминированный конечный автомат (NFA) обобщает DFA: функция переходов
возвращает *множество* состояний. Слово допускается, если хотя бы один путь
приводит в принимающее состояние.

Основной результат — эквивалентность NFA и DFA через **подмножественное
построение** (`toDFA`): язык NFA совпадает с языком построенного по нему DFA,
состояниями которого служат подмножества исходного множества состояний.
-/

namespace UAM_NFA
universe u

/-- NFA над алфавитом `α` с множеством состояний `Q`. -/
structure NFA (α : Type u) (Q : Type u) [DecidableEq Q] where
  /-- Функция переходов: состояние × символ → множество состояний. -/
  δ : Q → α → Set Q
  /-- Начальное состояние. -/
  q₀ : Q
  /-- Множество принимающих состояний. -/
  F : Set Q

namespace NFA

variable {α Q : Type u} [DecidableEq Q]

/-- Шаг по множеству состояний: объединение переходов из всех состояний. -/
def stepSet (A : NFA α Q) (S : Set Q) (a : α) : Set Q := ⋃ q ∈ S, A.δ q a

/-- Вычисление множества достижимых состояний из множества `S` по слову `w`. -/
def evalSet (A : NFA α Q) (S : Set Q) : UAM_Free.FreeMonoid α → Set Q
  | [] => S
  | a :: w => A.evalSet (A.stepSet S a) w

/-- Множество состояний, достижимых из одного состояния `q` по слову `w`. -/
def reachableFrom (A : NFA α Q) (q : Q) (w : UAM_Free.FreeMonoid α) : Set Q :=
  A.evalSet {q} w

/-- Множество состояний, достижимых из начального по слову `w`. -/
def reachable (A : NFA α Q) (w : UAM_Free.FreeMonoid α) : Set Q :=
  A.evalSet {A.q₀} w

/-- Слово допускается NFA, если множество достижимых состояний пересекает
    множество принимающих. -/
def nfaAccepts (A : NFA α Q) (w : UAM_Free.FreeMonoid α) : Prop :=
  (A.reachable w ∩ A.F).Nonempty

/-- Язык NFA. -/
def nfaLanguage (A : NFA α Q) : Set (UAM_Free.FreeMonoid α) :=
  {w | A.nfaAccepts w}

/-! ### Базовые свойства -/

@[simp] theorem evalSet_nil (A : NFA α Q) (S : Set Q) : A.evalSet S [] = S := rfl

theorem evalSet_cons (A : NFA α Q) (S : Set Q) (a : α) (w : UAM_Free.FreeMonoid α) :
    A.evalSet S (a :: w) = A.evalSet (A.stepSet S a) w := rfl

theorem mem_stepSet (A : NFA α Q) (S : Set Q) (a : α) (q : Q) :
    q ∈ A.stepSet S a ↔ ∃ q' ∈ S, q ∈ A.δ q' a := by
  simp only [stepSet, Set.mem_iUnion, exists_prop]

/-- Ключевая лемма: вычисление множества по конкатенации разбивается на два
    последовательных вычисления. -/
theorem evalSet_concat (A : NFA α Q) (S : Set Q) (w₁ w₂ : UAM_Free.FreeMonoid α) :
    A.evalSet S (w₁ ++ w₂) = A.evalSet (A.evalSet S w₁) w₂ := by
  induction w₁ generalizing S with
  | nil => rfl
  | cons a ws ih => simp only [List.cons_append, evalSet, ih]

/-- Конкатенация для `reachableFrom`. -/
theorem reachableFrom_concat (A : NFA α Q) (q : Q) (w₁ w₂ : UAM_Free.FreeMonoid α) :
    A.reachableFrom q (w₁ ++ w₂) = A.evalSet (A.reachableFrom q w₁) w₂ := by
  unfold reachableFrom
  rw [evalSet_concat]

/-! ### Подмножественное построение (subset construction) -/

open Classical in
/-- Подмножественное построение: DFA, состояниями которого являются подмножества
    множества состояний NFA. -/
noncomputable def toDFA (A : NFA α Q) : UAM_DFAEval.DFA α (Set Q) where
  δ := fun S a => A.stepSet S a
  q₀ := {A.q₀}
  F := {S | (S ∩ A.F).Nonempty}

open Classical in
/-- Вычисление в `toDFA` совпадает с `evalSet` в NFA. -/
theorem toDFA_evalFrom (A : NFA α Q) (S : Set Q) (w : UAM_Free.FreeMonoid α) :
    (A.toDFA).evalFrom S w = A.evalSet S w := by
  induction w generalizing S with
  | nil => rfl
  | cons a ws ih => exact ih (A.stepSet S a)

open Classical in
/-- **Эквивалентность NFA и DFA:** язык подмножественного построения совпадает
    с языком исходного NFA. -/
theorem nfaLanguage_eq_toDFA_language (A : NFA α Q) :
    (A.toDFA).language = A.nfaLanguage := by
  ext w
  show (A.toDFA).accepts w ↔ A.nfaAccepts w
  show (A.toDFA).eval w ∈ (A.toDFA).F ↔ (A.reachable w ∩ A.F).Nonempty
  have hev : (A.toDFA).eval w = A.reachable w := by
    show (A.toDFA).evalFrom {A.q₀} w = A.evalSet {A.q₀} w
    exact toDFA_evalFrom A {A.q₀} w
  rw [hev]
  rfl

/-! ### Пример -/

/-- Тривиальный NFA с единственным состоянием, допускающий все слова. -/
def trivialNFA (α : Type u) : NFA α PUnit.{u+1} where
  δ := fun _ _ => Set.univ
  q₀ := PUnit.unit
  F := Set.univ

end NFA

end UAM_NFA
