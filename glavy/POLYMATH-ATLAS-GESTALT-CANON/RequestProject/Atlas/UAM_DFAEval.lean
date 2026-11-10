import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_Congruence
import RequestProject.Atlas.UAM_Morphism

/-!
# UAM — Layer 1: Семантика DFA (DFAEval)

Детерминированные конечные автоматы (DFA) и их семантика: каноническое правое
действие свободного моноида `FreeMonoid α` на множестве состояний `Q`.

Этот модуль выделяет DFA-инфраструктуру в самостоятельный слой: он определяет
структуру `DFA`, функции `evalFrom`, `eval`, язык автомата и ключевые леммы о
конкатенации и сохранении равенства состояний. Никакой теории Нероуда,
регулярных выражений или морфизмов — только автоматная база.

**Важно.** `UAM_Free.FreeMonoid α` = `List α` (это `abbrev`), поэтому доступны все
леммы `List`. Тип `FreeMonoid` всегда пишется с квалификатором `UAM_Free.` во
избежание конфликта с `_root_.FreeMonoid` из Mathlib.
-/

namespace UAM_DFAEval
universe u

/-- DFA над алфавитом `α` с множеством состояний `Q`. -/
structure DFA (α : Type u) (Q : Type u) [DecidableEq Q] where
  /-- Функция переходов. -/
  δ : Q → α → Q
  /-- Начальное состояние. -/
  q₀ : Q
  /-- Множество принимающих состояний. -/
  F : Set Q

namespace DFA

variable {α Q : Type u} [DecidableEq Q] {A : DFA α Q}

/-- Вычисление состояния после обработки слова `w` из состояния `q`.
    Слово читается слева направо: `evalFrom q [a, b] = evalFrom (δ q a) [b]`. -/
def evalFrom (q : Q) : UAM_Free.FreeMonoid α → Q
  | [] => q
  | a :: w => evalFrom (A.δ q a) w

/-- Вычисление из начального состояния. -/
def eval (w : UAM_Free.FreeMonoid α) : Q := A.evalFrom A.q₀ w

/-- Слово `w` допускается автоматом. -/
def accepts (w : UAM_Free.FreeMonoid α) : Prop := A.eval w ∈ A.F

/-- Язык автомата: множество допускаемых слов. -/
def language : Set (UAM_Free.FreeMonoid α) := {w | A.accepts w}

/-! ### Базовые свойства evalFrom -/

/-- evalFrom для пустого слова. -/
theorem evalFrom_nil (q : Q) : A.evalFrom q [] = q := rfl

/-- evalFrom для одного символа. -/
theorem evalFrom_single (q : Q) (a : α) : A.evalFrom q [a] = A.δ q a := rfl

/-- evalFrom для cons (определяющее равенство). -/
theorem evalFrom_cons (q : Q) (a : α) (w : UAM_Free.FreeMonoid α) :
    A.evalFrom q (a :: w) = A.evalFrom (A.δ q a) w := rfl

/-! ### Базовые свойства eval -/

/-- eval для пустого слова = q₀. -/
theorem eval_nil : A.eval [] = A.q₀ := rfl

/-- eval для одного символа. -/
theorem eval_single (a : α) : A.eval [a] = A.δ A.q₀ a := rfl

/-! ### Конкатенация (ключевые леммы) -/

/-- Ключевая лемма: evalFrom для конкатенации.
    Сначала обрабатываем `w₁` из `q`, затем `w₂` из полученного состояния. -/
theorem evalFrom_concat (q : Q) (w₁ w₂ : UAM_Free.FreeMonoid α) :
    A.evalFrom q (w₁ ++ w₂) = A.evalFrom (A.evalFrom q w₁) w₂ := by
  induction w₁ generalizing q with
  | nil => rfl
  | cons a ws ih => simp [evalFrom, ih]

/-- eval для конкатенации: через evalFrom из состояния `eval w₁`. -/
theorem eval_concat (w₁ w₂ : UAM_Free.FreeMonoid α) :
    A.eval (w₁ ++ w₂) = A.evalFrom (A.eval w₁) w₂ :=
  A.evalFrom_concat A.q₀ w₁ w₂

/-! ### Сохранение равенства (инфраструктура для Nerode-теории) -/

/-- Если два слова приводят автомат в одно состояние, то после добавления
    любого суффикса результат тоже совпадает. КЛЮЧЕВАЯ лемма, используется
    в ReverseMyhillNerode, DFA-гомоморфизмах и минимизации. -/
theorem eval_eq_of_eval_eq {w₁ w₂ : UAM_Free.FreeMonoid α}
    (h : A.eval w₁ = A.eval w₂) (v : UAM_Free.FreeMonoid α) :
    A.eval (w₁ ++ v) = A.eval (w₂ ++ v) := by
  rw [A.eval_concat w₁ v, A.eval_concat w₂ v, h]

/-- Аналог `eval_eq_of_eval_eq`, но для `evalFrom`: если два слова действуют
    одинаково на всех состояниях, то результаты после суффикса совпадают. -/
theorem evalFrom_eq_of_eval_eq {w₁ w₂ : UAM_Free.FreeMonoid α}
    (h : ∀ q, A.evalFrom q w₁ = A.evalFrom q w₂) (q : Q)
    (v : UAM_Free.FreeMonoid α) :
    A.evalFrom q (w₁ ++ v) = A.evalFrom q (w₂ ++ v) := by
  rw [A.evalFrom_concat q w₁ v, A.evalFrom_concat q w₂ v, h]

/-! ### Язык -/

/-- `w ∈ language A ↔ accepts A w`. -/
theorem mem_language_iff (w : UAM_Free.FreeMonoid α) :
    w ∈ A.language ↔ A.accepts w := Iff.rfl

/-- Допускающее слово принадлежит языку. -/
theorem accepts_mem (w : UAM_Free.FreeMonoid α) (h : A.accepts w) :
    w ∈ A.language := h

/-- Принадлежность языку влечёт допускаемость. -/
theorem mem_accepts (w : UAM_Free.FreeMonoid α) (h : w ∈ A.language) :
    A.accepts w := h

end DFA

end UAM_DFAEval
