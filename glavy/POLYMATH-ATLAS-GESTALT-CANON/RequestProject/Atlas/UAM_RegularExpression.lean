import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages

/-!
# UAM — Регулярные выражения (Regular Expressions)

Индуктивный тип регулярных выражений над алфавитом `α` и их денотационная
семантика `languageOf` как подмножеств свободного моноида. Операции склеены с
уже существующими конструкциями над языками из `UAM_RegularLanguages`
(`languageConcat`, `kleeneStar`).
-/

namespace UAM_RegularExpression
universe u

open UAM_RegularLanguages

/-- Регулярное выражение над алфавитом `α`. -/
inductive RegExp (α : Type u) where
  /-- Пустой язык `∅`. -/
  | empty_set : RegExp α
  /-- Язык из одного пустого слова `{ε}`. -/
  | empty_str : RegExp α
  /-- Литерал: язык из одного однобуквенного слова. -/
  | atom : α → RegExp α
  /-- Объединение языков. -/
  | alt : RegExp α → RegExp α → RegExp α
  /-- Конкатенация языков. -/
  | concat : RegExp α → RegExp α → RegExp α
  /-- Звезда Клини. -/
  | star : RegExp α → RegExp α

namespace RegExp
variable {α : Type u}

/-- Денотационная семантика регулярного выражения: язык, который оно описывает. -/
def languageOf : RegExp α → Set (UAM_Free.FreeMonoid α)
  | empty_set => ∅
  | empty_str => {([] : UAM_Free.FreeMonoid α)}
  | atom a => {UAM_Free.FreeMonoid.of a}
  | alt r s => languageOf r ∪ languageOf s
  | concat r s => languageConcat (languageOf r) (languageOf s)
  | star r => kleeneStar (languageOf r)

/-! ### Уравнения семантики -/

@[simp] theorem languageOf_empty_set :
    languageOf (empty_set : RegExp α) = ∅ := rfl

@[simp] theorem languageOf_empty_str :
    languageOf (empty_str : RegExp α) = {([] : UAM_Free.FreeMonoid α)} := rfl

@[simp] theorem languageOf_atom (a : α) :
    languageOf (atom a) = {UAM_Free.FreeMonoid.of a} := rfl

@[simp] theorem languageOf_alt (r s : RegExp α) :
    languageOf (alt r s) = languageOf r ∪ languageOf s := rfl

@[simp] theorem languageOf_concat (r s : RegExp α) :
    languageOf (concat r s) = languageConcat (languageOf r) (languageOf s) := rfl

@[simp] theorem languageOf_star (r : RegExp α) :
    languageOf (star r) = kleeneStar (languageOf r) := rfl

/-! ### Простые следствия -/

/-- Пустое слово принадлежит `{ε}`. -/
theorem nil_mem_empty_str :
    ([] : UAM_Free.FreeMonoid α) ∈ languageOf (empty_str : RegExp α) := rfl

/-- Пустое слово принадлежит языку любой звезды. -/
theorem nil_mem_star (r : RegExp α) :
    ([] : UAM_Free.FreeMonoid α) ∈ languageOf (star r) :=
  kleeneStar_empty (languageOf r)

/-- Однобуквенное слово принадлежит языку соответствующего литерала. -/
theorem of_mem_atom (a : α) :
    UAM_Free.FreeMonoid.of a ∈ languageOf (atom a) := rfl

/-- Язык `concat` содержит склейки слов из компонент. -/
theorem concat_mem (r s : RegExp α) {w1 w2 : UAM_Free.FreeMonoid α}
    (h1 : w1 ∈ languageOf r) (h2 : w2 ∈ languageOf s) :
    w1 ++ w2 ∈ languageOf (concat r s) :=
  ⟨w1, w2, rfl, h1, h2⟩

/-- Язык `star` замкнут относительно конкатенации. -/
theorem star_concat_mem (r : RegExp α) {w1 w2 : UAM_Free.FreeMonoid α}
    (h1 : w1 ∈ languageOf (star r)) (h2 : w2 ∈ languageOf (star r)) :
    w1 ++ w2 ∈ languageOf (star r) :=
  kleeneStar_concat (languageOf r) w1 w2 h1 h2

/-- Язык регулярного выражения содержится в его звезде. -/
theorem subset_star (r : RegExp α) :
    languageOf r ⊆ languageOf (star r) :=
  kleeneStar_subset (languageOf r)

end RegExp
end UAM_RegularExpression
