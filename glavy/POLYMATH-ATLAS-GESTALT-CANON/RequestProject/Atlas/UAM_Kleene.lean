import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_DFAEval
import RequestProject.Atlas.UAM_NFA
import RequestProject.Atlas.UAM_RegularExpression
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_EpsilonNFA

/-!
# UAM — Теорема Клини: класс регулярных языков (Kleene)

Язык называется **регулярным**, если он описывается некоторым регулярным
выражением. Этот модуль устанавливает алгебраическую половину теоремы Клини:
класс регулярных языков содержит пустой язык, `{ε}` и однобуквенные языки и
замкнут относительно объединения, конкатенации (`languageConcat`) и звезды Клини
(`kleeneStar`); более того, это наименьший такой класс (принцип индукции по
регулярным выражениям).

**Замечание о полноте.** Полная эквивалентность «регулярный ⇔ распознаётся
конечным автоматом» (конструкция Томпсона в одну сторону и исключение состояний
в другую) — существенно более объёмный результат; здесь формализована
алгебраическая характеризация регулярных языков и её связь с языковыми
операциями из `UAM_RegularLanguages`.
-/

namespace UAM_Kleene
universe u

open UAM_RegularExpression UAM_RegularExpression.RegExp UAM_RegularLanguages

variable {α : Type u}

/-- Язык регулярен, если он задаётся некоторым регулярным выражением. -/
def IsRegularLanguage (L : Set (UAM_Free.FreeMonoid α)) : Prop :=
  ∃ r : RegExp α, languageOf r = L

/-! ### §1. Регулярность базовых языков -/

/-- Язык любого регулярного выражения регулярен. -/
theorem isRegular_of_regExp (r : RegExp α) : IsRegularLanguage (languageOf r) :=
  ⟨r, rfl⟩

/-- Пустой язык регулярен. -/
theorem isRegular_empty_set : IsRegularLanguage (∅ : Set (UAM_Free.FreeMonoid α)) :=
  ⟨empty_set, rfl⟩

/-- Язык `{ε}` регулярен. -/
theorem isRegular_empty_str :
    IsRegularLanguage ({([] : UAM_Free.FreeMonoid α)}) :=
  ⟨empty_str, rfl⟩

/-- Однобуквенный язык регулярен. -/
theorem isRegular_atom (a : α) :
    IsRegularLanguage ({UAM_Free.FreeMonoid.of a}) :=
  ⟨atom a, rfl⟩

/-! ### §2. Замкнутость относительно рациональных операций -/

/-- Объединение регулярных языков регулярно. -/
theorem isRegular_union {L₁ L₂ : Set (UAM_Free.FreeMonoid α)}
    (h₁ : IsRegularLanguage L₁) (h₂ : IsRegularLanguage L₂) :
    IsRegularLanguage (L₁ ∪ L₂) := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  exact ⟨alt r₁ r₂, by rw [languageOf_alt, hr₁, hr₂]⟩

/-- Конкатенация регулярных языков регулярна. -/
theorem isRegular_concat {L₁ L₂ : Set (UAM_Free.FreeMonoid α)}
    (h₁ : IsRegularLanguage L₁) (h₂ : IsRegularLanguage L₂) :
    IsRegularLanguage (languageConcat L₁ L₂) := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  exact ⟨concat r₁ r₂, by rw [languageOf_concat, hr₁, hr₂]⟩

/-- Звезда Клини регулярного языка регулярна. -/
theorem isRegular_star {L : Set (UAM_Free.FreeMonoid α)}
    (h : IsRegularLanguage L) :
    IsRegularLanguage (kleeneStar L) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨star r, by rw [languageOf_star, hr]⟩

/-! ### §3. Регулярные языки — наименьший замкнутый класс -/

/-- **Принцип индукции по регулярным выражениям.** Любой предикат `P` над
    языками, истинный на базовых языках и сохраняющийся при рациональных
    операциях, истинен на языке любого регулярного выражения. Иными словами,
    регулярные языки образуют наименьший класс, замкнутый относительно этих
    операций. -/
theorem regExp_induction {P : Set (UAM_Free.FreeMonoid α) → Prop}
    (hempty : P ∅)
    (hstr : P ({([] : UAM_Free.FreeMonoid α)}))
    (hatom : ∀ a : α, P ({UAM_Free.FreeMonoid.of a}))
    (hunion : ∀ L₁ L₂, P L₁ → P L₂ → P (L₁ ∪ L₂))
    (hconcat : ∀ L₁ L₂, P L₁ → P L₂ → P (languageConcat L₁ L₂))
    (hstar : ∀ L, P L → P (kleeneStar L)) :
    ∀ r : RegExp α, P (languageOf r) := by
  intro r
  induction r with
  | empty_set => exact hempty
  | empty_str => exact hstr
  | atom a => exact hatom a
  | alt r₁ r₂ ih₁ ih₂ => rw [languageOf_alt]; exact hunion _ _ ih₁ ih₂
  | concat r₁ r₂ ih₁ ih₂ => rw [languageOf_concat]; exact hconcat _ _ ih₁ ih₂
  | star r ih => rw [languageOf_star]; exact hstar _ ih

/-- Характеризация: язык регулярен тогда и только тогда, когда он получается из
    базовых языков конечным числом рациональных операций (сформулировано как
    предикат `C`, замкнутый относительно операций и содержащий базовые языки:
    всякий такой `C` содержит все регулярные языки). -/
theorem isRegular_minimal {C : Set (UAM_Free.FreeMonoid α) → Prop}
    (hempty : C ∅)
    (hstr : C ({([] : UAM_Free.FreeMonoid α)}))
    (hatom : ∀ a : α, C ({UAM_Free.FreeMonoid.of a}))
    (hunion : ∀ L₁ L₂, C L₁ → C L₂ → C (L₁ ∪ L₂))
    (hconcat : ∀ L₁ L₂, C L₁ → C L₂ → C (languageConcat L₁ L₂))
    (hstar : ∀ L, C L → C (kleeneStar L))
    {L : Set (UAM_Free.FreeMonoid α)} (hL : IsRegularLanguage L) : C L := by
  obtain ⟨r, hr⟩ := hL
  rw [← hr]
  exact regExp_induction hempty hstr hatom hunion hconcat hstar r

end UAM_Kleene
