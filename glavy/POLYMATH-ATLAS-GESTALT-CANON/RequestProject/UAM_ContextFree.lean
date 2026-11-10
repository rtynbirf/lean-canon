/-
# UAM — расширение на контекстно-свободные языки: CFG, PDA и их эквивалентность

Слой UAM в проекте покрывал регулярные языки (Майхилл–Нероуд, подмножественное
строительство, минимизация, Клини).  Этот модуль добавляет следующий уровень
иерархии Хомского.

Формализовано:

* `Grammar` — контекстно-свободная грамматика: правила `A → β`, где
  `β : List (N ⊕ T)` — сентенциальная форма, и стартовый нетерминал;
* `Yields` — отношение вывода: сентенциальная форма порождает терминальное
  слово (индуктивное определение, эквивалентное левому выводу);
* `PDA` — автомат с магазинной памятью **без конечного управления**
  (одно состояние) и с допуском **по пустому магазину**; конфигурация —
  пара «магазин × непрочитанный вход», шаг — `PStep`;
* `Grammar.toPDA` и `pda_language_toPDA` — **каждый КС-язык распознаётся
  автоматом с магазинной памятью** (нисходящий автомат грамматики);
* `PDA.toGrammar` и `grammar_language_toGrammar` — **каждый язык такого
  автомата контекстно-свободен**;
* `contextFree_iff_pda` — эквивалентность CFG ≡ PDA в этом классе.

**Граница формализации.**  Автомат здесь бесстековым управлением не обладает:
у него один состояние и допуск по пустому магазину.  Это стандартная
нормальная форма (общий PDA сводится к ней конструкцией «тройки состояний»);
сама эта редукция в объём модуля не входит и не утверждается.

Все утверждения доказаны; `sorry` и новых аксиом нет.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM.ContextFree

universe u v w

variable {N T Γ : Type u}

/-! ## Контекстно-свободные грамматики -/

/-- Контекстно-свободная грамматика: отношение «`A → β` есть правило» и
стартовый нетерминал.  Сентенциальная форма — список символов `N ⊕ T`. -/
structure Grammar (N T : Type u) where
  /-- Правила грамматики: `rule A β` означает `A → β`. -/
  rule : N → List (N ⊕ T) → Prop
  /-- Стартовый нетерминал. -/
  start : N

/-- Отношение вывода: сентенциальная форма `α` порождает терминальное слово `w`. -/
inductive Yields (g : Grammar N T) : List (N ⊕ T) → List T → Prop
  /-- Пустая форма порождает пустое слово. -/
  | nil : Yields g [] []
  /-- Терминал читается как он есть. -/
  | term {a : T} {α : List (N ⊕ T)} {w : List T} :
      Yields g α w → Yields g (Sum.inr a :: α) (a :: w)
  /-- Нетерминал раскрывается по правилу. -/
  | nonterm {A : N} {β α : List (N ⊕ T)} {u w : List T} :
      g.rule A β → Yields g β u → Yields g α w →
      Yields g (Sum.inl A :: α) (u ++ w)

/-- Язык грамматики. -/
def Grammar.language (g : Grammar N T) : Set (List T) :=
  {w | Yields g [Sum.inl g.start] w}

/-- Вывод склеивается: конкатенация форм порождает конкатенацию слов. -/
theorem Yields.append {g : Grammar N T} :
    ∀ {β α : List (N ⊕ T)} {u v : List T},
      Yields g β u → Yields g α v → Yields g (β ++ α) (u ++ v) := by
  intro β α u v hβ hα
  induction hβ with
  | nil => simpa using hα
  | term _ ih => simpa using Yields.term (ih)
  | nonterm hr _ _ ih₁ ih₂ =>
      have := Yields.nonterm hr ‹_› (ih₂)
      simpa [List.append_assoc] using this

/-- Вывод расщепляется: если конкатенация форм порождает слово, то слово
разбивается на соответствующие куски. -/
theorem Yields.split {g : Grammar N T} :
    ∀ (β α : List (N ⊕ T)) (w : List T), Yields g (β ++ α) w →
      ∃ u v, w = u ++ v ∧ Yields g β u ∧ Yields g α v := by
  intro β
  induction β with
  | nil => intro α w h; exact ⟨[], w, rfl, Yields.nil, h⟩
  | cons x β ih =>
      intro α w h
      cases x with
      | inr a =>
          cases h with
          | term hw =>
              obtain ⟨u, v, rfl, h₁, h₂⟩ := ih α _ hw
              exact ⟨a :: u, v, rfl, Yields.term h₁, h₂⟩
      | inl A =>
          cases h with
          | nonterm hr hβ hrest =>
              rename_i δ u₁ w₁
              obtain ⟨u, v, rfl, h₁, h₂⟩ := ih α w₁ hrest
              refine ⟨u₁ ++ u, v, ?_, Yields.nonterm hr hβ h₁, h₂⟩
              simp

/-! ## Автомат с магазинной памятью (одно состояние, допуск по пустому магазину) -/

/-- Автомат с магазинной памятью: переходы, читающие символ входа, и
ε-переходы; начальное содержимое магазина. -/
structure PDA (Γ T : Type u) where
  /-- `read Z a γ`: сняв `Z` с вершины и прочитав `a`, положить `γ`. -/
  read : Γ → T → List Γ → Prop
  /-- `eps Z γ`: сняв `Z` с вершины, положить `γ`, не читая входа. -/
  eps : Γ → List Γ → Prop
  /-- Начальное содержимое магазина. -/
  initStack : List Γ

/-- Конфигурация: магазин и непрочитанный вход. -/
abbrev Config (Γ T : Type u) := List Γ × List T

/-- Шаг автомата. -/
inductive PStep (M : PDA Γ T) : Config Γ T → Config Γ T → Prop
  /-- Переход с чтением входного символа. -/
  | read {Z : Γ} {a : T} {γ σ : List Γ} {w : List T} :
      M.read Z a γ → PStep M (Z :: σ, a :: w) (γ ++ σ, w)
  /-- ε-переход. -/
  | eps {Z : Γ} {γ σ : List Γ} {w : List T} :
      M.eps Z γ → PStep M (Z :: σ, w) (γ ++ σ, w)

/-- Достижимость конфигураций. -/
def Reach (M : PDA Γ T) : Config Γ T → Config Γ T → Prop :=
  Relation.ReflTransGen (PStep M)

/-- Автомат допускает слово, если из начальной конфигурации достижима
конфигурация с пустым магазином и прочитанным до конца входом. -/
def PDA.accepts (M : PDA Γ T) (w : List T) : Prop :=
  Reach M (M.initStack, w) ([], [])

/-- Язык автомата. -/
def PDA.language (M : PDA Γ T) : Set (List T) := {w | M.accepts w}

/-- Из пустого магазина шагов нет. -/
theorem no_step_of_empty_stack (M : PDA Γ T) {w : List T} {c : Config Γ T} :
    ¬ PStep M ([], w) c := by
  intro h; cases h

/-- Из пустого магазина достижима только та же конфигурация. -/
theorem reach_empty_stack (M : PDA Γ T) {w : List T} {c : Config Γ T}
    (h : Reach M ([], w) c) : c = ([], w) := by
  rcases Relation.ReflTransGen.cases_head h with h' | ⟨d, hstep, -⟩
  · exact h'.symm
  · exact absurd hstep (no_step_of_empty_stack M)

/-- **Frame-свойство шага.**  Шаг не зависит от того, что лежит под
использованной частью магазина и после прочитанной части входа. -/
theorem pstep_frame (M : PDA Γ T) {c d : Config Γ T} (h : PStep M c d)
    (τ : List Γ) (v : List T) :
    PStep M (c.1 ++ τ, c.2 ++ v) (d.1 ++ τ, d.2 ++ v) := by
  cases h with
  | @read Z a γ σ w hr =>
      have := PStep.read (M := M) (σ := σ ++ τ) (w := w ++ v) hr
      simpa [List.append_assoc] using this
  | @eps Z γ σ w he =>
      have := PStep.eps (M := M) (σ := σ ++ τ) (w := w ++ v) he
      simpa [List.append_assoc] using this

/-- Frame-свойство достижимости. -/
theorem reach_frame (M : PDA Γ T) {σ : List Γ} {u : List T}
    (h : Reach M (σ, u) ([], [])) (τ : List Γ) (v : List T) :
    Reach M (σ ++ τ, u ++ v) (τ, v) := by
  have := Relation.ReflTransGen.lift
    (r := PStep M) (p := PStep M)
    (f := fun c : Config Γ T => (c.1 ++ τ, c.2 ++ v))
    (fun a b hab => pstep_frame M hab τ v) h
  simpa using this

/-- Композиция: два принятых куска склеиваются в один. -/
theorem reach_comp (M : PDA Γ T) {σ τ : List Γ} {u v : List T}
    (h₁ : Reach M (σ, u) ([], [])) (h₂ : Reach M (τ, v) ([], [])) :
    Reach M (σ ++ τ, u ++ v) ([], []) :=
  Relation.ReflTransGen.trans (reach_frame M h₁ τ v) h₂

/-! ## CFG → PDA: нисходящий автомат грамматики -/

/-- Нисходящий автомат грамматики: магазин хранит сентенциальную форму,
нетерминал раскрывается ε-переходом, терминал снимается чтением входа. -/
def Grammar.toPDA (g : Grammar N T) : PDA (N ⊕ T) T where
  read Z a γ := Z = Sum.inr a ∧ γ = []
  eps Z γ := ∃ A : N, Z = Sum.inl A ∧ g.rule A γ
  initStack := [Sum.inl g.start]

/-- Достижимость пустой конфигурации влечёт вывод (формулировка по
конфигурации: индукция идёт по переменной-конфигурации). -/
theorem yields_of_reach_config (g : Grammar N T) {c : Config (N ⊕ T) T}
    (h : Reach g.toPDA c ([], [])) : Yields g c.1 c.2 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Yields.nil
  | head hstep _ ih =>
      cases hstep with
      | @read Z a γ σ w hr =>
          obtain ⟨rfl, rfl⟩ := hr
          exact Yields.term (by simpa using ih)
      | @eps Z γ σ w he =>
          obtain ⟨A, rfl, hrule⟩ := he
          obtain ⟨u, v, hw, h₁, h₂⟩ := Yields.split γ σ w (by simpa using ih)
          simpa [hw] using Yields.nonterm hrule h₁ h₂

/-- Ключевая лемма: магазин `α` доводится автоматом до пустого ровно на тех
словах, которые выводятся из сентенциальной формы `α`. -/
theorem yields_iff_reach (g : Grammar N T) (α : List (N ⊕ T)) (w : List T) :
    Yields g α w ↔ Reach g.toPDA (α, w) ([], []) := by
  constructor
  · intro h
    induction h with
    | nil => exact Relation.ReflTransGen.refl
    | @term a α w _ ih =>
        refine Relation.ReflTransGen.head ?_ ih
        have := PStep.read (M := g.toPDA) (Z := Sum.inr a) (a := a) (γ := [])
          (σ := α) (w := w) ⟨rfl, rfl⟩
        simpa using this
    | @nonterm A β α u w hr _ _ ih₁ ih₂ =>
        refine Relation.ReflTransGen.head ?_ (reach_comp g.toPDA ih₁ ih₂)
        exact PStep.eps (M := g.toPDA) (Z := Sum.inl A) (γ := β) (σ := α)
          (w := u ++ w) ⟨A, rfl, hr⟩
  · intro h
    exact yields_of_reach_config g (c := (α, w)) h

/-- **Каждый контекстно-свободный язык распознаётся автоматом с магазинной
памятью.** -/
theorem pda_language_toPDA (g : Grammar N T) : g.toPDA.language = g.language := by
  ext w
  simp only [PDA.language, Set.mem_setOf_eq, PDA.accepts, Grammar.language,
    Grammar.toPDA]
  exact (yields_iff_reach g [Sum.inl g.start] w).symm

/-! ## PDA → CFG -/

/-- Грамматика автомата: нетерминалы — символы магазина плюс свежий старт. -/
def PDA.toGrammar (M : PDA Γ T) : Grammar (Option Γ) T where
  rule A β :=
    match A with
    | none => β = M.initStack.map (fun Z => Sum.inl (some Z))
    | some Z =>
        (∃ (a : T) (γ : List Γ), M.read Z a γ ∧
            β = Sum.inr a :: γ.map (fun Y => Sum.inl (some Y))) ∨
        (∃ γ : List Γ, M.eps Z γ ∧ β = γ.map (fun Y => Sum.inl (some Y)))
  start := none

/-- Кодирование магазина сентенциальной формой. -/
def stackForm (σ : List Γ) : List (Option Γ ⊕ T) :=
  σ.map (fun Z => Sum.inl (some Z))

@[simp] theorem stackForm_nil : stackForm ([] : List Γ) = ([] : List (Option Γ ⊕ T)) := rfl

@[simp] theorem stackForm_cons (Z : Γ) (σ : List Γ) :
    stackForm (Z :: σ) = (Sum.inl (some Z) : Option Γ ⊕ T) :: stackForm σ := rfl

theorem stackForm_append (σ τ : List Γ) :
    stackForm (σ ++ τ) = (stackForm σ ++ stackForm τ : List (Option Γ ⊕ T)) := by
  simp [stackForm]

/-- Вывод из закодированного магазина влечёт допуск автоматом (с точностью до
уже прочитанного терминального префикса формы). -/
theorem reach_of_yields_stackForm (M : PDA Γ T) :
    ∀ (form : List (Option Γ ⊕ T)) (w : List T), Yields M.toGrammar form w →
      ∀ (pre : List T) (σ : List Γ), form = pre.map Sum.inr ++ stackForm σ →
        ∃ w', w = pre ++ w' ∧ Reach M (σ, w') ([], []) := by
  intro form w h
  induction h with
  | nil =>
      intro pre σ hform
      cases pre with
      | cons a p => simp at hform
      | nil =>
          cases σ with
          | cons Z s => simp [stackForm] at hform
          | nil => exact ⟨[], rfl, Relation.ReflTransGen.refl⟩
  | @term a α w _ ih =>
      intro pre σ hform
      cases pre with
      | nil =>
          exfalso
          cases σ with
          | nil => simp [stackForm] at hform
          | cons Z s => simp [stackForm] at hform
      | cons b p =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at hform
          obtain ⟨hab, hrest⟩ := hform
          have hba : a = b := Sum.inr_injective hab
          subst hba
          obtain ⟨w', hw', hreach⟩ := ih p σ hrest
          exact ⟨w', by simp [hw'], hreach⟩
  | @nonterm A β α u w hr _ _ ih₁ ih₂ =>
      intro pre σ hform
      cases pre with
      | cons b p => simp at hform
      | nil =>
          cases σ with
          | nil => simp [stackForm] at hform
          | cons Z s =>
              simp only [List.map_nil, List.nil_append, stackForm_cons,
                List.cons.injEq] at hform
              obtain ⟨hA, hα⟩ := hform
              have hA' : A = some Z := by
                simpa using (Sum.inl_injective hA : A = some Z)
              subst hA'
              obtain ⟨w₂, hw₂, hreach₂⟩ := ih₂ [] s (by simpa using hα)
              simp only [List.nil_append] at hw₂
              subst hw₂
              rcases hr with ⟨a, γ, hread, rfl⟩ | ⟨γ, heps, rfl⟩
              · obtain ⟨u', hu', hreach₁⟩ := ih₁ [a] γ (by simp [stackForm])
                subst hu'
                refine ⟨(a :: u') ++ w, rfl, ?_⟩
                refine Relation.ReflTransGen.head ?_ (reach_comp M hreach₁ hreach₂)
                have := PStep.read (M := M) (Z := Z) (a := a) (γ := γ) (σ := s)
                  (w := u' ++ w) hread
                simpa using this
              · obtain ⟨u', hu', hreach₁⟩ := ih₁ [] γ (by simp [stackForm])
                simp only [List.nil_append] at hu'
                have hreach₁' : Reach M (γ, u) ([], []) := by rw [hu']; exact hreach₁
                refine ⟨u ++ w, rfl, ?_⟩
                refine Relation.ReflTransGen.head ?_ (reach_comp M hreach₁' hreach₂)
                exact PStep.eps (M := M) (Z := Z) (γ := γ) (σ := s) (w := u ++ w) heps

/-- Допуск автоматом влечёт вывод в его грамматике. -/
theorem yields_stackForm_of_reach_config (M : PDA Γ T) {c : Config Γ T}
    (h : Reach M c ([], [])) : Yields M.toGrammar (stackForm c.1) c.2 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Yields.nil
  | head hstep _ ih =>
      cases hstep with
      | @read Z a γ σ' w' hr =>
          rw [stackForm_append] at ih
          obtain ⟨u, v, rfl, h₁, h₂⟩ := Yields.split (stackForm γ) (stackForm σ') _ ih
          have hrule : (M.toGrammar).rule (some Z)
              (Sum.inr a :: stackForm γ) := Or.inl ⟨a, γ, hr, rfl⟩
          have : Yields M.toGrammar (Sum.inr a :: stackForm γ) (a :: u) :=
            Yields.term h₁
          simpa using Yields.nonterm hrule this h₂
      | @eps Z γ σ' w' he =>
          rw [stackForm_append] at ih
          obtain ⟨u, v, rfl, h₁, h₂⟩ := Yields.split (stackForm γ) (stackForm σ') _ ih
          have hrule : (M.toGrammar).rule (some Z) (stackForm γ) :=
            Or.inr ⟨γ, he, rfl⟩
          exact Yields.nonterm hrule h₁ h₂

/-- Допуск автоматом влечёт вывод в его грамматике. -/
theorem yields_stackForm_of_reach (M : PDA Γ T) (σ : List Γ) (w : List T)
    (h : Reach M (σ, w) ([], [])) : Yields M.toGrammar (stackForm σ) w :=
  yields_stackForm_of_reach_config M (c := (σ, w)) h

/-- Вывод из закодированного магазина равносилен допуску. -/
theorem yields_stackForm_iff_reach (M : PDA Γ T) (σ : List Γ) (w : List T) :
    Yields M.toGrammar (stackForm σ) w ↔ Reach M (σ, w) ([], []) := by
  constructor
  · intro h
    obtain ⟨w', hw', hreach⟩ := reach_of_yields_stackForm M _ w h [] σ (by simp)
    simpa [hw'] using hreach
  · exact yields_stackForm_of_reach M σ w

/-- **Каждый язык автомата с магазинной памятью контекстно-свободен.** -/
theorem grammar_language_toGrammar (M : PDA Γ T) :
    (M.toGrammar).language = M.language := by
  ext w
  simp only [Grammar.language, Set.mem_setOf_eq, PDA.language, PDA.accepts,
    PDA.toGrammar]
  constructor
  · intro h
    cases h with
    | nonterm hr hβ hrest =>
        rename_i β u v
        cases hrest with
        | nil =>
            have : β = stackForm M.initStack := hr
            subst this
            simpa using (yields_stackForm_iff_reach M M.initStack u).mp hβ
  · intro h
    have hb : Yields M.toGrammar (stackForm M.initStack) w :=
      (yields_stackForm_iff_reach M M.initStack w).mpr h
    have hr : (M.toGrammar).rule none (stackForm M.initStack) := rfl
    simpa using Yields.nonterm hr hb (Yields.nil)

/-- **CFG ≡ PDA.**  Язык контекстно-свободен тогда и только тогда, когда он
распознаётся автоматом с магазинной памятью (в рассматриваемом классе). -/
theorem contextFree_iff_pda (L : Set (List T)) :
    (∃ (N : Type u) (g : Grammar N T), g.language = L) ↔
      (∃ (Γ : Type u) (M : PDA Γ T), M.language = L) := by
  constructor
  · rintro ⟨N, g, rfl⟩
    exact ⟨N ⊕ T, g.toPDA, pda_language_toPDA g⟩
  · rintro ⟨Γ, M, rfl⟩
    exact ⟨Option Γ, M.toGrammar, grammar_language_toGrammar M⟩

/-! ## Конкретный пример: язык `aⁿbⁿ` -/

/-- Алфавит примера. -/
inductive AB
  | a | b
  deriving DecidableEq, Repr

/-- Грамматика `S → a S b | ε`. -/
def anbn : Grammar Unit AB where
  rule _ β := β = [] ∨ β = [Sum.inr AB.a, Sum.inl (), Sum.inr AB.b]
  start := ()

/-- Слово `aⁿbⁿ`. -/
def abword (n : ℕ) : List AB := List.replicate n AB.a ++ List.replicate n AB.b

/-- Грамматика выводит каждое слово `aⁿbⁿ`. -/
theorem anbn_mem (n : ℕ) : abword n ∈ anbn.language := by
  induction n with
  | zero => exact Yields.nonterm (Or.inl rfl) Yields.nil Yields.nil
  | succ n ih =>
      have hbody : Yields anbn [Sum.inr AB.a, Sum.inl (), Sum.inr AB.b]
          (AB.a :: (abword n ++ [AB.b])) := by
        refine Yields.term ?_
        have : Yields anbn [Sum.inl ()] (abword n) := ih
        simpa using Yields.append this (Yields.term (a := AB.b) Yields.nil)
      have hstep := Yields.nonterm (g := anbn) (A := ()) (α := [])
        (Or.inr rfl) hbody Yields.nil
      have hb : List.replicate n AB.b ++ [AB.b] = AB.b :: List.replicate n AB.b := by
        rw [← List.replicate_succ', List.replicate_succ]
      have heq : abword (n + 1) = (AB.a :: (abword n ++ [AB.b])) ++ [] := by
        simp [abword, List.replicate_succ, List.append_assoc, hb]
      rw [Grammar.language, Set.mem_setOf_eq, heq]
      exact hstep

/-- Слово `ba` не выводится: язык не совпадает со всеми словами. -/
theorem ba_not_mem : [AB.b, AB.a] ∉ anbn.language := by
  have key : ∀ w : List AB, w = [AB.b, AB.a] → ¬ Yields anbn [Sum.inl ()] w := by
    intro w hw hy
    cases hy with
    | nonterm hr hβ hrest =>
        rename_i β u v
        rcases hr with rfl | rfl
        · cases hβ
          cases hrest
          simp at hw
        · cases hβ with
          | term h' => simp at hw
  exact key _ rfl

end UAM.ContextFree
