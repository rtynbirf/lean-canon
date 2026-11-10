import Mathlib.Tactic
import RequestProject.Atlas.UAM_MinimalUnique

/-!
# Теорема Майхилла–Нероуда: отношение неразличимости и его свойства

Этот модуль даёт «пользовательский» слой теоремы Майхилла–Нероуда поверх уже
формализованной в `RequestProject.Atlas` теории автоматов:

* `MyhillNerodeEquiv L x y` — неразличимость слов `x` и `y` относительно языка
  `L` (эквивалентность по всем правым продолжениям);
* рефлексивность, симметричность, транзитивность и соответствующий `Setoid`;
* **правая** конгруэнция по приписыванию буквы и формальное опровержение
  «левого» варианта конгруэнции (приписывание буквы слева), который в общем
  случае неверен;
* связь с DFA: равенство состояний влечёт неразличимость (и контрпример к
  обратному утверждению для произвольного DFA);
* конечность индекса `≈_L` для DFA с конечным множеством состояний;
* основная теорема: конечность индекса `≈_L` равносильна распознаваемости `L`
  конечным DFA;
* единственность минимального (приведённого) DFA с точностью до изоморфизма.

Все типы (`DFA`, слова `UAM_Free.FreeMonoid α = List α`) взяты из существующих
модулей `RequestProject.Atlas.UAM_DFAEval`, `…UAM_MyhillNerode`,
`…UAM_MinimalUnique`; ничего не переопределяется заново.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_Ring

open UAM_DFAEval UAM_MyhillNerode UAM_MinimalUnique

universe u

variable {α Q Q₁ Q₂ : Type u}

/-! ### §1. Отношение неразличимости -/

/-- Отношение неразличимости Майхилла–Нероуда: слова `x` и `y` неразличимы
    относительно языка `L`, если ни одно правое продолжение не отличает их. -/
def MyhillNerodeEquiv (L : Set (List α)) (x y : List α) : Prop :=
  ∀ w : List α, (x ++ w) ∈ L ↔ (y ++ w) ∈ L

@[inherit_doc MyhillNerodeEquiv]
notation:50 x " ≈[" L "] " y => MyhillNerodeEquiv L x y

/-- Рефлексивность отношения неразличимости. -/
theorem myhill_nerode_refl (L : Set (List α)) (x : List α) :
    MyhillNerodeEquiv L x x := fun _ => Iff.rfl

/-- Симметричность отношения неразличимости. -/
theorem myhill_nerode_symm {L : Set (List α)} {x y : List α}
    (h : MyhillNerodeEquiv L x y) : MyhillNerodeEquiv L y x :=
  fun w => (h w).symm

/-- Транзитивность отношения неразличимости. -/
theorem myhill_nerode_trans {L : Set (List α)} {x y z : List α}
    (h₁ : MyhillNerodeEquiv L x y) (h₂ : MyhillNerodeEquiv L y z) :
    MyhillNerodeEquiv L x z :=
  fun w => (h₁ w).trans (h₂ w)

/-- Неразличимость — отношение эквивалентности. -/
theorem myhill_nerode_equivalence (L : Set (List α)) :
    Equivalence (MyhillNerodeEquiv L) :=
  ⟨myhill_nerode_refl L, myhill_nerode_symm, myhill_nerode_trans⟩

/-- Сетоид неразличимости языка `L`. -/
def myhillNerodeSetoid (L : Set (List α)) : Setoid (List α) :=
  ⟨MyhillNerodeEquiv L, myhill_nerode_equivalence L⟩

/-- Тип классов неразличимости языка `L` (состояния канонического DFA). -/
abbrev MyhillNerodeQuot (L : Set (List α)) := Quotient (myhillNerodeSetoid L)

/-- Неразличимость совпадает с уже формализованным правым Nerode-отношением
    (последнее записано через равенство пропозиций, а не через `↔`). -/
theorem myhillNerodeEquiv_iff_nerodeRel (L : Set (List α)) (x y : List α) :
    MyhillNerodeEquiv L x y ↔ UAM_RegularLanguages.nerodeRel L x y :=
  ⟨fun h w => propext (h w), fun h w => Iff.of_eq (h w)⟩

/-! ### §2. Конгруэнция -/

/-- **Правая конгруэнция.** Неразличимость сохраняется при приписывании буквы
    справа. Именно это свойство делает корректным переход канонического
    автомата `δ([x], a) = [x ++ [a]]`. -/
theorem myhill_nerode_congr {L : Set (List α)} {x y : List α}
    (h : MyhillNerodeEquiv L x y) (a : α) :
    MyhillNerodeEquiv L (x ++ [a]) (y ++ [a]) := by
  intro w
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using h (a :: w)

/-- Правая конгруэнция для произвольного слова, а не только для одной буквы. -/
theorem myhill_nerode_congr_append {L : Set (List α)} {x y : List α}
    (h : MyhillNerodeEquiv L x y) (v : List α) :
    MyhillNerodeEquiv L (x ++ v) (y ++ v) := by
  intro w
  simpa only [List.append_assoc] using h (v ++ w)

/-- Язык-контрпример к «левой» конгруэнции: `{[false, false], [true, false]}`. -/
def congrCounterLanguage : Set (List Bool) :=
  {w | w = [false, false] ∨ w = [true, false]}

/-- В языке-контрпримере слова `[false]` и `[true]` неразличимы. -/
theorem congrCounter_equiv :
    MyhillNerodeEquiv congrCounterLanguage [false] [true] := by
  intro w
  simp [congrCounterLanguage]

/-- Но после приписывания буквы `false` **слева** они различимы. -/
theorem congrCounter_not_equiv :
    ¬ MyhillNerodeEquiv congrCounterLanguage (false :: [false]) (false :: [true]) := by
  intro h
  have hmem : ([false, false] ++ ([] : List Bool)) ∈ congrCounterLanguage := by
    simp [congrCounterLanguage]
  have := (h []).mp hmem
  simp [congrCounterLanguage] at this

/-- **Левая конгруэнция неверна.** Утверждение «`x ≈_L y → (a :: x) ≈_L (a :: y)`»
    ложно: приписывание буквы слева меняет левый контекст, а отношение
    Майхилла–Нероуда учитывает только правые контексты. Свидетель —
    `congrCounterLanguage`. -/
theorem not_myhill_nerode_cons_congr :
    ¬ ∀ (β : Type) (L : Set (List β)) (x y : List β),
        MyhillNerodeEquiv L x y → ∀ a : β, MyhillNerodeEquiv L (a :: x) (a :: y) := by
  intro hcongr
  exact congrCounter_not_equiv
    (hcongr Bool congrCounterLanguage [false] [true] congrCounter_equiv false)

/-! ### §3. Связь с DFA -/

variable [DecidableEq Q] [DecidableEq Q₁] [DecidableEq Q₂]

/-- Язык, распознаваемый DFA. -/
def DFALanguage (M : DFA α Q) : Set (List α) := {w | M.accepts w}

/-- `DFALanguage` — это в точности `DFA.language`. -/
theorem dfaLanguage_eq (M : DFA α Q) : DFALanguage M = M.language := rfl

/-- Если два слова приводят автомат в одно и то же состояние, то любые
    продолжения обрабатываются одинаково. -/
theorem dfa_evalFrom_eq_of_eval_eq (M : DFA α Q) {x y : List α}
    (h : M.eval x = M.eval y) (w : List α) :
    M.evalFrom (M.eval x) w = M.evalFrom (M.eval y) w := by
  rw [h]

/-- **DFA согласован с отношением Майхилла–Нероуда.** Если после чтения `x` и
    после чтения `y` автомат оказывается в одном состоянии, то `x` и `y`
    неразличимы относительно языка автомата. -/
theorem dfa_respects_myhill_nerode (M : DFA α Q) {x y : List α}
    (h : M.eval x = M.eval y) : MyhillNerodeEquiv (DFALanguage M) x y := by
  intro w
  exact Iff.of_eq (UAM_RegularLanguages.DFA.dfa_nerode_of_eval_eq M x y h w)

/-- DFA с двумя эквивалентными (но различными) состояниями. -/
def twoStateDFA : DFA Unit Bool where
  δ := fun _ _ => true
  q₀ := false
  F := Set.univ

/-- **Обратное к `dfa_respects_myhill_nerode` неверно** для произвольного DFA:
    неразличимые слова могут вести в разные состояния. Приведённость автомата
    (см. `IsStateReduced`) — необходимое условие обратного утверждения. -/
theorem twoStateDFA_not_reflects_myhill_nerode :
    MyhillNerodeEquiv (DFALanguage twoStateDFA) [] [()] ∧
      twoStateDFA.eval [] ≠ twoStateDFA.eval [()] := by
  constructor
  · intro w
    simp [DFALanguage, DFA.accepts, twoStateDFA]
  · simp [DFA.eval, DFA.evalFrom, twoStateDFA]

/-! ### §4. Конечность индекса -/

/-- Классы неразличимости совпадают с уже построенными Nerode-классами. -/
def myhillNerodeQuotEquiv (L : Set (List α)) :
    MyhillNerodeQuot L ≃ NerodeClass L :=
  Quotient.congr (Equiv.refl _) (fun x y => myhillNerodeEquiv_iff_nerodeRel L x y)

/-- Конечный DFA даёт конечный индекс отношения неразличимости своего языка. -/
noncomputable def fintypeMyhillNerodeQuot (L : Set (List α)) [Fintype Q]
    (M : DFA α Q) (hL : DFALanguage M = L) : Fintype (MyhillNerodeQuot L) :=
  letI : Fintype (NerodeClass L) := fintypeNerodeClassOfDFA L M hL
  Fintype.ofEquiv (NerodeClass L) (myhillNerodeQuotEquiv L).symm

/-- **Конечный индекс.** Индекс отношения неразличимости языка, распознаваемого
    DFA с `n` состояниями, не превосходит `n`. -/
theorem dfa_finite_index (L : Set (List α)) [Fintype Q] (M : DFA α Q)
    (hL : DFALanguage M = L) [Fintype (MyhillNerodeQuot L)] :
    Fintype.card (MyhillNerodeQuot L) ≤ Fintype.card Q := by
  letI : Fintype (NerodeClass L) :=
    Fintype.ofEquiv (MyhillNerodeQuot L) (myhillNerodeQuotEquiv L)
  rw [Fintype.card_congr (myhillNerodeQuotEquiv L)]
  exact canonicalDFA_card_le L M hL

/-! ### §5. Основная теорема -/

/-- **Теорема Майхилла–Нероуда.** Индекс отношения неразличимости языка `L`
    конечен тогда и только тогда, когда `L` распознаётся конечным DFA.

    Направление «⇐» — это `dfa_finite_index`/`fintypeMyhillNerodeQuot`;
    направление «⇒» реализуется каноническим автоматом, состояниями которого
    служат сами классы неразличимости, с переходом `δ([x], a) = [x ++ [a]]`
    (корректность перехода — правая конгруэнция `myhill_nerode_congr`). -/
theorem myhill_nerode_finite_iff_regular (L : Set (List α)) :
    Nonempty (Fintype (MyhillNerodeQuot L)) ↔
      ∃ (Q : Type u) (_ : Fintype Q) (_ : DecidableEq Q) (M : DFA α Q),
        DFALanguage M = L := by
  constructor
  · rintro ⟨hfin⟩
    letI : Fintype (MyhillNerodeQuot L) := hfin
    letI : Fintype (NerodeClass L) :=
      Fintype.ofEquiv (MyhillNerodeQuot L) (myhillNerodeQuotEquiv L)
    exact (recognizable_iff_finite_nerode L).mpr ⟨inferInstance⟩
  · rintro ⟨Q', hQ', dQ', M, hL⟩
    letI : Fintype Q' := hQ'
    letI : DecidableEq Q' := dQ'
    exact ⟨fintypeMyhillNerodeQuot L M hL⟩

/-! ### §6. Единственность минимального DFA -/

/-- **Единственность минимального DFA.** Любые два приведённых (достижимых и
    различимых по состояниям) DFA, распознающих один и тот же язык,
    изоморфны — то есть отличаются лишь переименованием состояний. -/
noncomputable def minimal_dfa_unique_up_to_iso (M₁ : DFA α Q₁) (M₂ : DFA α Q₂)
    (h₁ : IsReduced M₁) (h₂ : IsReduced M₂)
    (hL : DFALanguage M₁ = DFALanguage M₂) : DFAIso M₁ M₂ :=
  reducedDFA_unique M₁ M₂ h₁ h₂ hL

/-- Изоморфные минимальные DFA имеют одинаковое число состояний. -/
theorem minimal_dfa_card_eq (M₁ : DFA α Q₁) (M₂ : DFA α Q₂)
    [Fintype Q₁] [Fintype Q₂] (h₁ : IsReduced M₁) (h₂ : IsReduced M₂)
    (hL : DFALanguage M₁ = DFALanguage M₂) :
    Fintype.card Q₁ = Fintype.card Q₂ :=
  Fintype.card_congr (minimal_dfa_unique_up_to_iso M₁ M₂ h₁ h₂ hL).toEquiv

end UAM_Ring
