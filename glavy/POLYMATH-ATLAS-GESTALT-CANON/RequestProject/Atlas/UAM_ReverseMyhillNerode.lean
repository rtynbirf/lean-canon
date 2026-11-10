import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_Congruence
import RequestProject.Atlas.UAM_Morphism
import RequestProject.Atlas.UAM_DFAEval
import RequestProject.Atlas.UAM_RegularLanguages

/-!
# UAM — Обратная теорема Майхилла–Нероуда (Reverse Myhill–Nerode)

Обратное направление теоремы Майхилла–Нероуда: если язык `L` распознаётся
детерминированным конечным автоматом (DFA) с **конечным** множеством состояний
`Q`, то синтаксический моноид языка `L` конечен.

## Идея доказательства

Гомоморфизм `phi : FreeMonoid α → (Q → Q)` отображает слово `w` в функцию
«действие на состояниях» `q ↦ evalFrom q w`. Это моноидный гомоморфизм:
единица переходит в тождество, а конкатенация — в композицию действий.

Ядро этого гомоморфизма содержится в синтаксической конгруэнции языка
(лемма `phi_eq_imp_syntacticRel`): если два слова задают одно и то же действие на
всех состояниях, то они двусторонне неразличимы по `L`. Поэтому:

* фактор-моноид `FreeMonoid α / ker(phi)` вкладывается в конечный тип `Q → Q`
  (значит, конечен при `Fintype Q`);
* существует каноническая сюръекция `FreeMonoid α / ker(phi) ↠ SyntacticMonoid L`.

Из конечности источника и сюръективности следует конечность синтаксического
моноида.

Здесь `UAM_DFAEval` импортируется **после** `UAM_RegularLanguages`, поэтому при
неквалифицированном использовании `DFA` (внутри `open UAM_DFAEval`) обозначает
`UAM_DFAEval.DFA`. Определения из `UAM_RegularLanguages` берутся с квалификатором.
-/

namespace UAM_ReverseMyhillNerode
universe u

open UAM_DFAEval

variable {α Q : Type u} [DecidableEq Q]

/-! ### §0. Моноид действий на состояниях -/

/-- Моноидная структура на функциях `Q → Q` («действиях на состояниях»):
    умножение — композиция в порядке «сначала левый сомножитель»
    (`f * g = g ∘ f`), единица — тождественная функция.

    Такой порядок нужен, чтобы конкатенация слов соответствовала
    последовательному применению действий: сначала действие первого слова,
    затем второго. -/
instance instMonoidStateEnd : Monoid (Q → Q) where
  mul f g := g ∘ f
  one := id
  mul_assoc := fun _ _ _ => rfl
  one_mul := fun _ => rfl
  mul_one := fun _ => rfl

/-! ### §1. Гомоморфизм в эндоморфизмы состояний -/

/-- Моноидный гомоморфизм: слово ↦ функция «действие на состояниях».
    `phi A w q = evalFrom q w`.
    Сохраняет единицу (`phi A [] = id`) и умножение
    (`phi A (w₁ ++ w₂) = phi A w₂ ∘ phi A w₁`). -/
def phi (A : DFA α Q) : UAM_Morphism.MonoidMorphism (UAM_Free.FreeMonoid α) (Q → Q) where
  toFun := fun w q => A.evalFrom q w
  map_mul := by
    intro w₁ w₂
    funext q
    show A.evalFrom q (w₁ ++ w₂) = A.evalFrom (A.evalFrom q w₁) w₂
    exact A.evalFrom_concat q w₁ w₂
  map_one := by
    funext q
    rfl

/-! ### §2. Ядро ⊆ синтаксическая конгруэнция -/

/-- Центральная лемма: если два слова определяют одно и то же действие на
    состояниях, то они синтаксически эквивалентны (двусторонне неразличимы
    по `L`).

    Доказательство: пусть `phi A w₁ = phi A w₂`, т.е. `∀ q, evalFrom q w₁ =
    evalFrom q w₂`. Для любых `p, v` через `eval_concat` и `evalFrom_concat`
    получаем `eval (p ++ w₁ ++ v) = eval (p ++ w₂ ++ v)`, откуда следует
    равносильность принадлежности `L`. -/
theorem phi_eq_imp_syntacticRel {L : Set (UAM_Free.FreeMonoid α)}
    (A : DFA α Q) (hL : A.language = L)
    {w₁ w₂ : UAM_Free.FreeMonoid α} (h : phi A w₁ = phi A w₂) :
    UAM_RegularLanguages.syntacticRel L w₁ w₂ := by
  subst hL
  intro p v
  -- Слова действуют одинаково на всех состояниях.
  have h_act : ∀ q, A.evalFrom q w₁ = A.evalFrom q w₂ := fun q => congrFun h q
  -- Равенство вычислений на контексте `p _ v`.
  have h_eval : A.eval (p ++ w₁ ++ v) = A.eval (p ++ w₂ ++ v) := by
    simp only [List.append_assoc]
    rw [A.eval_concat p (w₁ ++ v), A.eval_concat p (w₂ ++ v),
        A.evalFrom_concat (A.eval p) w₁ v, A.evalFrom_concat (A.eval p) w₂ v, h_act]
  -- Принадлежность языку определяется значением `eval`.
  show A.accepts (p ++ w₁ ++ v) = A.accepts (p ++ w₂ ++ v)
  unfold DFA.accepts
  rw [h_eval]

/-! ### §3. Вложение фактор-моноида по ядру в `Q → Q` -/

/-- Вложение `QuotientMonoid (kernel phi) ↪ (Q → Q)`.
    Каждый класс ядра (слова с одинаковым действием) однозначно определяет
    функцию `Q → Q`. -/
def kerInjection (A : DFA α Q) :
    UAM_Congruence.QuotientMonoid (phi A).kernel → (Q → Q) :=
  Quotient.lift (s := UAM_Congruence.congruenceSetoid (phi A).kernel)
    (phi A).toFun
    (by
      intro a b hab
      exact UAM_Morphism.MonoidMorphism.kernel_eq_iff.mp hab)

/-- `kerInjection` инъективно: разные классы ядра дают разные функции. -/
theorem kerInjection_injective (A : DFA α Q) :
    Function.Injective (kerInjection A) := by
  intro x y h
  refine Quotient.inductionOn₂ x y
    (motive := fun x y => kerInjection A x = kerInjection A y → x = y) ?_ h
  intro a b hab
  exact Quotient.sound (UAM_Morphism.MonoidMorphism.kernel_eq_iff.mpr hab)

/-! ### §4. Конечность фактор-моноида по ядру -/

/-- Фактор свободного моноида по ядру `phi` конечен, если `Q` конечен.
    Доказательство: `kerInjection` — инъекция в `Q → Q`, а `Q → Q` конечен
    при `Fintype Q`. -/
noncomputable instance instFintypeKerQuotient (A : DFA α Q) [Fintype Q] :
    Fintype (UAM_Congruence.QuotientMonoid (phi A).kernel) :=
  Fintype.ofInjective (kerInjection A) (kerInjection_injective A)

/-! ### §5. Сюръекция из фактор-моноида по ядру в синтаксический моноид -/

/-- Сюръекция: каждый класс синтаксического моноида является образом некоторого
    класса ядра `phi`.

    Корректность определения опирается на `phi_eq_imp_syntacticRel`: конгруэнция
    ядра измельчает синтаксическую конгруэнцию, поэтому проекция на
    синтаксический моноид корректно факторизуется. -/
def syntacticSurjection {L : Set (UAM_Free.FreeMonoid α)}
    (A : DFA α Q) (hL : A.language = L) :
    UAM_Congruence.QuotientMonoid (phi A).kernel →
      UAM_RegularLanguages.SyntacticMonoid L :=
  Quotient.lift
    (s := UAM_Congruence.congruenceSetoid (phi A).kernel)
    UAM_Congruence.QuotientMonoid.mk
    (by
      intro a b hab
      exact Quotient.sound
        (phi_eq_imp_syntacticRel A hL
          (UAM_Morphism.MonoidMorphism.kernel_eq_iff.mp hab)))

/-- `syntacticSurjection` сюръективна. -/
theorem syntacticSurjection_surjective {L : Set (UAM_Free.FreeMonoid α)}
    (A : DFA α Q) (hL : A.language = L) :
    Function.Surjective (syntacticSurjection A hL) := by
  intro q
  rcases UAM_Congruence.QuotientMonoid.mk_surjective q with ⟨w, rfl⟩
  exact ⟨UAM_Congruence.QuotientMonoid.mk w, rfl⟩

/-! ### §6. Основная теорема -/

/-- Обратная теорема Майхилла–Нероуда: если язык `L` распознаётся DFA с
    конечным множеством состояний, то синтаксический моноид `L` конечен.

    Доказательство:
    1. `phi : FreeMonoid α → (Q → Q)` — моноидный гомоморфизм.
    2. `ker(phi) ⊆ syntacticRel L` (по `phi_eq_imp_syntacticRel`).
    3. `FreeMonoid α / ker(phi)` конечен (вкладывается в конечный `Q → Q`).
    4. Существует сюръекция `FreeMonoid α / ker(phi) ↠ SyntacticMonoid L`.
    5. Следовательно, `SyntacticMonoid L` конечен. -/
noncomputable def fintype_syntacticMonoid_of_dfa {L : Set (UAM_Free.FreeMonoid α)}
    (A : DFA α Q) (hL : A.language = L) [Fintype Q] :
    Fintype (UAM_RegularLanguages.SyntacticMonoid L) :=
  letI : DecidableEq (UAM_RegularLanguages.SyntacticMonoid L) := Classical.decEq _
  Fintype.ofSurjective (syntacticSurjection A hL) (syntacticSurjection_surjective A hL)

end UAM_ReverseMyhillNerode
