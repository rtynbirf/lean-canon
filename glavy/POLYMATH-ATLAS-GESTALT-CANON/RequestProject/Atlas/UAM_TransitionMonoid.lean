import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_Congruence
import RequestProject.Atlas.UAM_Morphism
import RequestProject.Atlas.UAM_Submonoid
import RequestProject.Atlas.UAM_DFAEval
import RequestProject.Atlas.UAM_Action

/-!
# UAM — Layer (Application): Моноид переходов DFA (Transition Monoid)

Каждому DFA сопоставляется гомоморфизм из свободного моноида в моноид
преобразований множества состояний `Q → Q` (с порядком композиции из
`UAM_Action`): слово `w` действует как функция `q ↦ evalFrom q w`.

**Моноид переходов** — образ этого гомоморфизма, оформленный как подмоноид
Mathlib `Submonoid (Q → Q)`. Если множество состояний конечно, то фактор
свободного моноида по ядру этого действия (то есть моноид переходов) конечен.

**Замечание об инстанциях.** Здесь `Q` — произвольный тип состояний (не моноид),
поэтому поточечная структура `Pi.monoid` на `Q → Q` не синтезируется, и
единственной моноидной структурой на `Q → Q` является `UAM_Action.instMonoid`.
-/

namespace UAM_TransitionMonoid
universe u

open UAM_DFAEval UAM_Action UAM_Morphism UAM_Congruence

variable {α Q : Type u} [DecidableEq Q]

/-- Действие DFA на состояниях как моноидный морфизм из свободного моноида в
    моноид преобразований `Q → Q`. Слово `w` отображается в функцию
    `q ↦ evalFrom q w`. -/
def actionHom (A : DFA α Q) :
    MonoidMorphism (UAM_Free.FreeMonoid α) (Q → Q) where
  toFun := fun w q => A.evalFrom q w
  map_mul := by
    intro w1 w2
    funext q
    show A.evalFrom q (w1 ++ w2) = A.evalFrom (A.evalFrom q w1) w2
    exact A.evalFrom_concat q w1 w2
  map_one := by
    funext q
    rfl

@[simp] theorem actionHom_apply (A : DFA α Q) (w : UAM_Free.FreeMonoid α) (q : Q) :
    (actionHom A).toFun w q = A.evalFrom q w := rfl

/-- Моноид переходов DFA `A`: образ действия как подмоноид `Q → Q`. -/
def TransitionMonoid (A : DFA α Q) : UAM_Submonoid.Submonoid (Q → Q) where
  carrier := Set.range (actionHom A).toFun
  one_mem := ⟨1, (actionHom A).map_one⟩
  mul_mem := by
    rintro a b ⟨w1, rfl⟩ ⟨w2, rfl⟩
    exact ⟨w1 ++ w2, (actionHom A).map_mul w1 w2⟩

/-- Отношение ядра действия совпадает с поточечным равенством действий слов. -/
theorem actionHom_eq_iff (A : DFA α Q) (w1 w2 : UAM_Free.FreeMonoid α) :
    (actionHom A).kernel.r w1 w2 ↔ ∀ q, A.evalFrom q w1 = A.evalFrom q w2 := by
  constructor
  · intro h q; exact congrFun h q
  · intro h; funext q; exact h q

/-- Инъекция фактора свободного моноида по ядру действия в моноид
    преобразований `Q → Q`. -/
def kerInjection (A : DFA α Q) :
    QuotientMonoid (actionHom A).kernel → (Q → Q) :=
  Quotient.lift (actionHom A).toFun (fun _ _ h => h)

/-- Инъекция ядра действительно инъективна. -/
theorem kerInjection_injective (A : DFA α Q) :
    Function.Injective (kerInjection A) := by
  intro x y h
  refine Quotient.inductionOn₂ x y ?_ h
  intro a b hab
  exact QuotientMonoid.mk_eq_iff.mpr hab

/-- Если множество состояний конечно, то фактор свободного моноида по ядру
    действия (моноид переходов) конечен. -/
noncomputable instance instFintypeKerQuotient (A : DFA α Q) [Fintype Q] :
    Fintype (QuotientMonoid (actionHom A).kernel) :=
  Fintype.ofInjective (kerInjection A) (kerInjection_injective A)

end UAM_TransitionMonoid
