import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_DFAEval
import RequestProject.Atlas.UAM_NFA

/-!
# UAM — ε-NFA (Epsilon NFA)

ε-NFA обобщает NFA, добавляя переходы по пустому слову `ε` (обозначаются
`δ q none`; обычные переходы — `δ q (some a)`). Семантика задаётся расширенной
функцией переходов с ε-замыканием, а эквивалентность с обычными NFA — через
подмножественную конструкцию `toNFA`, встраивающую ε-замыкание в переходы и
множество принимающих состояний.
-/

namespace UAM_EpsilonNFA
universe u

/-- ε-NFA над алфавитом `α` с множеством состояний `Q`. -/
structure EpsilonNFA (α : Type u) (Q : Type u) [DecidableEq Q] where
  /-- Функция переходов: `none` — ε-переход, `some a` — переход по символу. -/
  δ : Q → Option α → Set Q
  /-- Начальное состояние. -/
  q₀ : Q
  /-- Множество принимающих состояний. -/
  F : Set Q

namespace EpsilonNFA
variable {α Q : Type u} [DecidableEq Q]

/-- Отношение ε-шага: `q ⟶ε q'`. -/
def epsStep (A : EpsilonNFA α Q) (q q' : Q) : Prop := q' ∈ A.δ q none

/-- ε-замыкание множества состояний: рефлексивно-транзитивное замыкание по
    ε-переходам. -/
def epsilonClosure (A : EpsilonNFA α Q) (S : Set Q) : Set Q :=
  {q' | ∃ q ∈ S, Relation.ReflTransGen A.epsStep q q'}

/-! ### §1. ε-замыкание как оператор замыкания -/

theorem subset_closure (A : EpsilonNFA α Q) (S : Set Q) :
    S ⊆ A.epsilonClosure S :=
  fun q hq => ⟨q, hq, Relation.ReflTransGen.refl⟩

theorem closure_mono (A : EpsilonNFA α Q) {S T : Set Q} (h : S ⊆ T) :
    A.epsilonClosure S ⊆ A.epsilonClosure T := by
  rintro q' ⟨q, hq, hrel⟩
  exact ⟨q, h hq, hrel⟩

theorem closure_idem (A : EpsilonNFA α Q) (S : Set Q) :
    A.epsilonClosure (A.epsilonClosure S) = A.epsilonClosure S := by
  apply Set.Subset.antisymm
  · rintro q' ⟨q, ⟨p, hp, hpq⟩, hqq'⟩
    exact ⟨p, hp, hpq.trans hqq'⟩
  · exact A.subset_closure _

theorem mem_closure_iff (A : EpsilonNFA α Q) (S : Set Q) (q' : Q) :
    q' ∈ A.epsilonClosure S ↔ ∃ q ∈ S, Relation.ReflTransGen A.epsStep q q' := Iff.rfl

/-- ε-замыкание распределяется по объединению по индексам. -/
theorem closure_iUnion {ι : Type u} (A : EpsilonNFA α Q) (f : ι → Set Q) :
    A.epsilonClosure (⋃ i, f i) = ⋃ i, A.epsilonClosure (f i) := by
  ext q'
  simp only [epsilonClosure, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, ⟨i, hqi⟩, hrel⟩; exact ⟨i, q, hqi, hrel⟩
  · rintro ⟨i, q, hqi, hrel⟩; exact ⟨q, ⟨i, hqi⟩, hrel⟩

/-! ### §2. Расширенная функция переходов ε-NFA -/

/-- Шаг по множеству состояний, читающий символ `a` (без ε-замыкания). -/
def eStepSet (A : EpsilonNFA α Q) (S : Set Q) (a : α) : Set Q :=
  ⋃ q ∈ S, A.δ q (some a)

/-- Расширенное вычисление: замыкаем, читаем символ, снова замыкаем и т.д. -/
def eEval (A : EpsilonNFA α Q) (S : Set Q) : UAM_Free.FreeMonoid α → Set Q
  | [] => A.epsilonClosure S
  | a :: w => A.eEval (A.eStepSet (A.epsilonClosure S) a) w

/-- Множество состояний, достижимых из начального по слову `w`. -/
def eReachable (A : EpsilonNFA α Q) (w : UAM_Free.FreeMonoid α) : Set Q :=
  A.eEval {A.q₀} w

/-- Слово допускается ε-NFA. -/
def eAccepts (A : EpsilonNFA α Q) (w : UAM_Free.FreeMonoid α) : Prop :=
  (A.eReachable w ∩ A.F).Nonempty

/-- Язык ε-NFA. -/
def epsilonLanguage (A : EpsilonNFA α Q) : Set (UAM_Free.FreeMonoid α) :=
  {w | A.eAccepts w}

@[simp] theorem eEval_nil (A : EpsilonNFA α Q) (S : Set Q) :
    A.eEval S [] = A.epsilonClosure S := rfl

theorem eEval_cons (A : EpsilonNFA α Q) (S : Set Q) (a : α)
    (w : UAM_Free.FreeMonoid α) :
    A.eEval S (a :: w) = A.eEval (A.eStepSet (A.epsilonClosure S) a) w := rfl

/-- Значение `eEval` всегда ε-замкнуто. -/
theorem eEval_closed (A : EpsilonNFA α Q) (S : Set Q) (w : UAM_Free.FreeMonoid α) :
    A.epsilonClosure (A.eEval S w) = A.eEval S w := by
  cases w with
  | nil => exact A.closure_idem S
  | cons a w => exact eEval_closed A (A.eStepSet (A.epsilonClosure S) a) w

/-! ### §3. Подмножественная конструкция в NFA -/

/-- Преобразование ε-NFA в NFA: ε-замыкания встроены в переходы и в множество
    принимающих состояний. -/
def toNFA (A : EpsilonNFA α Q) : UAM_NFA.NFA α Q where
  δ := fun q a => ⋃ q'' ∈ A.epsilonClosure {q}, A.epsilonClosure (A.δ q'' (some a))
  q₀ := A.q₀
  F := {q | (A.epsilonClosure {q} ∩ A.F).Nonempty}

/-- Ключевая алгебраическая лемма: NFA-шаг по ε-замкнутому множеству совпадает с
    ε-замыканием ε-шага. -/
theorem stepSet_toNFA (A : EpsilonNFA α Q) (S : Set Q) (a : α) :
    (A.toNFA).stepSet (A.epsilonClosure S) a
      = A.epsilonClosure (A.eStepSet (A.epsilonClosure S) a) := by
  ext p
  rw [UAM_NFA.NFA.mem_stepSet]
  constructor
  · rintro ⟨q, hqS, hp⟩
    change p ∈ (⋃ q'' ∈ A.epsilonClosure {q},
      A.epsilonClosure (A.δ q'' (some a))) at hp
    rw [Set.mem_iUnion₂] at hp
    obtain ⟨q'', hq'', hp''⟩ := hp
    have hq''S : q'' ∈ A.epsilonClosure S := by
      obtain ⟨s, hsS, hsq⟩ := hqS
      obtain ⟨q0, hq0, hq0q''⟩ := hq''
      rw [Set.mem_singleton_iff] at hq0
      subst hq0
      exact ⟨s, hsS, hsq.trans hq0q''⟩
    obtain ⟨r, hr, hrp⟩ := hp''
    exact ⟨r, Set.mem_iUnion₂.mpr ⟨q'', hq''S, hr⟩, hrp⟩
  · rintro ⟨r, hr, hrp⟩
    rw [EpsilonNFA.eStepSet, Set.mem_iUnion₂] at hr
    obtain ⟨q, hqS, hrq⟩ := hr
    refine ⟨q, hqS, ?_⟩
    change p ∈ (⋃ q'' ∈ A.epsilonClosure {q},
      A.epsilonClosure (A.δ q'' (some a)))
    exact Set.mem_iUnion₂.mpr
      ⟨q, A.subset_closure _ (Set.mem_singleton q), ⟨r, hrq, hrp⟩⟩

/-- Мостовая лемма: NFA-вычисление из ε-замыкания совпадает с ε-вычислением. -/
theorem evalSet_toNFA (A : EpsilonNFA α Q) (S : Set Q) (w : UAM_Free.FreeMonoid α) :
    (A.toNFA).evalSet (A.epsilonClosure S) w = A.eEval S w := by
  induction w generalizing S with
  | nil => rfl
  | cons a w ih =>
    rw [UAM_NFA.NFA.evalSet_cons, stepSet_toNFA, ih]
    rfl

/-- Соответствие принимающих множеств на ε-замкнутых множествах. -/
theorem accept_iff_of_closed (A : EpsilonNFA α Q) {T : Set Q}
    (hT : A.epsilonClosure T = T) :
    (T ∩ (A.toNFA).F).Nonempty ↔ (T ∩ A.F).Nonempty := by
  constructor
  · rintro ⟨q, hqT, hqF⟩
    obtain ⟨p, hpcl, hpF⟩ := hqF
    have hsub : A.epsilonClosure {q} ⊆ T := by
      have hmono := A.closure_mono (Set.singleton_subset_iff.mpr hqT)
      rwa [hT] at hmono
    exact ⟨p, hsub hpcl, hpF⟩
  · rintro ⟨p, hpT, hpF⟩
    exact ⟨p, hpT, ⟨p, A.subset_closure _ (Set.mem_singleton p), hpF⟩⟩

/-- Шаг NFA из одного состояния совпадает с шагом из его ε-замыкания
    (т.к. ε-замыкание уже встроено в переходы `toNFA`). -/
theorem stepSet_singleton (A : EpsilonNFA α Q) (q : Q) (a : α) :
    (A.toNFA).stepSet {q} a = (A.toNFA).stepSet (A.epsilonClosure {q}) a := by
  ext p
  rw [UAM_NFA.NFA.mem_stepSet, UAM_NFA.NFA.mem_stepSet]
  constructor
  · rintro ⟨q', hq', hp⟩
    rw [Set.mem_singleton_iff] at hq'
    subst hq'
    exact ⟨q', A.subset_closure _ (Set.mem_singleton q'), hp⟩
  · rintro ⟨q', hq', hp⟩
    change p ∈ (⋃ q'' ∈ A.epsilonClosure {q'},
      A.epsilonClosure (A.δ q'' (some a))) at hp
    rw [Set.mem_iUnion₂] at hp
    obtain ⟨q'', hq'', hp''⟩ := hp
    have hq''q : q'' ∈ A.epsilonClosure {q} := by
      obtain ⟨s, hs, hsq'⟩ := hq'
      obtain ⟨t, ht, htq''⟩ := hq''
      rw [Set.mem_singleton_iff] at hs ht
      subst hs
      subst ht
      exact ⟨s, Set.mem_singleton s, hsq'.trans htq''⟩
    refine ⟨q, Set.mem_singleton q, ?_⟩
    change p ∈ (⋃ q'' ∈ A.epsilonClosure {q},
      A.epsilonClosure (A.δ q'' (some a)))
    exact Set.mem_iUnion₂.mpr ⟨q'', hq''q, hp''⟩

/-- **Эквивалентность ε-NFA и NFA:** язык подмножественной конструкции совпадает
    с языком исходного ε-NFA. -/
theorem epsilonLanguage_eq_nfa_language (A : EpsilonNFA α Q) :
    (A.toNFA).nfaLanguage = A.epsilonLanguage := by
  ext w
  show ((A.toNFA).reachable w ∩ (A.toNFA).F).Nonempty ↔ (A.eReachable w ∩ A.F).Nonempty
  cases w with
  | nil =>
    show (({A.q₀} : Set Q) ∩ (A.toNFA).F).Nonempty ↔
        (A.epsilonClosure {A.q₀} ∩ A.F).Nonempty
    constructor
    · rintro ⟨q, hq, hqF⟩
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hqF
    · intro h
      exact ⟨A.q₀, Set.mem_singleton _, h⟩
  | cons a w =>
    have hrw : (A.toNFA).reachable (a :: w) = A.eReachable (a :: w) := by
      show (A.toNFA).evalSet {A.q₀} (a :: w) = A.eEval {A.q₀} (a :: w)
      rw [UAM_NFA.NFA.evalSet_cons, stepSet_singleton, stepSet_toNFA, evalSet_toNFA]
      rfl
    rw [hrw]
    exact accept_iff_of_closed A (A.eEval_closed {A.q₀} (a :: w))

end EpsilonNFA
end UAM_EpsilonNFA