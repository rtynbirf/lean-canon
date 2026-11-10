import Mathlib

/-!
# UAM_Equivalence: «Эквивалентность путей»

Этот файл формализует понятие **эквивалентности путей** для проекта
UAM (Universal Algebra of Models).

Идея диаграммы:
```
Синтаксис (FreeMonoid α)  ──eval f──→  Семантика (моноид M)
        │                                    │
   все возможные пути                что они значат
        │                                    │
        └──────── ker (eval f) ──────────────┘
                       │
                 Эквивалентность
              (какие пути одинаковы)
```

* **Синтаксис** — свободный моноид `FreeMonoid α` — пространство ВСЕХ путей.
* **Семантика** — моноид `M`.
* **Интерпретация** — гомоморфизм `eval f : FreeMonoid α →* M`.
* **Теория (эквивалентность)** — ядро `eval f`: какие пути дают один элемент.

Файл самодостаточен: все нужные определения продублированы.
-/

namespace UAM_Equivalence_ns

open FreeMonoid

universe u v

variable {α : Type u} {M : Type v}

/-! ## 0. Интерпретация путей: `eval`

`eval f` отправляет путь (слово `w : FreeMonoid α`) в элемент моноида `M`,
перемножая образы генераторов `f a`. Это в точности `FreeMonoid.lift f`. -/

/-- Интерпретация путей в моноиде `M`.
    Путь `w` (слово из генераторов) переходит в произведение образов `f`. -/
@[reducible] noncomputable def eval [Monoid M] (f : α → M) : FreeMonoid α →* M :=
  FreeMonoid.lift f

@[simp] theorem eval_of [Monoid M] (f : α → M) (a : α) :
    eval f (FreeMonoid.of a) = f a := by
  simp [eval]

@[simp] theorem eval_one [Monoid M] (f : α → M) :
    eval f (1 : FreeMonoid α) = 1 := by
  simp [eval]

theorem eval_mul [Monoid M] (f : α → M) (w₁ w₂ : FreeMonoid α) :
    eval f (w₁ * w₂) = eval f w₁ * eval f w₂ := by
  simp [eval]

/-! ## 1. Отношение эквивалентности путей и конгруэнция -/

/-- Два пути (слова) `w₁` и `w₂` **эквивалентны** в моноиде `M` относительно
    интерпретации `eval f`, если они порождают один и тот же элемент. -/
def PathEquiv [Monoid M] (f : α → M) (w₁ w₂ : FreeMonoid α) : Prop :=
  eval f w₁ = eval f w₂

@[inherit_doc] notation:50 w₁ " ~[" f "] " w₂ => PathEquiv f w₁ w₂

/-- **Рефлексивность**: каждый путь эквивалентен самому себе. -/
theorem PathEquiv.refl [Monoid M] (f : α → M) (w : FreeMonoid α) :
    PathEquiv f w w := rfl

/-- **Симметричность**. -/
theorem PathEquiv.symm [Monoid M] {f : α → M} {w₁ w₂ : FreeMonoid α} :
    PathEquiv f w₁ w₂ → PathEquiv f w₂ w₁ := fun h => Eq.symm h

/-- **Транзитивность**. -/
theorem PathEquiv.trans [Monoid M] {f : α → M} {w₁ w₂ w₃ : FreeMonoid α} :
    PathEquiv f w₁ w₂ → PathEquiv f w₂ w₃ → PathEquiv f w₁ w₃ :=
  fun h₁ h₂ => Eq.trans h₁ h₂

/-- **Совместимость с умножением** — это и делает `PathEquiv f` *конгруэнцией*:
    эквивалентность сохраняется при умножении путей. -/
theorem PathEquiv.mul [Monoid M] {f : α → M} {w₁ w₂ u₁ u₂ : FreeMonoid α}
    (hw : PathEquiv f w₁ w₂) (hu : PathEquiv f u₁ u₂) :
    PathEquiv f (w₁ * u₁) (w₂ * u₂) := by
  unfold PathEquiv at *
  rw [eval_mul, eval_mul, hw, hu]

/-- Ядро является конгруэнцией: обрамление `u · w₁ · v ~ u · w₂ · v`. -/
theorem PathEquiv.congr [Monoid M] {f : α → M} {w₁ w₂ : FreeMonoid α}
    (h : PathEquiv f w₁ w₂) (u v : FreeMonoid α) :
    PathEquiv f (u * w₁ * v) (u * w₂ * v) :=
  ((PathEquiv.refl f u).mul h).mul (PathEquiv.refl f v)

/-- `PathEquiv f` как конгруэнция Mathlib (`Con`), а именно ядро `eval f`. -/
noncomputable def pathCon [Monoid M] (f : α → M) : Con (FreeMonoid α) :=
  Con.ker (eval f)

/-- `PathEquiv f` совпадает с отношением конгруэнции `pathCon f = Con.ker (eval f)`. -/
theorem pathCon_rel [Monoid M] (f : α → M) (w₁ w₂ : FreeMonoid α) :
    (pathCon f) w₁ w₂ ↔ PathEquiv f w₁ w₂ :=
  Con.ker_rel (eval f)

/-! ## 2. Фактор и первая теорема об изоморфизме

Фактор-моноид `FreeMonoid α` по конгруэнции `pathCon f` изоморфен образу
`eval f`, т.е. подмоноиду `M`, порождённому `f(α)`. Это первая теорема об
изоморфизме для моноидов (`Con.quotientKerEquivRange`). -/

/-- **Первая теорема об изоморфизме для моноидов**:
    `FreeMonoid α / ker(eval f) ≅ Im(eval f)`. -/
noncomputable def pathQuotientEquivRange [Monoid M] (f : α → M) :
    (pathCon f).Quotient ≃* MonoidHom.mrange (eval f) :=
  Con.quotientKerEquivRange (eval f)

/-- Образ `eval f` — это подмоноид `M`, порождённый образом генераторов `f(α)`. -/
theorem mrange_eval [Monoid M] (f : α → M) :
    MonoidHom.mrange (eval f) = Submonoid.closure (Set.range f) :=
  FreeMonoid.mrange_lift f

/-- Комбинация: фактор `FreeMonoid α / ker(eval f)` изоморфен подмоноиду,
    порождённому образами генераторов. -/
noncomputable def pathQuotientEquivClosure [Monoid M] (f : α → M) :
    (pathCon f).Quotient ≃* Submonoid.closure (Set.range f) :=
  (pathQuotientEquivRange f).trans
    (MulEquiv.subsemigroupCongr (by rw [mrange_eval]) )

/-! ## 3. Свободный моноид: нетривиальных эквивалентностей нет

В свободном моноиде (интерпретация — тождественная, `f = FreeMonoid.of`)
разные пути всегда различны: ядро тривиально. -/

/-- В свободном моноиде эквивалентны только совпадающие пути: ядро тривиально. -/
theorem freeMonoid_no_equivalence {w₁ w₂ : FreeMonoid α}
    (h : PathEquiv (FreeMonoid.of : α → FreeMonoid α) w₁ w₂) : w₁ = w₂ := by
  have hid : eval (FreeMonoid.of : α → FreeMonoid α) = MonoidHom.id (FreeMonoid α) := by
    apply FreeMonoid.hom_eq; intro x; simp
  unfold PathEquiv at h
  rw [hid] at h
  simpa using h

/-! ## 4. Коммутативный моноид: перестановка = эквивалентность

В коммутативном моноиде перестановка соседних генераторов сохраняет результат:
это минимальная нетривиальная эквивалентность. -/

/-- В коммутативном моноиде перестановка соседних генераторов даёт
    эквивалентные пути. -/
theorem comm_equiv_swap [CommMonoid M] (f : α → M) (a b : α) (w : FreeMonoid α) :
    PathEquiv f (FreeMonoid.of a * FreeMonoid.of b * w)
                (FreeMonoid.of b * FreeMonoid.of a * w) := by
  unfold PathEquiv
  rw [eval_mul, eval_mul, eval_mul, eval_mul, eval_of, eval_of, mul_comm (f a) (f b)]

/-! ## 5. Эквивалентность и направленность (trivial units)

**Направленность** моноида: `∀ u v, u · v = 1 → u = 1`
(нельзя «пойти назад»: единственный элемент, который обратим слева до `1`, — это `1`).

Ключевой результат: в направленном моноиде путь с результатом `1` состоит
целиком из генераторов, чьи образы равны `1`. Иначе говоря, «путь назад к `1`»
не может использовать нетривиальный генератор. -/

/-- Вспомогательная лемма над списками: если направленность выполнена и
    произведение образов `= 1`, то каждый образ `= 1`. -/
theorem dir_prod_one [Monoid M] (hdir : ∀ u v : M, u * v = 1 → u = 1)
    (f : α → M) (l : List α) (h : (l.map f).prod = 1) :
    ∀ a ∈ l, f a = 1 := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons b t ih =>
      simp only [List.map_cons, List.prod_cons] at h
      have hb : f b = 1 := hdir (f b) ((t.map f).prod) h
      have ht : (t.map f).prod = 1 := by
        rw [hb, one_mul] at h; exact h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | hat
      · exact hb
      · exact ih ht a hat

/-- **Направленность и путь к `1`**: в направленном моноиде, если путь `w`
    даёт результат `1` (`eval f w = 1`), то образ каждого генератора этого
    пути равен `1`. Содержательно: «путь назад к началу» не проходит через
    нетривиальные генераторы. -/
theorem directionality_path_to_one [Monoid M]
    (hdir : ∀ u v : M, u * v = 1 → u = 1)
    (f : α → M) (w : FreeMonoid α) (h : eval f w = 1) :
    ∀ a ∈ FreeMonoid.toList w, f a = 1 := by
  have : ((FreeMonoid.toList w).map f).prod = 1 := by
    rw [← FreeMonoid.lift_apply]; exact h
  exact dir_prod_one hdir f (FreeMonoid.toList w) this

/-- Следствие: если вдобавок все генераторы имеют нетривиальный образ
    (`∀ a, f a ≠ 1`), то единственный путь с результатом `1` — пустой путь
    (`w = 1`). Единственный путь к `1` начинается и заканчивается в `1`. -/
theorem directionality_only_identity_path_to_one [Monoid M]
    (hdir : ∀ u v : M, u * v = 1 → u = 1)
    (f : α → M) (hf : ∀ a, f a ≠ 1)
    (w : FreeMonoid α) (h : eval f w = 1) : w = 1 := by
  have hall := directionality_path_to_one hdir f w h
  have : FreeMonoid.toList w = [] := by
    rcases List.eq_nil_or_concat (FreeMonoid.toList w) with hnil | ⟨l, a, hla⟩
    · exact hnil
    · exact absurd (hall a (by rw [hla]; simp)) (hf a)
  exact FreeMonoid.toList.injective (by simpa using this)

/-! ## 6. Нормальная форма

Канонический представитель класса эквивалентности пути.
В свободном моноиде нормальная форма — сам путь (эквивалентность тривиальна). -/

/-- Нормальная форма в свободном моноиде: путь совпадает со своим
    представителем (ведь классы одноэлементны). -/
theorem freeMonoid_normalForm_eq {w₁ w₂ : FreeMonoid α}
    (h : PathEquiv (FreeMonoid.of : α → FreeMonoid α) w₁ w₂) :
    w₁ = w₂ := freeMonoid_no_equivalence h

/-! ## 7. UAM-Модель: связь синтаксиса и семантики

UAM-модель над алфавитом `α` — это моноид вместе с сюръективной
интерпретацией из свободного моноида. Каждый элемент модели есть результат
некоторого пути. -/

/-- **UAM-Модель**: моноид-носитель `carrier` с интерпретацией `evalMap`
    из свободного моноида `FreeMonoid α`, покрывающей весь носитель.

    * Синтаксис: `FreeMonoid α` (все возможные пути);
    * Семантика: `carrier` (фактические элементы);
    * Интерпретация: `evalMap` (каждому пути — элемент);
    * Теория: `Con.ker evalMap` (какие пути эквивалентны). -/
structure Model (α : Type u) where
  /-- Носитель модели. -/
  carrier : Type v
  /-- Структура моноида на носителе. -/
  [monoid : Monoid carrier]
  /-- Интерпретация: гомоморфизм из синтаксиса (путей) в семантику. -/
  evalMap : FreeMonoid α →* carrier
  /-- Каждый элемент носителя — результат некоторого пути. -/
  surjective : Function.Surjective evalMap

attribute [instance] Model.monoid

namespace Model

variable (Mod : Model.{u, v} α)

/-- Теория модели: конгруэнция «эквивалентности путей» = ядро интерпретации. -/
noncomputable def theory : Con (FreeMonoid α) := Con.ker Mod.evalMap

/-- Два пути эквивалентны в модели, если они дают один элемент носителя. -/
def Equiv (w₁ w₂ : FreeMonoid α) : Prop := Mod.evalMap w₁ = Mod.evalMap w₂

/-- Эквивалентность путей модели совпадает с её теорией (ядром). -/
theorem theory_rel (w₁ w₂ : FreeMonoid α) :
    (Mod.theory) w₁ w₂ ↔ Mod.Equiv w₁ w₂ := Con.ker_rel Mod.evalMap

/-- **Фактор-модель изоморфна носителю**: так как интерпретация сюръективна,
    `FreeMonoid α / theory ≅ carrier`. Это делает модель ровно
    «пространством путей по модулю эквивалентности». -/
noncomputable def quotientEquivCarrier :
    (Mod.theory).Quotient ≃* Mod.carrier := by
  refine (Con.quotientKerEquivRange Mod.evalMap).trans ?_
  have : MonoidHom.mrange Mod.evalMap = (⊤ : Submonoid Mod.carrier) := by
    rw [MonoidHom.mrange_eq_top]; exact Mod.surjective
  rw [this]
  exact Submonoid.topEquiv

/-- Каноническая UAM-модель, порождённая функцией `f : α → M`:
    носитель — подмоноид, порождённый образом `f`, интерпретация — `eval f`. -/
noncomputable def ofFun [Monoid M] (f : α → M) : Model.{u, v} α where
  carrier := MonoidHom.mrange (UAM_Equivalence_ns.eval f)
  evalMap := (UAM_Equivalence_ns.eval f).mrangeRestrict
  surjective := (UAM_Equivalence_ns.eval f).mrangeRestrict_surjective

end Model

/-! ## 8. Три смысла «Эквивалентности»

* **Существительное** — класс эквивалентности `[w]` в факторе `FreeMonoid α / ~`
  (множество путей с одним результатом): это элемент `(pathCon f).Quotient`.
* **Глагол** — действие «сравнить пути»: проверка `eval f w₁ = eval f w₂`,
  т.е. предикат `PathEquiv f w₁ w₂` (словесная проблема, word problem).
* **Прошедшее** — установленный факт эквивалентности `w₁ ~[f] w₂`.

Эти три смысла формально согласованы: -/

/-- (Существительное ↔ Прошедшее) Два пути лежат в одном классе фактора
    тогда и только тогда, когда они эквивалентны. -/
theorem quotient_mk_eq_iff [Monoid M] (f : α → M) (w₁ w₂ : FreeMonoid α) :
    (pathCon f).toQuotient w₁ = (pathCon f).toQuotient w₂ ↔ PathEquiv f w₁ w₂ := by
  rw [Con.eq]
  exact pathCon_rel f w₁ w₂

/-- (Глагол ↔ Прошедшее) «Сравнить пути» = проверить равенство образов =
    факт эквивалентности. По определению одно и то же. -/
theorem verb_eq_fact [Monoid M] (f : α → M) (w₁ w₂ : FreeMonoid α) :
    (eval f w₁ = eval f w₂) ↔ PathEquiv f w₁ w₂ := Iff.rfl

end UAM_Equivalence_ns
