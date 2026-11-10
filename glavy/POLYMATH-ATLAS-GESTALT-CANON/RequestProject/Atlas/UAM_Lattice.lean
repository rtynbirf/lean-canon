import Mathlib

/-!
# UAM_Lattice.lean — Решётка моделей UAM(α)

Этот файл продолжает построение UAM (Universal Algebra of Models). Категория
`UAM(α)` — это предпорядок (thin category) моделей над алфавитом `α`. Здесь мы
показываем, что этот предпорядок образует **полную решётку**.

Ключевое наблюдение: `Model.Equiv Mod` — это в точности `Con.ker Mod.evalMap`,
конгруэнция на свободном моноиде `FreeMonoid α`. Порядок `modelLe` соответствует
включению конгруэнций, а `Con (FreeMonoid α)` — полная решётка. Отсюда:

| Операция | Конгруэнции | Модели |
|---|---|---|
| Meet ⊓ | пересечение | «запоминает только общее» |
| Join ⊔ | замыкание объединения | «запоминает всё» |
| ⊥ | диагональ | свободная модель |
| ⊤ | полный квадрат | тривиальная модель |

Определения `Model`, `Model.Equiv`, `modelLe`, `Model.ofFree`, `Model.ofTrivial`,
`StrictIso` продублированы из `UAM_Morphism.lean` (файл сделан самодостаточным).
-/

universe u v w

open scoped Classical

namespace UAM_Lattice_ns

/-! ## §0. Дублированные определения (from UAM_Morphism) -/

/-- Модель над алфавитом `α`: моноид-носитель вместе с сюръективным
вычислением слов `FreeMonoid α`. -/
-- duplicated from UAM_Morphism
structure Model (α : Type u) where
  carrier : Type v
  [monoid : Monoid carrier]
  evalMap : FreeMonoid α →* carrier
  surjective : Function.Surjective evalMap

attribute [instance] Model.monoid

namespace Model

variable {α : Type u}

/-- Отношение эквивалентности слов, индуцированное моделью:
два слова эквивалентны, если модель их не различает. -/
-- duplicated from UAM_Morphism
def Equiv (Mod : Model.{u, v} α) (w₁ w₂ : FreeMonoid α) : Prop :=
  Mod.evalMap w₁ = Mod.evalMap w₂

end Model

variable {α : Type u}

/-- Алгебраический порядок на моделях: `Mod₁ ≤ Mod₂`, если `Mod₂` отождествляет
все слова, которые отождествляет `Mod₁` (то есть `Mod₂` «грубее»). -/
-- duplicated from UAM_Morphism
def modelLe (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) : Prop :=
  ∀ w₁ w₂, Model.Equiv Mod₁ w₁ w₂ → Model.Equiv Mod₂ w₁ w₂

/-- `modelLe` рефлексивно. -/
theorem modelLe_refl (Mod : Model.{u, v} α) : modelLe Mod Mod := fun _ _ h => h

/-- `modelLe` транзитивно. -/
theorem modelLe_trans {Mod₁ : Model.{u, v} α} {Mod₂ : Model.{u, w} α}
    {Mod₃ : Model α} (h₁₂ : modelLe Mod₁ Mod₂) (h₂₃ : modelLe Mod₂ Mod₃) :
    modelLe Mod₁ Mod₃ := fun w₁ w₂ h => h₂₃ w₁ w₂ (h₁₂ w₁ w₂ h)

/-- Строгий изоморфизм моделей: изоморфизм носителей, коммутирующий с
вычислением слов. Это «равенство» в тонкой категории `UAM(α)`. -/
-- duplicated from UAM_Morphism
structure StrictIso (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) where
  toEquiv : Mod₁.carrier ≃* Mod₂.carrier
  comm : ∀ x, toEquiv (Mod₁.evalMap x) = Mod₂.evalMap x

/-- Свободная модель: носитель — сам свободный моноид, вычисление тождественно.
Она «ничего не забывает». -/
-- duplicated from UAM_Morphism
def Model.ofFree (α : Type u) : Model.{u, u} α where
  carrier := FreeMonoid α
  evalMap := MonoidHom.id _
  surjective := Function.surjective_id

/-- Тривиальная модель: носитель — `PUnit`, все слова отождествлены.
Она «всё забывает». -/
-- duplicated from UAM_Morphism
def Model.ofTrivial (α : Type u) : Model.{u, u} α where
  carrier := PUnit
  evalMap := 1
  surjective := fun _ => ⟨1, Subsingleton.elim _ _⟩

/-! ## §1. Конгруэнция как теория модели

Теория модели — это её ядро как конгруэнция на свободном моноиде. Порядок
моделей в точности соответствует включению конгруэнций. -/

/-- Конгруэнция (теория), ассоциированная с моделью: ядро вычисляющего
гомоморфизма. -/
def Model.con (Mod : Model.{u, v} α) : Con (FreeMonoid α) :=
  Con.ker Mod.evalMap

/-- `Model.con Mod` отождествляет слова ровно тогда, когда их отождествляет
модель. -/
theorem Model.con_rel (Mod : Model.{u, v} α) (w₁ w₂ : FreeMonoid α) :
    (Model.con Mod) w₁ w₂ ↔ Model.Equiv Mod w₁ w₂ := by
  simp [Model.con, Model.Equiv, Con.ker_rel]

/-
**Фундаментальная теорема связи порядка.** `modelLe` совпадает с включением
конгруэнций.
-/
theorem modelLe_iff_con_le (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) :
    modelLe Mod₁ Mod₂ ↔ Model.con Mod₁ ≤ Model.con Mod₂ := by
  simp +decide only [modelLe, Model.Equiv, Model.con, Con.le_def, Con.ker_rel]

/-- Из `modelLe` следует включение конгруэнций. -/
theorem con_le_of_modelLe {Mod₁ : Model.{u, v} α} {Mod₂ : Model.{u, w} α}
    (h : modelLe Mod₁ Mod₂) : Model.con Mod₁ ≤ Model.con Mod₂ :=
  (modelLe_iff_con_le Mod₁ Mod₂).1 h

/-- Из включения конгруэнций следует `modelLe`. -/
theorem modelLe_of_con_le {Mod₁ : Model.{u, v} α} {Mod₂ : Model.{u, w} α}
    (h : Model.con Mod₁ ≤ Model.con Mod₂) : modelLe Mod₁ Mod₂ :=
  (modelLe_iff_con_le Mod₁ Mod₂).2 h

/-
Теория свободной модели — диагональ (`⊥`): она различает все слова.
-/
theorem Model.con_ofFree (α : Type u) : Model.con (Model.ofFree α) = ⊥ := by
  exact Con.toSetoid_eq_bot.mp rfl

/-
Теория тривиальной модели — полный квадрат (`⊤`): она отождествляет всё.
-/
theorem Model.con_ofTrivial (α : Type u) : Model.con (Model.ofTrivial α) = ⊤ := by
  convert Con.ext _;
  tauto

/-
**Критерий строгого изоморфизма.** Модели строго изоморфны тогда и только
тогда, когда у них совпадают теории (двусторонний `modelLe`).
-/
theorem strictIso_iff_sameTheory (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) :
    Nonempty (StrictIso Mod₁ Mod₂) ↔ modelLe Mod₁ Mod₂ ∧ modelLe Mod₂ Mod₁ := by
  constructor <;> intro h;
  · obtain ⟨ iso ⟩ := h;
    constructor;
    · intro w₁ w₂ h;
      simpa [ iso.comm ] using congr_arg iso.toEquiv h;
    · intro w₁ w₂ h; have := iso.comm w₁; have := iso.comm w₂; simp_all +decide [ Model.Equiv ] ;
      exact iso.toEquiv.injective ( by aesop );
  · -- By definition of `modelLe`, we know that `Con.ker Mod₁.evalMap = Con.ker Mod₂.evalMap`.
    have h_ker : Con.ker Mod₁.evalMap = Con.ker Mod₂.evalMap := by
      exact le_antisymm ( con_le_of_modelLe h.1 ) ( con_le_of_modelLe h.2 );
    refine' ⟨ ⟨ _, _ ⟩ ⟩;
    refine' MulEquiv.trans ( MulEquiv.symm ( Con.quotientKerEquivOfSurjective _ Mod₁.surjective ) ) ( MulEquiv.trans ( Con.congr h_ker ) ( Con.quotientKerEquivOfSurjective _ Mod₂.surjective ) );
    simp +decide [ Con.quotientKerEquivOfSurjective ];
    intro x
    generalize_proofs at *;
    have := ‹∃ finv, Function.RightInverse finv Mod₁.evalMap›.choose_spec ( Mod₁.evalMap x ) ; simp_all +decide [ Con.ext_iff ] ;

/-- Достаточное условие строгого изоморфизма: двусторонний `modelLe`. -/
theorem strictIso_of_sameTheory {Mod₁ : Model.{u, v} α} {Mod₂ : Model.{u, w} α}
    (h₁ : modelLe Mod₁ Mod₂) (h₂ : modelLe Mod₂ Mod₁) :
    Nonempty (StrictIso Mod₁ Mod₂) :=
  (strictIso_iff_sameTheory Mod₁ Mod₂).2 ⟨h₁, h₂⟩

/-- Строгий изоморфизм влечёт равенство теорий. -/
theorem con_eq_of_strictIso {Mod₁ : Model.{u, v} α} {Mod₂ : Model.{u, w} α}
    (h : Nonempty (StrictIso Mod₁ Mod₂)) : Model.con Mod₁ = Model.con Mod₂ := by
  obtain ⟨h₁, h₂⟩ := (strictIso_iff_sameTheory Mod₁ Mod₂).1 h
  exact le_antisymm (con_le_of_modelLe h₁) (con_le_of_modelLe h₂)

/-! ## §2. Meet моделей (пересечение теорий)

`meet` двух моделей запоминает ровно то, на чём согласны обе: фактор свободного
моноида по пересечению конгруэнций. -/

/-- Пересечение двух моделей: фактор `FreeMonoid α` по пересечению теорий. -/
def Model.meet (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) : Model.{u, u} α where
  carrier := (Model.con Mod₁ ⊓ Model.con Mod₂).Quotient
  evalMap := (Model.con Mod₁ ⊓ Model.con Mod₂).mk'
  surjective := Con.mk'_surjective

/-- Теория `meet` — пересечение теорий сомножителей. -/
theorem Model.con_meet (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) :
    Model.con (Model.meet Mod₁ Mod₂) = Model.con Mod₁ ⊓ Model.con Mod₂ := by
  simp [Model.con, Model.meet, Con.mk'_ker]

/-- `meet` не больше первого сомножителя. -/
theorem meet_le_left (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) :
    modelLe (Model.meet Mod₁ Mod₂) Mod₁ := by
  refine modelLe_of_con_le ?_
  rw [Model.con_meet]; exact inf_le_left

/-- `meet` не больше второго сомножителя. -/
theorem meet_le_right (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) :
    modelLe (Model.meet Mod₁ Mod₂) Mod₂ := by
  refine modelLe_of_con_le ?_
  rw [Model.con_meet]; exact inf_le_right

/-- **Универсальное свойство `meet`.** Любая модель, меньшая обеих, меньше их
`meet`. -/
theorem meet_greatest {Mod₁ : Model.{u, v} α} {Mod₂ : Model.{u, w} α}
    {Mod₃ : Model α} (h₁ : modelLe Mod₃ Mod₁) (h₂ : modelLe Mod₃ Mod₂) :
    modelLe Mod₃ (Model.meet Mod₁ Mod₂) := by
  refine modelLe_of_con_le ?_
  rw [Model.con_meet]
  exact le_inf (con_le_of_modelLe h₁) (con_le_of_modelLe h₂)

/-! ## §3. Join моделей (замыкание объединения теорий)

`join` двух моделей запоминает всё, что помнит хотя бы одна: фактор по
конгруэнции, порождённой объединением теорий. -/

/-- Объединение двух моделей: фактор `FreeMonoid α` по замыканию объединения
теорий. -/
def Model.join (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) : Model.{u, u} α where
  carrier := (Model.con Mod₁ ⊔ Model.con Mod₂).Quotient
  evalMap := (Model.con Mod₁ ⊔ Model.con Mod₂).mk'
  surjective := Con.mk'_surjective

/-- Теория `join` — объединение (в решётке конгруэнций) теорий слагаемых. -/
theorem Model.con_join (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) :
    Model.con (Model.join Mod₁ Mod₂) = Model.con Mod₁ ⊔ Model.con Mod₂ := by
  simp [Model.con, Model.join, Con.mk'_ker]

/-- Первое слагаемое не больше `join`. -/
theorem left_le_join (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) :
    modelLe Mod₁ (Model.join Mod₁ Mod₂) := by
  refine modelLe_of_con_le ?_
  rw [Model.con_join]; exact le_sup_left

/-- Второе слагаемое не больше `join`. -/
theorem right_le_join (Mod₁ : Model.{u, v} α) (Mod₂ : Model.{u, w} α) :
    modelLe Mod₂ (Model.join Mod₁ Mod₂) := by
  refine modelLe_of_con_le ?_
  rw [Model.con_join]; exact le_sup_right

/-- **Универсальное свойство `join`.** Любая модель, большая обеих, больше их
`join`. -/
theorem join_least {Mod₁ : Model.{u, v} α} {Mod₂ : Model.{u, w} α}
    {Mod₃ : Model α} (h₁ : modelLe Mod₁ Mod₃) (h₂ : modelLe Mod₂ Mod₃) :
    modelLe (Model.join Mod₁ Mod₂) Mod₃ := by
  refine modelLe_of_con_le ?_
  rw [Model.con_join]
  exact sup_le (con_le_of_modelLe h₁) (con_le_of_modelLe h₂)

/-! ## §4. Коммутативность и ассоциативность (вплоть до изоморфизма)

`UAM(α)` — предпорядок, поэтому `meet` и `join` единственны только с точностью
до строгого изоморфизма. -/

/-- Коммутативность `meet`. -/
theorem meet_comm (Mod₁ Mod₂ : Model.{u, v} α) :
    Nonempty (StrictIso (Model.meet Mod₁ Mod₂) (Model.meet Mod₂ Mod₁)) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    rw [Model.con_meet, Model.con_meet] <;> rw [inf_comm]

/-- Ассоциативность `meet`. -/
theorem meet_assoc (Mod₁ Mod₂ Mod₃ : Model.{u, v} α) :
    Nonempty (StrictIso (Model.meet (Model.meet Mod₁ Mod₂) Mod₃)
                        (Model.meet Mod₁ (Model.meet Mod₂ Mod₃))) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    simp only [Model.con_meet] <;> rw [inf_assoc]

/-- Коммутативность `join`. -/
theorem join_comm (Mod₁ Mod₂ : Model.{u, v} α) :
    Nonempty (StrictIso (Model.join Mod₁ Mod₂) (Model.join Mod₂ Mod₁)) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    rw [Model.con_join, Model.con_join] <;> rw [sup_comm]

/-- Ассоциативность `join`. -/
theorem join_assoc (Mod₁ Mod₂ Mod₃ : Model.{u, v} α) :
    Nonempty (StrictIso (Model.join (Model.join Mod₁ Mod₂) Mod₃)
                        (Model.join Mod₁ (Model.join Mod₂ Mod₃))) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    simp only [Model.con_join] <;> rw [sup_assoc]

/-! ## §5. Поглощение и граничные свойства -/

/-- Свободная модель — нейтральный элемент `meet` (слева). -/
theorem meet_free_left (Mod : Model.{u, v} α) :
    Nonempty (StrictIso (Model.meet (Model.ofFree α) Mod) (Model.ofFree α)) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    simp only [Model.con_meet, Model.con_ofFree, bot_inf_eq, le_refl]

/-- Свободная модель — нейтральный элемент `meet` (справа). -/
theorem meet_free_right (Mod : Model.{u, v} α) :
    Nonempty (StrictIso (Model.meet Mod (Model.ofFree α)) (Model.ofFree α)) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    simp only [Model.con_meet, Model.con_ofFree, inf_bot_eq, le_refl]

/-- Тривиальная модель — нейтральный элемент `join` (слева). -/
theorem join_trivial_left (Mod : Model.{u, v} α) :
    Nonempty (StrictIso (Model.join (Model.ofTrivial α) Mod) (Model.ofTrivial α)) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    simp only [Model.con_join, Model.con_ofTrivial, top_sup_eq, le_refl]

/-- Тривиальная модель — нейтральный элемент `join` (справа). -/
theorem join_trivial_right (Mod : Model.{u, v} α) :
    Nonempty (StrictIso (Model.join Mod (Model.ofTrivial α)) (Model.ofTrivial α)) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    simp only [Model.con_join, Model.con_ofTrivial, sup_top_eq, le_refl]

/-- Закон поглощения: `Mod₁ ⊓ (Mod₁ ⊔ Mod₂) ≅ Mod₁`. -/
theorem meet_join_absorption (Mod₁ Mod₂ : Model.{u, v} α) :
    Nonempty (StrictIso (Model.meet Mod₁ (Model.join Mod₁ Mod₂)) Mod₁) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    simp only [Model.con_meet, Model.con_join, inf_sup_self, le_refl]

/-- Закон поглощения: `Mod₁ ⊔ (Mod₁ ⊓ Mod₂) ≅ Mod₁`. -/
theorem join_meet_absorption (Mod₁ Mod₂ : Model.{u, v} α) :
    Nonempty (StrictIso (Model.join Mod₁ (Model.meet Mod₁ Mod₂)) Mod₁) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    simp only [Model.con_join, Model.con_meet, sup_inf_self, le_refl]

/-- Идемпотентность `meet`. -/
theorem meet_idempotent (Mod : Model.{u, v} α) :
    Nonempty (StrictIso (Model.meet Mod Mod) Mod) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    simp only [Model.con_meet, inf_idem, le_refl]

/-- Идемпотентность `join`. -/
theorem join_idempotent (Mod : Model.{u, v} α) :
    Nonempty (StrictIso (Model.join Mod Mod) Mod) := by
  refine strictIso_of_sameTheory (modelLe_of_con_le ?_) (modelLe_of_con_le ?_) <;>
    simp only [Model.con_join, sup_idem, le_refl]

/-! ## §6. Произвольные meets и joins (полная решётка)

`meet` и `join` существуют для произвольных семейств моделей, что делает
`UAM(α)` полной решёткой. -/

/-- Meet произвольного семейства моделей: фактор по пересечению всех теорий. -/
def Model.sInf' (Mods : Set (Model.{u, v} α)) : Model.{u, u} α where
  carrier := (sInf (Model.con '' Mods)).Quotient
  evalMap := (sInf (Model.con '' Mods)).mk'
  surjective := Con.mk'_surjective

/-- Теория `sInf'` — пересечение всех теорий семейства. -/
theorem Model.con_sInf' (Mods : Set (Model.{u, v} α)) :
    Model.con (Model.sInf' Mods) = sInf (Model.con '' Mods) := by
  simp [Model.con, Model.sInf', Con.mk'_ker]

/-- `sInf'` не больше любого члена семейства. -/
theorem sInf'_le {Mods : Set (Model.{u, v} α)} {Mod₀ : Model.{u, v} α}
    (h₀ : Mod₀ ∈ Mods) : modelLe (Model.sInf' Mods) Mod₀ := by
  refine modelLe_of_con_le ?_
  rw [Model.con_sInf']
  exact sInf_le ⟨Mod₀, h₀, rfl⟩

/-- **Универсальное свойство `sInf'`.** Любая модель, меньшая всех членов
семейства, меньше их `sInf'`. -/
theorem sInf'_greatest {Mods : Set (Model.{u, v} α)} {Mod₃ : Model α}
    (h : ∀ Mod ∈ Mods, modelLe Mod₃ Mod) :
    modelLe Mod₃ (Model.sInf' Mods) := by
  refine modelLe_of_con_le ?_
  rw [Model.con_sInf']
  refine le_sInf ?_
  rintro c ⟨Mod, hMod, rfl⟩
  exact con_le_of_modelLe (h Mod hMod)

/-- Join произвольного семейства моделей: фактор по замыканию объединения всех
теорий. -/
def Model.sSup' (Mods : Set (Model.{u, v} α)) : Model.{u, u} α where
  carrier := (sSup (Model.con '' Mods)).Quotient
  evalMap := (sSup (Model.con '' Mods)).mk'
  surjective := Con.mk'_surjective

/-- Теория `sSup'` — объединение (в решётке конгруэнций) всех теорий семейства. -/
theorem Model.con_sSup' (Mods : Set (Model.{u, v} α)) :
    Model.con (Model.sSup' Mods) = sSup (Model.con '' Mods) := by
  simp [Model.con, Model.sSup', Con.mk'_ker]

/-- Любой член семейства не больше `sSup'`. -/
theorem le_sSup' {Mods : Set (Model.{u, v} α)} {Mod₀ : Model.{u, v} α}
    (h₀ : Mod₀ ∈ Mods) : modelLe Mod₀ (Model.sSup' Mods) := by
  refine modelLe_of_con_le ?_
  rw [Model.con_sSup']
  exact le_sSup ⟨Mod₀, h₀, rfl⟩

/-- **Универсальное свойство `sSup'`.** Любая модель, большая всех членов
семейства, больше их `sSup'`. -/
theorem sSup'_least {Mods : Set (Model.{u, v} α)} {Mod₃ : Model α}
    (h : ∀ Mod ∈ Mods, modelLe Mod Mod₃) :
    modelLe (Model.sSup' Mods) Mod₃ := by
  refine modelLe_of_con_le ?_
  rw [Model.con_sSup']
  refine sSup_le ?_
  rintro c ⟨Mod, hMod, rfl⟩
  exact con_le_of_modelLe (h Mod hMod)

/-! ## §7. Интерпретация: «спектр моделей»

Решётка `UAM(α)` — это «спектр» всех возможных теорий над алфавитом `α`.

* Каждый элемент решётки — «точка зрения» на алфавит: что различать, что
  отождествлять.
* Движение вниз по решётке (`meet`, `sInf'`) — «забывание» различий, то есть
  добавление отождествлений.
* Движение вверх (`join`, `sSup'`) — «различение», то есть удаление
  отождествлений.
* `⊥` — свободная модель (`Model.ofFree`), различающая всё
  (`Model.con_ofFree`).
* `⊤` — тривиальная модель (`Model.ofTrivial`), отождествляющая всё
  (`Model.con_ofTrivial`).

Формально: отображение `Model.con : Model α → Con (FreeMonoid α)` — это
изоморфизм предпорядка `(Model α, modelLe)` на полную решётку конгруэнций
`Con (FreeMonoid α)` (сюръективно на объекты с точностью до `StrictIso`,
см. `modelLe_iff_con_le` и `strictIso_iff_sameTheory`). Это точный аналог
спектра примитивных идеалов, но для моноидов. -/

end UAM_Lattice_ns