import Mathlib

/-!
# UAM_Functor.lean — Функтор изменения алфавита

Этот файл исследует «горизонтальное» измерение UAM: как модели переходят при
изменении алфавита. Функция `f : α → β` порождает гомоморфизм свободных
моноидов `FreeMonoid.map f`, а композиция с `evalMap` даёт **pullback модели**.

Ключевое ограничение: pullback корректен только при сюръективном `f` (иначе
теряется сюръективность `evalMap`). Биективный `f` даёт изоморфизм;
не-инъективный `f` может увеличить теорию.

Все определения дублированы из предыдущих файлов UAM с пометкой
`-- duplicated from UAM_...`.
-/

namespace UAM_Functor_ns

universe u v

/-- Модель над алфавитом `α`: моноид с сюръективным гомоморфизмом вычисления
    из свободного моноида. -/
-- duplicated from UAM_Equivalence
structure Model (α : Type u) : Type (max u (v + 1)) where
  carrier : Type v
  [monoid : Monoid carrier]
  evalMap : FreeMonoid α →* carrier
  surjective : Function.Surjective evalMap

attribute [instance] Model.monoid

/-- Отношение эквивалентности слов в модели: два слова эквивалентны, если их
    образы под `evalMap` совпадают. -/
-- duplicated from UAM_Equivalence
def Model.Equiv {α : Type u} (Mod : Model.{u, v} α) (w₁ w₂ : FreeMonoid α) : Prop :=
  Mod.evalMap w₁ = Mod.evalMap w₂

/-- Предпорядок на моделях над одним алфавитом: `Mod₁ ≤ Mod₂`, если каждое
    отождествление в `Mod₁` есть и в `Mod₂`. -/
-- duplicated from UAM_Morphism
def modelLe {α : Type u} (Mod₁ Mod₂ : Model.{u, v} α) : Prop :=
  ∀ w₁ w₂, Mod₁.Equiv w₁ w₂ → Mod₂.Equiv w₁ w₂

/-- Свободная модель над `α`: носитель — сам свободный моноид, вычисление —
    тождество. -/
-- duplicated from UAM_Equivalence
def Model.ofFree (α : Type u) : Model.{u, u} α where
  carrier := FreeMonoid α
  evalMap := MonoidHom.id _
  surjective := Function.surjective_id

/-- Тривиальная модель над `α`: носитель — `PUnit`, все слова отождествлены. -/
-- duplicated from UAM_End
def Model.ofTrivial (α : Type u) : Model.{u, v} α where
  carrier := PUnit
  evalMap := 1
  surjective := fun _ => ⟨1, Subsingleton.elim _ _⟩

/-- Элемент `e` — «конец» (правый поглощающий элемент): `x * e = e` для всех `x`. -/
-- duplicated from UAM_End
def IsEnd {M : Type v} [Monoid M] (e : M) : Prop :=
  ∀ x : M, x * e = e

/-- Строгий изоморфизм моделей над одним алфавитом: изоморфизм носителей,
    коммутирующий с вычислением. -/
-- duplicated from UAM_Morphism
structure StrictIso {α : Type u} (Mod₁ Mod₂ : Model.{u, v} α) where
  toEquiv : Mod₁.carrier ≃* Mod₂.carrier
  commutes : toEquiv.toMonoidHom.comp Mod₁.evalMap = Mod₂.evalMap

/-! ## §1. `FreeMonoid.map` — основа -/

/-
`FreeMonoid.map f` — мономорфизм, если `f` инъективна.
-/
theorem FreeMonoid.map_injective {α β : Type u} (f : α → β) (hf : Function.Injective f) :
    Function.Injective (FreeMonoid.map f) := by
      exact fun x y h => List.map_injective_iff.mpr hf h

/-
`FreeMonoid.map f` — эпиморфизм, если `f` сюръективна.
-/
theorem FreeMonoid.map_surjective {α β : Type u} (f : α → β) (hf : Function.Surjective f) :
    Function.Surjective (FreeMonoid.map f) := by
      intro b
      induction' b using List.recOn with b ih;
      · exact ⟨ 1, rfl ⟩;
      · cases' hf b with a ha ; cases' ‹∃ a, _› with a' ha' ; use a :: a' ; aesop

/-! ## §2. Pullback модели -/

/-- Pullback модели вдоль функции `f : α → β`.
    Требование сюръективности `f` гарантирует, что композиция
    `evalMap ∘ FreeMonoid.map f` сюръективна, и pullback — корректная модель. -/
def Model.pullback {α β : Type u} (Mod : Model.{u, v} β) (f : α → β)
    (hf : Function.Surjective f) : Model.{u, v} α where
  carrier := Mod.carrier
  evalMap := Mod.evalMap.comp (FreeMonoid.map f)
  surjective := by
    intro x
    obtain ⟨w, hw⟩ := Mod.surjective x
    obtain ⟨v, hv⟩ := FreeMonoid.map_surjective f hf w
    exact ⟨v, by simp [hv, hw]⟩

/-- Сюръективность `evalMap` pullback-модели. -/
theorem Model.pullback_evalMap_surjective {α β : Type u} (Mod : Model.{u, v} β)
    (f : α → β) (hf : Function.Surjective f) :
    Function.Surjective (Model.pullback Mod f hf).evalMap :=
  (Model.pullback Mod f hf).surjective

/-! ## §3. Свойства pullback (функториальность) -/

/-
Pullback вдоль тождественной функции — та же модель.
-/
theorem Model.pullback_id {α : Type u} (Mod : Model.{u, v} α) :
    Model.pullback Mod id (Function.surjective_id) = Mod := by
      convert rfl;
      cases Mod;
      congr;
      ext; aesop;

/-
Pullback вдоль композиции — композиция pullback'ов.
-/
theorem Model.pullback_comp {α β γ : Type u} (Mod : Model.{u, v} γ) (f : α → β) (g : β → γ)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Model.pullback Mod (g ∘ f) (hg.comp hf) =
      Model.pullback (Model.pullback Mod g hg) f hf := by
        unfold Model.pullback; aesop;

/-
Конгруэнция pullback-модели содержит «прообраз» конгруэнции оригинала:
    если `FreeMonoid.map f w₁ = FreeMonoid.map f w₂`, то `w₁ ~ w₂` в pullback.
-/
theorem Model.pullback_con_contains_preimage {α β : Type u} (Mod : Model.{u, v} β) (f : α → β)
    (hf : Function.Surjective f) (w₁ w₂ : FreeMonoid α)
    (h : FreeMonoid.map f w₁ = FreeMonoid.map f w₂) :
    (Model.pullback Mod f hf).Equiv w₁ w₂ := by
      exact congr_arg ( fun z => Mod.evalMap z ) h

/-! ## §4. Pullback свободной модели -/

/-- Если `f` биективна, `FreeMonoid.map f` — изоморфизм моноидов. -/
noncomputable def FreeMonoid.mapMulEquiv {α β : Type u} (f : α → β) (hf : Function.Bijective f) :
    FreeMonoid α ≃* FreeMonoid β :=
  MulEquiv.ofBijective (FreeMonoid.map f)
    ⟨FreeMonoid.map_injective f hf.injective, FreeMonoid.map_surjective f hf.surjective⟩

/-
Если `f` биективна, pullback свободной модели — свободная модель.
    (Общий сюръективный случай неверен: не-инъективный `f` увеличивает теорию.)
-/
theorem Model.pullback_free_of_bijective {α β : Type u} (f : α → β) (hf : Function.Bijective f) :
    Nonempty (StrictIso (Model.pullback (Model.ofFree β) f hf.surjective) (Model.ofFree α)) := by
  refine' ⟨ ⟨ _, _ ⟩ ⟩;
  refine' MulEquiv.symm ( FreeMonoid.mapMulEquiv f hf );
  ext;
  convert MulEquiv.symm_apply_apply ( FreeMonoid.mapMulEquiv f hf ) ( FreeMonoid.of _ ) using 1

/-! ## §5. Pullback тривиальной модели -/

/-
Pullback тривиальной модели — тривиальная модель (любой алфавит).
-/
theorem Model.pullback_trivial {α β : Type u} (f : α → β) (hf : Function.Surjective f) :
    Nonempty (StrictIso (Model.pullback (Model.ofTrivial β) f hf) (Model.ofTrivial α)) := by
  constructor;
  constructor;
  all_goals norm_cast

/-! ## §6. Сохранение структурных свойств -/

/-- Если в оригинале есть End, то в pullback тоже есть End (тот же элемент):
    `IsEnd` — свойство элемента носителя, не зависящее от алфавита. -/
theorem Model.pullback_preserves_end {α β : Type u} (Mod : Model.{u, v} β) (f : α → β)
    (hf : Function.Surjective f) {e : Mod.carrier} (he : IsEnd e) :
    IsEnd (M := (Model.pullback Mod f hf).carrier) e := he

/-
**Не-инъективный `f` может увеличить теорию.**
    Существуют различные слова над `α`, отождествляемые в pullback свободной
    модели вдоль не-инъективного `f`. Здесь `f : Bool → Unit` (сюръективна,
    не инъективна), и слова `[true]`, `[false]` становятся эквивалентными.
-/
theorem Model.pullback_not_injective_increases_theory :
    ∃ (w₁ w₂ : FreeMonoid Bool),
      w₁ ≠ w₂ ∧
      (Model.pullback (Model.ofFree PUnit) (fun _ => PUnit.unit)
        (fun _ => ⟨true, rfl⟩)).Equiv w₁ w₂ := by
          refine' ⟨ FreeMonoid.of Bool.true, FreeMonoid.of Bool.false, _, _ ⟩ <;> simp +decide [ Model.Equiv ];
          · exact ne_of_apply_ne FreeMonoid.toList ( by simp +decide );
          · rfl

/-! ## §7. Три смысла функтора изменения алфавита

1. **Транспорт (Noun)**: `Model.pullback Mod f` — новая модель, «перенесённая»
   вдоль `f`. Носитель тот же, но алфавит изменился.

2. **Секция (Verb/Action)**: выбор `f` и pullback — активное перекодирование
   модели; `pullback_id` и `pullback_comp` делают это функториальным.

3. **Инвариант (Result)**: свойства, сохраняющиеся при любом биективном
   pullback — «настоящие» свойства модели (End, направленность, петли).

**Итог:** UAM — теория моделей как функтора из категории алфавитов в категорию
решёток. Алфавит — не «параметр», а часть морфизма.
-/

end UAM_Functor_ns