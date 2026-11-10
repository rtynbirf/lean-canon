/-
# OSA-4.0 — пять ортогональных осей и решётка типов

Формализация §3 «АРХИТЕКТУРНЫЙ СДВИГ — 5 ОРТОГОНАЛЬНЫХ ОСЕЙ» и §7
«FORMAL CORE / SEMANTIC KERNEL v0.1» кодекса OSA-4.0:

* Ось A (Категория): Object, Data, Model, Decision, Action, Meta;
* Ось B (Роль): Input, Output, Resource, Target, Constraint;
* Ось C (Уровень абстракции): L0 Reality → L1 Data → L2 Model → L3 Decision → L4 Action;
* Ось D (Тип): формальная решётка с отношением `IsSubtype`;
* Ось E (Фаза): Created, Available, Consumed, Destroyed.

Здесь доказываются LAW-001 (Type Reflexivity) и LAW-002 (Type Transitivity),
а также сама *ортогональность* осей: пространство артефактов — прямое
произведение осей, ни одна ось не является функцией остальных.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace Polymath.OSA4

/-! ## Ось A — категория -/

/-- Ось A: категория сущности. -/
inductive Category
  | Object | Data | Model | Decision | Action | Meta
  deriving DecidableEq, Repr, Fintype, Inhabited

/-! ## Ось B — роль -/

/-- Ось B: роль сущности в операторе. -/
inductive Role
  | Input | Output | Resource | Target | Constraint
  deriving DecidableEq, Repr, Fintype, Inhabited

/-! ## Ось C — уровень абстракции -/

/-- Ось C: уровень абстракции. -/
inductive Level
  | L0 | L1 | L2 | L3 | L4
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Числовой индекс уровня абстракции. -/
def Level.idx : Level → ℕ
  | .L0 => 0 | .L1 => 1 | .L2 => 2 | .L3 => 3 | .L4 => 4

/-- Индекс уровня инъективен: уровни различимы. -/
theorem Level.idx_injective : Function.Injective Level.idx := by
  decide

/-! ## Ось E — фаза жизненного цикла -/

/-- Ось E: фаза жизненного цикла ресурса. -/
inductive Phase
  | Created | Available | Consumed | Destroyed
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Фаза, в которой ресурс доступен для потребления. -/
def Phase.isUsable : Phase → Bool
  | .Available => true
  | _ => false

/-! ## Ось D — решётка типов -/

/-- Тип-метка (ось D).  Конкретный набор меток задаётся приложением, поэтому
здесь это просто строка, а структура оси D — в объявленной решётке. -/
abbrev TypeTag := String

/-- Решётка типов: список объявленных рёбер подтипизации. -/
structure TypeLattice where
  /-- Объявленные пары «подтип — надтип». -/
  edges : List (TypeTag × TypeTag)
  deriving Repr, Inhabited

namespace TypeLattice

variable (L : TypeLattice)

/-- Непосредственное объявленное отношение подтипа. -/
def Edge (a b : TypeTag) : Prop := (a, b) ∈ L.edges

/-- `IsSubtype` — рефлексивно-транзитивное замыкание объявленных рёбер. -/
def IsSubtype : TypeTag → TypeTag → Prop :=
  Relation.ReflTransGen L.Edge

/-- **LAW-001 (Type Reflexivity).** ∀ A ∈ T, A ⊑ A. -/
theorem isSubtype_refl (a : TypeTag) : L.IsSubtype a a :=
  Relation.ReflTransGen.refl

/-- **LAW-002 (Type Transitivity).** A ⊑ B ∧ B ⊑ C ⇒ A ⊑ C. -/
theorem isSubtype_trans {a b c : TypeTag}
    (hab : L.IsSubtype a b) (hbc : L.IsSubtype b c) : L.IsSubtype a c :=
  Relation.ReflTransGen.trans hab hbc

/-- Объявленное ребро — частный случай подтипизации. -/
theorem isSubtype_of_edge {a b : TypeTag} (h : L.Edge a b) : L.IsSubtype a b :=
  Relation.ReflTransGen.single h

/-- Подтипизация монотонна по расширению решётки: добавление объявлений
никогда не отменяет уже выведенных отношений. -/
theorem isSubtype_mono {L₁ L₂ : TypeLattice} (h : L₁.edges ⊆ L₂.edges)
    {a b : TypeTag} (hab : L₁.IsSubtype a b) : L₂.IsSubtype a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (h hstep)

/-- В пустой решётке подтипизация — это в точности равенство: ничего лишнего
не выводится. -/
theorem isSubtype_empty_iff {a b : TypeTag} :
    (TypeLattice.mk []).IsSubtype a b ↔ a = b := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hstep _ => exact absurd hstep (by simp [TypeLattice.Edge])
  · rintro rfl; exact Relation.ReflTransGen.refl

end TypeLattice

/-! ## Артефакт: точка в произведении осей -/

/-- Тип артефакта — точка в произведении пяти осей (ось D представлена
меткой типа, отношение на которой задаёт `TypeLattice`). -/
structure ArtifactType where
  /-- Ось A. -/
  category : Category
  /-- Ось B. -/
  role : Role
  /-- Ось C. -/
  level : Level
  /-- Ось D. -/
  typeTag : TypeTag
  /-- Ось E. -/
  phase : Phase
  deriving DecidableEq, Repr, Inhabited

/-- Оси A, B, C, E независимы: любая комбинация значений реализуется
артефактом.  Это и есть содержание «ортогональности» §3 — в отличие от
единой иерархии L0–L4, ни одна ось не ограничивает другие. -/
theorem axes_orthogonal (c : Category) (r : Role) (l : Level) (p : Phase)
    (t : TypeTag) :
    ∃ a : ArtifactType,
      a.category = c ∧ a.role = r ∧ a.level = l ∧ a.phase = p ∧ a.typeTag = t :=
  ⟨⟨c, r, l, t, p⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- Число комбинаций дискретных осей A × B × C × E равно 6 · 5 · 5 · 4 = 600. -/
theorem axes_card :
    Fintype.card (Category × Role × Level × Phase) = 600 := by
  decide

/-- Ни одна ось не определяется остальными: например, категория может
меняться при фиксированных роли, уровне, типе и фазе. -/
theorem category_not_determined (r : Role) (l : Level) (t : TypeTag) (p : Phase) :
    ∃ a b : ArtifactType,
      a.role = b.role ∧ a.level = b.level ∧ a.typeTag = b.typeTag ∧
        a.phase = b.phase ∧ a.category ≠ b.category :=
  ⟨⟨.Object, r, l, t, p⟩, ⟨.Meta, r, l, t, p⟩, rfl, rfl, rfl, rfl, by simp⟩

/-- Фаза не определяется остальными осями: тот же артефакт бывает доступным
и уничтоженным. -/
theorem phase_not_determined (c : Category) (r : Role) (l : Level) (t : TypeTag) :
    ∃ a b : ArtifactType,
      a.category = b.category ∧ a.role = b.role ∧ a.level = b.level ∧
        a.typeTag = b.typeTag ∧ a.phase ≠ b.phase :=
  ⟨⟨c, r, l, t, .Available⟩, ⟨c, r, l, t, .Destroyed⟩, rfl, rfl, rfl, rfl, by simp⟩

/-- Скачок по оси абстракции между двумя артефактами. -/
def levelGap (a b : ArtifactType) : ℕ :=
  max a.level.idx b.level.idx - min a.level.idx b.level.idx

/-- Прыжок L1 → L3 — это скачок величины 2, а не соседний переход. -/
theorem levelGap_L1_L3 (c : Category) (r : Role) (t : TypeTag) (p : Phase) :
    levelGap ⟨c, r, .L1, t, p⟩ ⟨c, r, .L3, t, p⟩ = 2 := rfl

end Polymath.OSA4
