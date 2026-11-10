/-
# OSA-4.0 — пять пространств артефакта как индексированное семейство

Модуль формализует §3 кодекса OSA-4.0 («5 ортогональных осей») в виде,
пригодном для формальной верификации: пять пространств заданы одним
индексированным семейством `Axis.Carrier`, координатное отображение —
функцией `Axis.proj`, а утверждение «оси ортогональны» — не описанием,
а теоремами:

* `artifactEquivCoords` — пространство артефактов *есть* зависимое
  произведение носителей пяти осей (биекция, а не аналогия);
* `coord_independent` — любая координата изменяется независимо от остальных;
* `axis_not_determined` — ни одна ось не является функцией остальных;
* `axis_card` — осей ровно пять.

Термин «ортогональность», использованный в источнике без определения,
определён здесь как `Orthogonal` (предикат первого порядка) и доказан
для пространства артефактов (`artifact_orthogonal`).
-/
import RequestProject.OSA4.Axes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-! ## Индекс пространства -/

/-- Индекс пространства (оси) OSA-4.0.  Ровно пять значений. -/
inductive Axis
  /-- Пространство A: категория. -/
  | A
  /-- Пространство B: роль. -/
  | B
  /-- Пространство C: уровень абстракции. -/
  | C
  /-- Пространство D: тип. -/
  | D
  /-- Пространство E: фаза жизненного цикла. -/
  | E
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Носитель пространства. -/
def Axis.Carrier : Axis → Type
  | .A => Category
  | .B => Role
  | .C => Level
  | .D => TypeTag
  | .E => Phase

instance (a : Axis) : DecidableEq a.Carrier := by
  cases a <;> (show DecidableEq _; unfold Axis.Carrier; infer_instance)

instance (a : Axis) : Inhabited a.Carrier := by
  cases a <;> (show Inhabited _; unfold Axis.Carrier; infer_instance)

/-- Координата артефакта в заданном пространстве. -/
def Axis.proj : (a : Axis) → ArtifactType → a.Carrier
  | .A, x => x.category
  | .B, x => x.role
  | .C, x => x.level
  | .D, x => x.typeTag
  | .E, x => x.phase

/-- Артефакт, собранный из набора координат. -/
def ofCoords (c : (a : Axis) → a.Carrier) : ArtifactType :=
  ⟨c .A, c .B, c .C, c .D, c .E⟩

@[simp] theorem proj_ofCoords (c : (a : Axis) → a.Carrier) (a : Axis) :
    a.proj (ofCoords c) = c a := by
  cases a <;> rfl

@[simp] theorem ofCoords_proj (x : ArtifactType) : ofCoords (fun a => a.proj x) = x := rfl

/-- Артефакт определяется своими пятью координатами. -/
theorem artifact_ext {x y : ArtifactType} (h : ∀ a : Axis, a.proj x = a.proj y) : x = y := by
  have hx : ofCoords (fun a => a.proj x) = ofCoords (fun a => a.proj y) := by
    exact congrArg ofCoords (funext h)
  simpa using hx

/-- **Пространство артефактов есть произведение пяти пространств.**
Формальное содержание §3: биекция между артефактами и наборами координат. -/
def artifactEquivCoords : ArtifactType ≃ ((a : Axis) → a.Carrier) where
  toFun x a := a.proj x
  invFun := ofCoords
  left_inv _ := rfl
  right_inv c := funext (proj_ofCoords c)

/-- Пространств ровно пять. -/
theorem axis_card : Fintype.card Axis = 5 := by decide

/-! ## Ортогональность как предикат -/

/-- **Определение.**  Семейство координатных отображений `p` ортогонально на
типе `X`, если любую координату можно изменить произвольно, не изменив
остальных. -/
def Orthogonal {I : Type} {X : Type} {C : I → Type} [DecidableEq I]
    (p : (i : I) → X → C i) : Prop :=
  ∀ (x : X) (i : I) (v : C i), ∃ y : X, p i y = v ∧ ∀ j : I, j ≠ i → p j y = p j x

/-- Любая координата артефакта изменяется независимо от остальных. -/
theorem coord_independent (x : ArtifactType) (a : Axis) (v : a.Carrier) :
    ∃ y : ArtifactType, a.proj y = v ∧ ∀ b : Axis, b ≠ a → b.proj y = b.proj x := by
  cases a with
  | A =>
      refine ⟨⟨v, x.role, x.level, x.typeTag, x.phase⟩, rfl, ?_⟩
      intro b hb; cases b <;> first | rfl | exact absurd rfl hb
  | B =>
      refine ⟨⟨x.category, v, x.level, x.typeTag, x.phase⟩, rfl, ?_⟩
      intro b hb; cases b <;> first | rfl | exact absurd rfl hb
  | C =>
      refine ⟨⟨x.category, x.role, v, x.typeTag, x.phase⟩, rfl, ?_⟩
      intro b hb; cases b <;> first | rfl | exact absurd rfl hb
  | D =>
      refine ⟨⟨x.category, x.role, x.level, v, x.phase⟩, rfl, ?_⟩
      intro b hb; cases b <;> first | rfl | exact absurd rfl hb
  | E =>
      refine ⟨⟨x.category, x.role, x.level, x.typeTag, v⟩, rfl, ?_⟩
      intro b hb; cases b <;> first | rfl | exact absurd rfl hb

/-- **Оси OSA-4.0 ортогональны** в смысле определения `Orthogonal`. -/
theorem artifact_orthogonal : Orthogonal Axis.proj :=
  fun x a v => coord_independent x a v

/-- Ни одно пространство не является функцией остальных: если в его носителе
есть два различных значения, существуют два артефакта, совпадающие по всем
прочим координатам и различающиеся по данной. -/
theorem axis_not_determined (a : Axis) {u v : a.Carrier} (huv : u ≠ v) (x : ArtifactType) :
    ∃ y z : ArtifactType,
      (∀ b : Axis, b ≠ a → b.proj y = b.proj x ∧ b.proj z = b.proj x) ∧
        a.proj y ≠ a.proj z := by
  obtain ⟨y, hy, hy'⟩ := coord_independent x a u
  obtain ⟨z, hz, hz'⟩ := coord_independent x a v
  refine ⟨y, z, fun b hb => ⟨hy' b hb, hz' b hb⟩, ?_⟩
  rw [hy, hz]; exact huv

/-- Носители четырёх пространств конечны, их произведение содержит 600 точек
(6 · 5 · 5 · 4); пятое пространство (ось D, метки типов) бесконечно. -/
theorem discrete_axes_card : Fintype.card (Category × Role × Level × Phase) = 600 :=
  axes_card

/-- Носитель оси D бесконечен: множество меток типов не ограничено. -/
theorem typeTag_infinite : Infinite TypeTag := inferInstanceAs (Infinite String)

end Polymath.OSA4
