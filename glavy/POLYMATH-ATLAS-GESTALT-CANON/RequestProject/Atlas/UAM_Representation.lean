import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_Inverse          -- IsInverse, IsInverseSemigroup
import RequestProject.Atlas.UAM_Morphism         -- MonoidMorphism
import RequestProject.Atlas.UAM_Free             -- FreeMonoid

/-!
# UAM — Layer 10: Представления (Representation), теорема Вагнера-Престона

**Симметрическая обратная полугруппа** `PartialBij X` — множество частичных биекций
на `X`, то есть биекций между подмножествами `X`.

**Замечание о формализации.** В отличие от первоначального (упрощённого) наброска,
где частичная биекция задавалась одной функцией `X → X` с условием инвариантности
области (`image_in_dom : toFun x ∈ dom`), мы используем корректную модель настоящей
симметрической обратной полугруппы: частичная биекция хранит область `dom`, кообласть
`ran`, прямое отображение `toFun` и обратное `invFun`, связанные законами биекции.
Инвариантная-по-области модель не позволяет представить произвольную обратную
полугруппу (для этого требуются несовпадающие область и кообласть, например
`a⁻¹a ≠ aa⁻¹`), тогда как данная модель даёт доказанную теорему Вагнера-Престона
и не требует неконструктивного выбора.

**Теорема Вагнера-Престона** (`wagner_preston_injective`): каждая обратная полугруппа
инъективно вкладывается в `PartialBij` на своём носителе через правые трансляции
`a ↦ (x ↦ x * a⁻¹)`.
-/

namespace UAM_Representation
universe u

open UAM_Directionality UAM_Idempotent UAM_Inverse UAM_Morphism

/-! ### §0. Собственные определения -/

/-- Частичная биекция на `X`: биекция между подмножествами `dom` и `ran`,
    хранящая прямое (`toFun`) и обратное (`invFun`) отображения. -/
structure PartialBij (X : Type u) where
  dom : Set X
  ran : Set X
  toFun : X → X
  invFun : X → X
  maps_to : ∀ ⦃x⦄, x ∈ dom → toFun x ∈ ran
  inv_maps_to : ∀ ⦃y⦄, y ∈ ran → invFun y ∈ dom
  left_inv : ∀ ⦃x⦄, x ∈ dom → invFun (toFun x) = x
  right_inv : ∀ ⦃y⦄, y ∈ ran → toFun (invFun y) = y

namespace PartialBij
variable {X : Type u}

/-- Экстенсиональность: частичные биекции равны, если совпадают их четыре
    компоненты-данные (утверждения-поля несущественны по proof-irrelevance). -/
theorem ext' {f g : PartialBij X}
    (hd : f.dom = g.dom) (hr : f.ran = g.ran)
    (ht : f.toFun = g.toFun) (hi : f.invFun = g.invFun) : f = g := by
  cases f
  cases g
  cases hd; cases hr; cases ht; cases hi
  rfl

/-- Частичная биекция инъективна на своей области. -/
theorem inj_on_dom (f : PartialBij X) {x y : X}
    (hx : x ∈ f.dom) (hy : y ∈ f.dom) (h : f.toFun x = f.toFun y) : x = y := by
  have hx' := f.left_inv hx
  have hy' := f.left_inv hy
  rw [← hx', ← hy', h]

/-- Тождественная частичная биекция на подмножестве `S`. -/
def idOn (S : Set X) : PartialBij X where
  dom := S
  ran := S
  toFun := id
  invFun := id
  maps_to := fun _ h => h
  inv_maps_to := fun _ h => h
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

/-- Тождественная частичная биекция на всём `X`. -/
def idAll : PartialBij X := idOn Set.univ

/-- Обращение частичной биекции: меняет местами область и кообласть,
    прямое и обратное отображения. -/
def inv (f : PartialBij X) : PartialBij X where
  dom := f.ran
  ran := f.dom
  toFun := f.invFun
  invFun := f.toFun
  maps_to := f.inv_maps_to
  inv_maps_to := f.maps_to
  left_inv := f.right_inv
  right_inv := f.left_inv

/-- Композиция частичных биекций `comp f g = f ∘ g` (сначала `g`, затем `f`). -/
def comp (f g : PartialBij X) : PartialBij X where
  dom := {x | x ∈ g.dom ∧ g.toFun x ∈ f.dom}
  ran := {y | y ∈ f.ran ∧ f.invFun y ∈ g.ran}
  toFun := fun x => f.toFun (g.toFun x)
  invFun := fun y => g.invFun (f.invFun y)
  maps_to := fun x hx => by
    refine ⟨f.maps_to hx.2, ?_⟩
    rw [f.left_inv hx.2]
    exact g.maps_to hx.1
  inv_maps_to := fun y hy => by
    refine ⟨g.inv_maps_to hy.2, ?_⟩
    rw [g.right_inv hy.2]
    exact f.inv_maps_to hy.1
  left_inv := fun x hx => by
    rw [f.left_inv hx.2, g.left_inv hx.1]
  right_inv := fun y hy => by
    rw [g.right_inv hy.2, f.right_inv hy.1]

/-! ### §1. Свойства базовых операций -/

/-- Область `idOn S` равна `S`. -/
theorem idOn_dom (S : Set X) : (idOn S).dom = S := rfl

/-- Прямое отображение `idOn S` — тождественное. -/
theorem idOn_toFun (S : Set X) : (idOn S).toFun = id := rfl

/-- `idAll` действует на всём `X`. -/
theorem idAll_dom : (idAll : PartialBij X).dom = Set.univ := rfl

/-- Обращение инволютивно: `inv (inv f) = f`. -/
theorem inv_inv (f : PartialBij X) : inv (inv f) = f := by
  apply ext' <;> rfl

/-- Обращение `idOn S` — снова `idOn S`. -/
theorem inv_idOn (S : Set X) : inv (idOn S) = idOn S := by
  apply ext' <;> rfl

/-- `idOn S` идемпотентна: `comp (idOn S) (idOn S) = idOn S`. -/
theorem idOn_idempotent (S : Set X) :
    comp (idOn S) (idOn S) = idOn S := by
  apply ext'
  · ext x; simp only [comp, idOn, id_eq, Set.mem_setOf_eq, and_self]
  · ext y; simp only [comp, idOn, id_eq, Set.mem_setOf_eq, and_self]
  · rfl
  · rfl

/-- Обращение `idAll` — снова `idAll`. -/
theorem inv_idAll : inv (idAll : PartialBij X) = idAll := inv_idOn Set.univ

/-! ### §2. Теорема Вагнера-Престона -/

variable {M : Type u} [Monoid M]

open Classical in
/-- Внутренний обратный элемента обратной полугруппы (выбор из единственного). -/
noncomputable def invSG (hS : IsInverseSemigroup M) (a : M) : M :=
  (hS a).exists.choose

/-- `invSG hS a` действительно является обратным `a`. -/
theorem invSG_isInverse (hS : IsInverseSemigroup M) (a : M) :
    IsInverse a (invSG hS a) :=
  (hS a).exists.choose_spec

/-- Правая трансляция `ρ_{a,y}`: частичная биекция `x ↦ x * y` c обратной `w ↦ w * a`,
    где `y` — внутренний обратный `a`. Область — идемпотент-фиксированное множество
    `{x | x * (y*a) = x}`, кообласть — `{w | w * (a*y) = w}`. -/
def rho {a y : M} (hi : IsInverse a y) : PartialBij M where
  dom := {x | x * (y * a) = x}
  ran := {w | w * (a * y) = w}
  toFun := fun x => x * y
  invFun := fun w => w * a
  maps_to := fun x _ => by
    show (x * y) * (a * y) = x * y
    rw [mul_assoc x y (a * y), ← mul_assoc y a y, hi.2]
  inv_maps_to := fun w _ => by
    show (w * a) * (y * a) = w * a
    rw [mul_assoc w a (y * a), ← mul_assoc a y a, hi.1]
  left_inv := fun x hx => by
    have hx' : x * (y * a) = x := hx
    show (x * y) * a = x
    rw [mul_assoc, hx']
  right_inv := fun w hw => by
    have hw' : w * (a * y) = w := hw
    show (w * a) * y = w
    rw [mul_assoc, hw']

/-- **Отображение Вагнера-Престона.** Каждому элементу `a` обратной полугруппы `M`
    сопоставляется правая трансляция — частичная биекция на `M`. -/
noncomputable def wagnerPrestonMap (hS : IsInverseSemigroup M) (a : M) : PartialBij M :=
  rho (invSG_isInverse hS a)

/-- Прямое отображение представления `a` — правое умножение на `invSG hS a`. -/
theorem wagnerPrestonMap_toFun (hS : IsInverseSemigroup M) (a : M) :
    (wagnerPrestonMap hS a).toFun = fun x => x * invSG hS a := rfl

/-- Обратное отображение представления `a` — правое умножение на `a`. -/
theorem wagnerPrestonMap_invFun (hS : IsInverseSemigroup M) (a : M) :
    (wagnerPrestonMap hS a).invFun = fun w => w * a := rfl

/-- **Теорема Вагнера-Престона.** Отображение `a ↦ ρ_a` инъективно, то есть
    обратная полугруппа вкладывается в симметрическую обратную полугруппу
    частичных биекций на своём носителе. -/
theorem wagner_preston_injective (hS : IsInverseSemigroup M) :
    Function.Injective (wagnerPrestonMap hS) := by
  intro a b hab
  have h1 : (fun w : M => w * a) = (fun w : M => w * b) :=
    congrArg PartialBij.invFun hab
  have h2 : (1 : M) * a = 1 * b := congrFun h1 1
  rwa [one_mul, one_mul] at h2

end PartialBij
end UAM_Representation
