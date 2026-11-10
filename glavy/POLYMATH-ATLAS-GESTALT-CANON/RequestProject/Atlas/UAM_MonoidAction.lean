import Mathlib.Tactic
import RequestProject.Atlas.UAM_Action
import RequestProject.Atlas.UAM_Morphism
import RequestProject.Atlas.UAM_Cayley
import RequestProject.Atlas.UAM_TransitionMonoid
import RequestProject.Atlas.UAM_Congruence

/-!
# UAM — Действия моноидов (Monoid Actions)

Формализация действия моноида `M` на множестве `X`. Порядок композиции согласован
с `UAM_Action` (`act (a * b) = act b ∘ act a`), поэтому действие — это в точности
моноидный морфизм `M → (X → X)`. Рассматриваются каноническое правое действие
моноида на себе, орбиты и стабилизаторы, а также связь с теоремой Кэли и ядром
действия (конгруэнцией).
-/

namespace UAM_MonoidAction
universe u

open UAM_Action UAM_Morphism UAM_Congruence

/-- Действие моноида `M` на множестве `X` (правое, в порядке `UAM_Action`). -/
structure MonoidAction (M : Type u) [Monoid M] (X : Type u) where
  /-- Функция действия. -/
  act : M → X → X
  /-- Единица действует тождественно. -/
  one_act : act 1 = id
  /-- Совместимость с умножением (порядок `UAM_Action`). -/
  mul_act : ∀ a b : M, act (a * b) = act b ∘ act a

namespace MonoidAction
variable {M : Type u} [Monoid M] {X : Type u}

@[simp] theorem act_one_apply (A : MonoidAction M X) (x : X) : A.act 1 x = x := by
  rw [A.one_act]; rfl

theorem act_mul_apply (A : MonoidAction M X) (a b : M) (x : X) :
    A.act (a * b) x = A.act b (A.act a x) := by
  rw [A.mul_act]; rfl

/-- Действие как моноидный морфизм `M → (X → X)` (в моноиде `UAM_Action`). -/
def toMorphism (A : MonoidAction M X) : MonoidMorphism M (X → X) where
  toFun := A.act
  map_mul := fun a b => by
    rw [A.mul_act]; rfl
  map_one := A.one_act

@[simp] theorem toMorphism_apply (A : MonoidAction M X) (a : M) :
    (A.toMorphism).toFun a = A.act a := rfl

/-! ### §1. Каноническое правое действие моноида на себе -/

/-- Каноническое правое действие: `act a x = x * a`. -/
def canonical (M : Type u) [Monoid M] : MonoidAction M M where
  act := fun a x => x * a
  one_act := by funext x; simp
  mul_act := fun a b => by funext x; simp [mul_assoc]

@[simp] theorem canonical_act (a x : M) : (canonical M).act a x = x * a := rfl

/-- Каноническое действие совпадает с правым регулярным представлением Кэли. -/
theorem canonical_eq_cayley (a x : M) :
    (canonical M).act a x = (UAM_Cayley.rho a).toFun x := rfl

/-! ### §2. Орбиты и стабилизаторы -/

/-- Орбита точки `x`: множество достижимых из неё состояний. -/
def orbit (A : MonoidAction M X) (x : X) : Set X := Set.range (fun a => A.act a x)

/-- Стабилизатор точки `x`: элементы, оставляющие её на месте. -/
def stabilizer (A : MonoidAction M X) (x : X) : Set M := {a | A.act a x = x}

/-- Точка лежит в своей орбите. -/
theorem mem_orbit_self (A : MonoidAction M X) (x : X) : x ∈ A.orbit x :=
  ⟨1, by simp⟩

/-- Единица лежит в стабилизаторе. -/
theorem one_mem_stabilizer (A : MonoidAction M X) (x : X) : (1 : M) ∈ A.stabilizer x := by
  show A.act 1 x = x
  simp

/-- Стабилизатор замкнут относительно умножения. -/
theorem mul_mem_stabilizer (A : MonoidAction M X) (x : X) {a b : M}
    (ha : a ∈ A.stabilizer x) (hb : b ∈ A.stabilizer x) :
    a * b ∈ A.stabilizer x := by
  show A.act (a * b) x = x
  rw [act_mul_apply]
  show A.act b (A.act a x) = x
  rw [show A.act a x = x from ha, show A.act b x = x from hb]

/-! ### §3. Ядро действия как конгруэнция -/

/-- Ядро действия — конгруэнция на `M` (совпадает с ядром морфизма `toMorphism`). -/
def actionKernel (A : MonoidAction M X) : IsCongruence M := (A.toMorphism).kernel

/-- Два элемента конгруэнтны по ядру действия тогда и только тогда, когда
    действуют одинаково на всех точках. -/
theorem actionKernel_iff (A : MonoidAction M X) (a b : M) :
    (A.actionKernel).r a b ↔ ∀ x, A.act a x = A.act b x := by
  constructor
  · intro h x; exact congrFun h x
  · intro h; funext x; exact h x

end MonoidAction
end UAM_MonoidAction
