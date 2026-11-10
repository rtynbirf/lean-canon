import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Action
import RequestProject.Atlas.UAMProject.UAM_Morphism
import RequestProject.Atlas.UAMProject.UAM_Cayley
import RequestProject.Atlas.UAMProject.UAM_TransitionMonoid
import RequestProject.Atlas.UAMProject.UAM_Congruence
import RequestProject.Atlas.UAMProject.UAM_Submonoid

namespace UAMP_MonoidAction
universe u

open UAMP_Morphism UAMP_Cayley UAMP_Congruence

/-- Monoid action of M on X (with UAMP_Action composition order) -/
structure MonoidAction (M : Type u) [Monoid M] (X : Type u) where
  act : M → X → X
  one_act : act 1 = id
  mul_act : ∀ a b, act (a * b) = act b ∘ act a

/-- Canonical right action of M on itself -/
def canonicalAction {M : Type u} [Monoid M] : MonoidAction M M where
  act := fun a x => x * a
  one_act := by
    funext x
    exact mul_one x
  mul_act := fun a b => by
    funext x
    exact (mul_assoc x a b).symm

/-- Orbit of x under action ρ -/
def orbit {M : Type u} [Monoid M] {X : Type u} (ρ : MonoidAction M X) (x : X) : Set X :=
  {y | ∃ a, ρ.act a x = y}

/-- Stabilizer of x under action ρ -/
def stabilizer {M : Type u} [Monoid M] {X : Type u} (ρ : MonoidAction M X) (x : X) : Set M :=
  {a | ρ.act a x = x}

/-- Stabilizer is a submonoid -/
def stabilizerSubmonoid {M : Type u} [Monoid M] {X : Type u} (ρ : MonoidAction M X) (x : X) :
    UAMP_Submonoid.Submonoid M where
  carrier := stabilizer ρ x
  one_mem := by
    show ρ.act 1 x = x
    rw [ρ.one_act]
    rfl
  mul_mem := by
    intro a b ha hb
    show ρ.act (a * b) x = x
    rw [ρ.mul_act]
    show ρ.act b (ρ.act a x) = x
    rw [ha, hb]

/- Архивное утверждение

theorem orbit_stabilizer (ρ : MonoidAction M X) [Fintype M] [Fintype X] (x : X) :
    Fintype.card M = Fintype.card (orbit ρ x) * Fintype.card (stabilizer ρ x)

неверно для моноидов: теорема об орбите и стабилизаторе опирается на групповую
структуру (обратимость), а стабилизатор моноидного действия — лишь подмоноид.
Например, для моноида `M = {1, z}` с нулём `z`, действующего на себе справа,
орбита элемента `1` есть `{1, z}`, стабилизатор `1` есть `{1}`,
и `2 = 2 * 1` выполняется, но уже для орбиты элемента `z` получаем
`|орбита| = 1`, `|стабилизатор| = 2`, то есть `2 ≠ 1 * 2` не даёт общего равенства
для всех точек. Утверждение не воспроизводится. -/

/-- Конгруэнция «неразличимости слева»: `x ~ y` тогда и только тогда, когда
`z * x = z * y` для всех `z`. -/
def leftIndistinguishable (M : Type u) [Monoid M] : IsCongruence M where
  r := fun x y => ∀ z : M, z * x = z * y
  refl := fun _ _ => rfl
  symm := fun _ _ h z => (h z).symm
  trans := fun _ _ _ hab hbc z => (hab z).trans (hbc z)
  mul_compat := fun a b c d hab hcd z => by
    calc z * (a * c) = (z * a) * c := by rw [mul_assoc]
      _ = (z * b) * c := by rw [hab z]
      _ = (z * b) * d := hcd (z * b)
      _ = z * (b * d) := by rw [mul_assoc]
  one_compat := fun _ => rfl

/-- Transition monoid as quotient of M by kernel of canonical action
(в архиве доказательство отсутствовало). -/
theorem transitionMonoid_as_quotient {M : Type u} [Monoid M] :
    ∃ θ : IsCongruence M, ∀ x y, θ.r x y ↔ ∀ z : M, z * x = z * y :=
  ⟨leftIndistinguishable M, fun _ _ => Iff.rfl⟩

/-- Connection with Cayley: right regular representation is canonical action.
(Архивная формулировка сравнивала объекты разных типов; здесь сравниваются
соответствующие функции.) -/
theorem cayley_is_canonical {M : Type u} [Monoid M] :
    (fun a : M => (rho.toFun a).toFun) = (canonicalAction (M := M)).act := rfl

end UAMP_MonoidAction
