import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Group
import RequestProject.Atlas.UAMProject.UAM_Submonoid

namespace UAMP_Center
universe u

open UAMP_Group

variable {M : Type u} [Monoid M]

/-- a is central: commutes with every element -/
def IsCentral (a : M) : Prop := ∀ x, a * x = x * a

/-- One is central -/
theorem one_central : IsCentral (1 : M) := by
  intro x
  rw [one_mul, mul_one]

/-- Product of centrals is central -/
theorem mul_central {a b : M} (ha : IsCentral a) (hb : IsCentral b) : IsCentral (a * b) := by
  intro x
  calc a * b * x = a * (b * x) := by rw [mul_assoc]
    _ = a * (x * b) := by rw [hb x]
    _ = (a * x) * b := by rw [mul_assoc]
    _ = (x * a) * b := by rw [ha x]
    _ = x * (a * b) := by rw [mul_assoc]

/-- Center of M: all central elements -/
def center (M : Type u) [Monoid M] : UAMP_Submonoid.Submonoid M where
  carrier := {a | IsCentral a}
  one_mem := one_central
  mul_mem := fun _ _ ha hb => mul_central ha hb

/-- Centralizer of a subset: elements commuting with everything in subset -/
def centralizer (s : Set M) : UAMP_Submonoid.Submonoid M where
  carrier := {a | ∀ x ∈ s, a * x = x * a}
  one_mem := by
    intro x _
    rw [one_mul, mul_one]
  mul_mem := by
    intro a b ha hb x hx
    calc a * b * x = a * (b * x) := by rw [mul_assoc]
      _ = a * (x * b) := by rw [hb x hx]
      _ = (a * x) * b := by rw [mul_assoc]
      _ = (x * a) * b := by rw [ha x hx]
      _ = x * (a * b) := by rw [mul_assoc]

/-- Power of central is central -/
theorem pow_central {a : M} (ha : IsCentral a) (n : Nat) : IsCentral (a ^ n) := by
  induction n with
  | zero =>
    intro x
    rw [pow_zero, one_mul, mul_one]
  | succ k ih =>
    intro x
    rw [pow_succ]
    exact mul_central ih ha x

/-- Centralizer is antitone: larger subset, smaller centralizer -/
theorem centralizer_antitone {s t : Set M} (h : s ⊆ t) :
    (centralizer t).carrier ⊆ (centralizer s).carrier := by
  intro a ha x hx
  exact ha x (h hx)

/-- Center equals centralizer of universal set -/
theorem center_eq_centralizer_univ :
    (center M).carrier = (centralizer (Set.univ : Set M)).carrier := by
  ext a
  constructor
  · intro ha x _
    exact ha x
  · intro ha x
    exact ha x (Set.mem_univ _)

/-- Commutative monoid has central everything -/
theorem central_of_comm {a : M} (hcomm : ∀ x y : M, x * y = y * x) : IsCentral a :=
  fun x => hcomm a x

/-- Center is the whole monoid iff M is commutative -/
theorem center_eq_top_of_comm (hcomm : ∀ x y : M, x * y = y * x) :
    (center M).carrier = (Set.univ : Set M) := by
  ext a
  exact ⟨fun _ => Set.mem_univ _, fun _ x => hcomm a x⟩

/-- Обратный к центральному обратимому элементу централен.
(Архивная версия ссылалась на несуществующее поле `IsUnit'.exists` и обрывалось незавершённым.) -/
theorem inv_central {a b : M} (hb : a * b = 1 ∧ b * a = 1) (hcent : IsCentral a) :
    IsCentral b := by
  intro x
  calc b * x = b * x * (a * b) := by rw [hb.1, mul_one]
    _ = b * (x * a) * b := by simp only [mul_assoc]
    _ = b * (a * x) * b := by rw [hcent x]
    _ = (b * a) * x * b := by simp only [mul_assoc]
    _ = x * b := by rw [hb.2, one_mul]

end UAMP_Center
