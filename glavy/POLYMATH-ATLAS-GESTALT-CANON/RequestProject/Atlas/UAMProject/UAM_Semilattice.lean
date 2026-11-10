import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Inverse

namespace UAMP_Semilattice
universe u

open UAMP_Idempotent

variable {M : Type u} [Monoid M]

/-- Commutative monoid -/
def IsCommutative (M : Type u) [Monoid M] : Prop := ∀ a b : M, a * b = b * a

/-- Semilattice: commutative + all idempotent -/
def IsSemilattice (M : Type u) [Monoid M] : Prop :=
  IsCommutative M ∧ ∀ a : M, IsIdempotent a

/-- Meet operation in a semilattice (multiplication) -/
def semilattice_meet (a b : M) : M := a * b

/-- In a semilattice, every element is its own inverse semigroup inverse.
(В архивной версии единственность обратного не доказывалась; здесь доказана.) -/
theorem semilattice_inverse (h : IsSemilattice M) :
    UAMP_Inverse.IsInverseSemigroup M := by
  obtain ⟨hcomm, hidem⟩ := h
  intro a
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · rw [hidem a, hidem a]
  · rw [hidem a, hidem a]
  · rintro y ⟨hy1, hy2⟩
    -- y = y * a * y = y * y * a = y * a  и  a = a * y * a = a * a * y = a * y = y * a
    have hya : y * a = y := by
      calc y * a = (y * y) * a := by rw [hidem y]
        _ = y * (y * a) := by simp only [mul_assoc]
        _ = y * (a * y) := by rw [hcomm y a]
        _ = y * a * y := by simp only [mul_assoc]
        _ = y := hy2
    have hay : a * y = a := by
      calc a * y = (a * a) * y := by rw [hidem a]
        _ = a * (a * y) := by simp only [mul_assoc]
        _ = a * (y * a) := by rw [hcomm a y]
        _ = a * y * a := by simp only [mul_assoc]
        _ = a := hy1
    calc y = y * a := hya.symm
      _ = a * y := hcomm y a
      _ = a := hay

/-- Bool is a semilattice under AND.
Инстанс объявлен как `scoped`, чтобы не влиять на остальные модули проекта. -/
scoped instance : Monoid Bool where
  mul := fun a b => a && b
  one := true
  mul_assoc := fun _ _ _ => Bool.and_assoc _ _ _
  one_mul := fun _ => Bool.true_and _
  mul_one := fun _ => Bool.and_true _

theorem bool_isSemilattice : IsSemilattice Bool := by
  refine ⟨fun a b => Bool.and_comm a b, ?_⟩
  intro a
  show a * a = a
  cases a <;> rfl

/-- Unit is a semilattice (используется стандартный инстанс моноида на `Unit`). -/
theorem unit_isSemilattice : IsSemilattice Unit :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

end UAMP_Semilattice
