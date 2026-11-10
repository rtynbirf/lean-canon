import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Green
import RequestProject.Atlas.UAMProject.UAM_Idempotent

namespace UAMP_Congruence
universe u

/-- A congruence on a monoid: an equivalence relation compatible with multiplication -/
structure IsCongruence (M : Type u) [Monoid M] where
  r : M → M → Prop
  refl : ∀ a, r a a
  symm : ∀ a b, r a b → r b a
  trans : ∀ a b c, r a b → r b c → r a c
  mul_compat : ∀ a b c d, r a b → r c d → r (a * c) (b * d)
  one_compat : r 1 1

variable {M : Type u} [Monoid M] (θ : IsCongruence M)

/-- Convert a congruence to a Setoid -/
def congruenceSetoid : Setoid M where
  r := θ.r
  iseqv := ⟨θ.refl, fun {a b} h => θ.symm a b h, fun {a b c} h₁ h₂ => θ.trans a b c h₁ h₂⟩

/-- The quotient monoid by a congruence -/
abbrev QuotientMonoid : Type u := Quotient (congruenceSetoid θ)

instance : Monoid (QuotientMonoid θ) where
  mul := Quotient.map₂ (· * ·) (fun a b hab c d hcd => θ.mul_compat a b c d hab hcd)
  one := Quotient.mk _ 1
  mul_assoc := fun x y z => Quotient.inductionOn₃ x y z (fun a b c => by
    show Quotient.mk (congruenceSetoid θ) (a * b * c)
        = Quotient.mk (congruenceSetoid θ) (a * (b * c))
    rw [mul_assoc])
  one_mul := fun x => Quotient.inductionOn x (fun a => by
    show Quotient.mk (congruenceSetoid θ) (1 * a) = Quotient.mk (congruenceSetoid θ) a
    rw [one_mul])
  mul_one := fun x => Quotient.inductionOn x (fun a => by
    show Quotient.mk (congruenceSetoid θ) (a * 1) = Quotient.mk (congruenceSetoid θ) a
    rw [mul_one])

/-- Construction of quotient element -/
def mk (a : M) : QuotientMonoid θ := Quotient.mk _ a

theorem mk_mul (a b : M) : mk θ (a * b) = mk θ a * mk θ b := rfl

theorem mk_one : mk θ (1 : M) = 1 := rfl

theorem mk_surjective : Function.Surjective (mk θ) :=
  fun q => Quotient.inductionOn q (fun a => ⟨a, rfl⟩)

theorem mk_eq_iff {a b : M} : mk θ a = mk θ b ↔ θ.r a b := Quotient.eq

/-- Trivial congruence: equality -/
def trivialCongruence : IsCongruence M where
  r := (· = ·)
  refl := fun _ => rfl
  symm := fun _ _ => Eq.symm
  trans := fun _ _ _ hab hbc => hab.trans hbc
  mul_compat := fun _ _ _ _ hab hcd => by rw [hab, hcd]
  one_compat := rfl

/-- Universal congruence: everything is related -/
def universal : IsCongruence M where
  r := fun _ _ => True
  refl := fun _ => True.intro
  symm := fun _ _ _ => True.intro
  trans := fun _ _ _ _ _ => True.intro
  mul_compat := fun _ _ _ _ _ _ => True.intro
  one_compat := True.intro

/-- Congruences are compatible with powers -/
theorem congruence_pow_compat (a b : M) (n : Nat) (hab : θ.r a b) :
    θ.r (a ^ n) (b ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact θ.one_compat
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact θ.mul_compat _ _ _ _ ih hab

end UAMP_Congruence
