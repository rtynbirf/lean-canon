import Mathlib
import RequestProject.Atlas.UAM_MonoidAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_ActionCongruence

universe u

/-- An equivalence relation on states preserved by a monoid action. -/
@[ext]
structure ActionCongruence (M X : Type u) [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) where
  rel : X → X → Prop
  refl : ∀ x, rel x x
  symm : ∀ x y, rel x y → rel y x
  trans : ∀ x y z, rel x y → rel y z → rel x z
  invariant : ∀ m x y, rel x y → rel (A.act m x) (A.act m y)

/-- Unified constructor from an equivalence relation and action invariance. -/
def mkActionCongruence {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (r : X → X → Prop)
    (hEquiv : Equivalence r)
    (hInv : ∀ m x y, r x y → r (A.act m x) (A.act m y)) :
    ActionCongruence M X A where
  rel := r
  refl := fun x => hEquiv.refl x
  symm := fun _ _ h => hEquiv.symm h
  trans := fun _ _ _ hxy hyz => hEquiv.trans hxy hyz
  invariant := hInv

def actionCongruenceSetoid {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : ActionCongruence M X A) : Setoid X where
  r := C.rel
  iseqv := ⟨C.refl, fun h => C.symm _ _ h, fun h₁ h₂ => C.trans _ _ _ h₁ h₂⟩

/-- The state space modulo an action-invariant equivalence. -/
def ActionQuotient (M X : Type u) [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : ActionCongruence M X A) : Type u :=
  Quotient (actionCongruenceSetoid A C)

/-- Canonical projection to the state quotient. -/
def quotientProj {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : ActionCongruence M X A) (x : X) : ActionQuotient M X A C :=
  Quotient.mk (actionCongruenceSetoid A C) x

/-- The monoid action induced on equivalence classes. -/
def inducedAction {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : ActionCongruence M X A) :
    UAM_MonoidAction.MonoidAction M (ActionQuotient M X A C) where
  act m := Quotient.map (A.act m) (fun _ _ h => C.invariant m _ _ h)
  one_act := by
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    change Quotient.mk (actionCongruenceSetoid A C) (A.act 1 x) =
      Quotient.mk (actionCongruenceSetoid A C) x
    rw [UAM_MonoidAction.MonoidAction.act_one_apply]
  mul_act := by
    intro a b
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    change Quotient.mk (actionCongruenceSetoid A C) (A.act (a * b) x) =
      Quotient.mk (actionCongruenceSetoid A C) (A.act b (A.act a x))
    rw [UAM_MonoidAction.MonoidAction.act_mul_apply]

/-- The kernel relation of the quotient projection, equipped with the original
action invariance. -/
def quotientKernelCongruence {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : ActionCongruence M X A) : ActionCongruence M X A where
  rel x y := quotientProj A C x = quotientProj A C y
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  trans := fun _ _ _ hxy hyz => hxy.trans hyz
  invariant := by
    intro m x y hxy
    apply Quotient.sound
    exact C.invariant m x y (Quotient.exact hxy)

/-- The kernel of the quotient projection is exactly the action congruence
used to form the quotient. -/
theorem quotientKernelCongruence_eq {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : ActionCongruence M X A) :
    quotientKernelCongruence A C = C := by
  apply ActionCongruence.ext
  funext x y
  apply propext
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

/-- Pointwise form of the quotient-kernel theorem. -/
theorem quotientProj_eq_iff {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : ActionCongruence M X A) (x y : X) :
    quotientProj A C x = quotientProj A C y ↔ C.rel x y := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

/-- `C₁` refines `C₂` when every `C₁`-class is contained in a `C₂`-class. -/
def refines {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C₁ C₂ : ActionCongruence M X A) : Prop :=
  ∀ x y, C₁.rel x y → C₂.rel x y

theorem refines_refl {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (C : ActionCongruence M X A) :
    refines A C C := fun _ _ h => h

theorem refines_trans {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C₁ C₂ C₃ : ActionCongruence M X A)
    (h₁₂ : refines A C₁ C₂) (h₂₃ : refines A C₂ C₃) :
    refines A C₁ C₃ := fun x y h => h₂₃ x y (h₁₂ x y h)

/-- Intersection is the meet of two action congruences. -/
def actionCongruenceInf {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C₁ C₂ : ActionCongruence M X A) : ActionCongruence M X A where
  rel x y := C₁.rel x y ∧ C₂.rel x y
  refl x := ⟨C₁.refl x, C₂.refl x⟩
  symm x y h := ⟨C₁.symm x y h.1, C₂.symm x y h.2⟩
  trans x y z h₁ h₂ :=
    ⟨C₁.trans x y z h₁.1 h₂.1, C₂.trans x y z h₁.2 h₂.2⟩
  invariant m x y h :=
    ⟨C₁.invariant m x y h.1, C₂.invariant m x y h.2⟩

theorem inf_is_glb {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C₁ C₂ C₃ : ActionCongruence M X A) :
    refines A C₃ (actionCongruenceInf A C₁ C₂) ↔
      refines A C₃ C₁ ∧ refines A C₃ C₂ := by
  constructor
  · intro h
    exact ⟨fun x y hx => (h x y hx).1, fun x y hx => (h x y hx).2⟩
  · rintro ⟨h₁, h₂⟩ x y hx
    exact ⟨h₁ x y hx, h₂ x y hx⟩

/-- Reflexive and transitive state preorder data. -/
structure StatePreorder (X : Type u) where
  rel : X → X → Prop
  refl : ∀ x, rel x x
  trans : ∀ x y z, rel x y → rel y z → rel x z

/-- A symmetric state preorder is precisely equivalence-relation data. -/
structure StateEquivalence (X : Type u) extends StatePreorder X where
  symm : ∀ x y, rel x y → rel y x

/-- An action preserving a state preorder. -/
structure PreorderInvariant (M X : Type u) [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (E : StatePreorder X) where
  preserves : ∀ m x y, E.rel x y →
    E.rel (A.act m x) (A.act m y)

/-- An action congruence determines a state equivalence. -/
def toStateEquivalence {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (C : ActionCongruence M X A) :
    StateEquivalence X where
  rel := C.rel
  refl := C.refl
  trans := C.trans
  symm := C.symm

/-- Method-style form of `toStateEquivalence`. -/
def ActionCongruence.toStateEquivalence {M X : Type u} [Monoid M]
    {A : UAM_MonoidAction.MonoidAction M X} (C : ActionCongruence M X A) :
    StateEquivalence X := UAM_ActionCongruence.toStateEquivalence A C

/-- Its invariance data becomes a preorder invariant. -/
def ActionCongruence.toPreorderInvariant {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (C : ActionCongruence M X A) :
    PreorderInvariant M X A C.toStateEquivalence.toStatePreorder where
  preserves := C.invariant

end UAM_ActionCongruence
