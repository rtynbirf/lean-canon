import Mathlib
import RequestProject.Atlas.UAM_MonoidAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_StateCongruence

universe u

/-- An equivalence relation on states preserved by a monoid action. -/
@[ext]
structure StateCongruence (M X : Type u) [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) where
  rel : X → X → Prop
  refl : ∀ x, rel x x
  symm : ∀ x y, rel x y → rel y x
  trans : ∀ x y z, rel x y → rel y z → rel x z
  invariant : ∀ m x y, rel x y → rel (A.act m x) (A.act m y)

/-- Unified constructor from an equivalence relation and action invariance. -/
def mkStateCongruence {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (r : X → X → Prop)
    (hEquiv : Equivalence r)
    (hInv : ∀ m x y, r x y → r (A.act m x) (A.act m y)) :
    StateCongruence M X A where
  rel := r
  refl := fun x => hEquiv.refl x
  symm := fun _ _ h => hEquiv.symm h
  trans := fun _ _ _ hxy hyz => hEquiv.trans hxy hyz
  invariant := hInv

def stateCongruenceSetoid {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : StateCongruence M X A) : Setoid X where
  r := C.rel
  iseqv := ⟨C.refl, fun h => C.symm _ _ h, fun h₁ h₂ => C.trans _ _ _ h₁ h₂⟩

/-- The state space modulo an action-invariant equivalence. -/
def StateQuotient (M X : Type u) [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : StateCongruence M X A) : Type u :=
  Quotient (stateCongruenceSetoid A C)

/-- Canonical projection to the state quotient. -/
def quotientMap {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : StateCongruence M X A) (x : X) : StateQuotient M X A C :=
  Quotient.mk (stateCongruenceSetoid A C) x

/-- The monoid action induced on equivalence classes. -/
def inducedAction {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C : StateCongruence M X A) :
    UAM_MonoidAction.MonoidAction M (StateQuotient M X A C) where
  act m := Quotient.map (A.act m) (fun _ _ h => C.invariant m _ _ h)
  one_act := by
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    change Quotient.mk (stateCongruenceSetoid A C) (A.act 1 x) =
      Quotient.mk (stateCongruenceSetoid A C) x
    rw [UAM_MonoidAction.MonoidAction.act_one_apply]
  mul_act := by
    intro a b
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    change Quotient.mk (stateCongruenceSetoid A C) (A.act (a * b) x) =
      Quotient.mk (stateCongruenceSetoid A C) (A.act b (A.act a x))
    rw [UAM_MonoidAction.MonoidAction.act_mul_apply]

/-- `C₁` refines `C₂` when every `C₁`-class is contained in a `C₂`-class. -/
def refinesCongruence {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C₁ C₂ : StateCongruence M X A) : Prop :=
  ∀ x y, C₁.rel x y → C₂.rel x y

theorem refinesCongruence_refl {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (C : StateCongruence M X A) :
    refinesCongruence A C C := fun _ _ h => h

theorem refinesCongruence_trans {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C₁ C₂ C₃ : StateCongruence M X A)
    (h₁₂ : refinesCongruence A C₁ C₂) (h₂₃ : refinesCongruence A C₂ C₃) :
    refinesCongruence A C₁ C₃ := fun x y h => h₂₃ x y (h₁₂ x y h)

/-- Intersection is the meet of two state congruences. -/
def stateCongruence_inter {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C₁ C₂ : StateCongruence M X A) : StateCongruence M X A where
  rel x y := C₁.rel x y ∧ C₂.rel x y
  refl x := ⟨C₁.refl x, C₂.refl x⟩
  symm x y h := ⟨C₁.symm x y h.1, C₂.symm x y h.2⟩
  trans x y z h₁ h₂ :=
    ⟨C₁.trans x y z h₁.1 h₂.1, C₂.trans x y z h₁.2 h₂.2⟩
  invariant m x y h :=
    ⟨C₁.invariant m x y h.1, C₂.invariant m x y h.2⟩

theorem inter_is_inf {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X)
    (C₁ C₂ C₃ : StateCongruence M X A) :
    refinesCongruence A C₃ (stateCongruence_inter A C₁ C₂) ↔
      refinesCongruence A C₃ C₁ ∧ refinesCongruence A C₃ C₂ := by
  constructor
  · intro h
    exact ⟨fun x y hx => (h x y hx).1, fun x y hx => (h x y hx).2⟩
  · rintro ⟨h₁, h₂⟩ x y hx
    exact ⟨h₁ x y hx, h₂ x y hx⟩

/-- Reflexive and transitive empathy data. -/
structure EmpathyModel (X : Type u) where
  resonatesWith : X → X → Prop
  refl : ∀ x, resonatesWith x x
  trans : ∀ x y z, resonatesWith x y → resonatesWith y z → resonatesWith x z

/-- Symmetric empathy is precisely equivalence-relation data. -/
structure SymmetricEmpathy (X : Type u) extends EmpathyModel X where
  symm : ∀ x y, resonatesWith x y → resonatesWith y x

/-- An action preserving empathy. -/
structure EmpathicAction (M X : Type u) [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (E : EmpathyModel X) where
  preserves : ∀ m x y, E.resonatesWith x y →
    E.resonatesWith (A.act m x) (A.act m y)

/-- A state congruence determines symmetric empathy. -/
def stateCongruenceToSymmetricEmpathy {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (C : StateCongruence M X A) :
    SymmetricEmpathy X where
  resonatesWith := C.rel
  refl := C.refl
  trans := C.trans
  symm := C.symm

/-- Method-style form of `stateCongruenceToSymmetricEmpathy`. -/
def StateCongruence.toSymmetricEmpathy {M X : Type u} [Monoid M]
    {A : UAM_MonoidAction.MonoidAction M X} (C : StateCongruence M X A) :
    SymmetricEmpathy X := stateCongruenceToSymmetricEmpathy A C

/-- Its invariance data becomes an empathic action. -/
def StateCongruence.toEmpathicAction {M X : Type u} [Monoid M]
    (A : UAM_MonoidAction.MonoidAction M X) (C : StateCongruence M X A) :
    EmpathicAction M X A C.toSymmetricEmpathy.toEmpathyModel where
  preserves := C.invariant

end UAM_StateCongruence
