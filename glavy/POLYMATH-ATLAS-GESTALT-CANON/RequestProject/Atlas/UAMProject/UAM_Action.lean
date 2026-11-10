import Mathlib.Tactic

namespace UAMP_Action
universe u

/-- Monoid instance on Q → Q with composition order f * g = g ∘ f -/
instance instMonoid {Q : Type u} : Monoid (Q → Q) where
  mul f g := g ∘ f
  one := id
  mul_assoc := fun _ _ _ => rfl
  one_mul := fun _ => rfl
  mul_one := fun _ => rfl

end UAMP_Action
