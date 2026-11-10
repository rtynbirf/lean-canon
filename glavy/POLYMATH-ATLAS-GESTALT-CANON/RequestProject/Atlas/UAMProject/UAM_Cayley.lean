import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Group
import RequestProject.Atlas.UAMProject.UAM_Morphism

namespace UAMP_Cayley
universe u

open UAMP_Morphism UAMP_Group

/-- Right regular representation: Transform M = M → M with multiplication f * g = g ∘ f -/
structure Transform (M : Type u) where
  toFun : M → M

instance (M : Type u) [Monoid M] : Mul (Transform M) where
  mul f g := ⟨g.toFun ∘ f.toFun⟩

instance (M : Type u) [Monoid M] : One (Transform M) where
  one := ⟨id⟩

instance (M : Type u) [Monoid M] : Monoid (Transform M) where
  mul := (· * ·)
  one := 1
  mul_assoc := fun _ _ _ => rfl
  one_mul := fun _ => rfl
  mul_one := fun _ => rfl

/-- Right regular representation: ρ(a) = right multiplication by a -/
def rho {M : Type u} [Monoid M] : MonoidMorphism M (Transform M) where
  toFun := fun a => ⟨fun x => x * a⟩
  map_mul := fun a b => by
    show Transform.mk (fun x => x * (a * b)) = Transform.mk (fun x => (x * a) * b)
    exact congrArg Transform.mk (funext fun x => (mul_assoc x a b).symm)
  map_one := congrArg Transform.mk (funext fun x => mul_one x)

/-- Cayley's theorem: ρ is injective (M embeds into Transform M) -/
theorem cayley_embedding {M : Type u} [Monoid M] :
    Function.Injective (rho (M := M)).toFun := by
  intros a b h
  -- ρ(a) = ρ(b) means (fun x => x * a) = (fun x => x * b)
  -- Plug in x = 1: 1 * a = 1 * b, so a = b
  have h1 : (rho.toFun a).toFun 1 = (rho.toFun b).toFun 1 := by rw [h]
  have h2 : (1 : M) * a = 1 * b := h1
  rwa [one_mul, one_mul] at h2

/-- Left regular representation (anti-homomorphism) -/
def lambdaMap {M : Type u} [Monoid M] : M → Transform M :=
  fun a => ⟨fun x => a * x⟩

/-- lambdaMap is an anti-homomorphism: λ(a*b) = λ(b) ∘ λ(a) -/
theorem lambdaMap_antihom {M : Type u} [Monoid M] (a b : M) :
    lambdaMap (a * b) = (lambdaMap b) * (lambdaMap a) := by
  show Transform.mk (fun x => a * b * x) = Transform.mk (fun x => a * (b * x))
  exact congrArg Transform.mk (funext fun x => mul_assoc a b x)

end UAMP_Cayley
