import Mathlib
import RequestProject.Atlas.UAMTransfer.Transferability

/-!
# UAM — The category `Dyn` of dynamical systems

An object of `Dyn` is a *discrete dynamical system* `(K, F)` consisting of a
carrier type `K` and a self-map `F : K → K`. A morphism `(K, F) ⟶ (L, G)` is an
**equivariant** map `f : K → L`, i.e. one intertwining the dynamics:
`f ∘ F = G ∘ f`.

We then relate the transferability calculus to categorical **naturality**: a
uniform family of dynamic properties is invariant under change of coordinates iff
it is transferable along every conjugation. Finally we distinguish **structural**
transport (conjugation, `conj`) from **semantic** transport (any property-carrying
map).
-/

namespace UAMTransfer

open Function CategoryTheory

universe u

/-! ## Objects and morphisms of `Dyn` -/

/-- An object of the category of dynamical systems: a carrier with a self-map. -/
structure DynObj where
  /-- The state space. -/
  carrier : Type u
  /-- The one-step evolution map. -/
  map : carrier → carrier

/-- An equivariant map between dynamical systems (a morphism of `Dyn`). -/
@[ext]
structure DynHom (A B : DynObj.{u}) where
  /-- The underlying map of states. -/
  toFun : A.carrier → B.carrier
  /-- Equivariance: the map intertwines the two dynamics. -/
  equivariant : ∀ x, toFun (A.map x) = B.map (toFun x)

/-- The category `Dyn` of discrete dynamical systems and equivariant maps. -/
instance : Category DynObj.{u} where
  Hom A B := DynHom A B
  id A := ⟨id, fun _ => rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun x => by
    simp only [Function.comp_apply, f.equivariant, g.equivariant]⟩
  id_comp _ := by apply DynHom.ext; rfl
  comp_id _ := by apply DynHom.ext; rfl
  assoc _ _ _ := by apply DynHom.ext; rfl

@[simp] theorem DynHom.id_toFun (A : DynObj.{u}) :
    (𝟙 A : DynHom A A).toFun = id := rfl

@[simp] theorem DynHom.comp_toFun {A B C : DynObj.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

/-! ## Conjugation and isomorphisms

An isomorphism of dynamical systems is exactly an equivariant bijection, and
equivariance for a bijection `φ` says precisely that `G = conj φ F`. -/

/-- Conjugation is idempotent under inversion: `conj φ⁻¹ ∘ conj φ = id`. -/
theorem conj_conj_symm {K X : Type*} (phi : K ≃ X) (F : K → K) :
    conj phi.symm (conj phi F) = F := by
  ext x; simp [conj]

theorem conj_symm_conj {K X : Type*} (phi : K ≃ X) (G : X → X) :
    conj phi (conj phi.symm G) = G := by
  ext x; simp [conj]

/-! ## Property families and naturality -/

/-- A **uniform family of dynamic properties**: one dynamic property per carrier
type. -/
def PropFamily := ∀ K : Type u, DynamicProperty K

/-- A property family is **natural** if it is invariant under any change of
coordinates: `P` holds of `F` iff it holds of every conjugate `conj φ F`. -/
def IsNatural (P : PropFamily.{u}) : Prop :=
  ∀ {K X : Type u} (phi : K ≃ X) (F : K → K), P K F ↔ P X (conj phi F)

/-- **Transferability is naturality, pointwise.** Along a fixed transport `conj φ`,
transferability of `P` is exactly its (one-directional) naturality condition. -/
theorem transferable_iff_naturality_at (P : PropFamily.{u}) {K X : Type u}
    (phi : K ≃ X) :
    Transferable (conj phi) (P K) (P X) ↔ (∀ F, P K F → P X (conj phi F)) :=
  Iff.rfl

/-- **Naturality is transferability along every conjugation.** A property family
is natural iff it transfers along conjugation by *every* equivalence (in
particular along inverses, which supplies the reverse implication). -/
theorem isNatural_iff_all_transferable (P : PropFamily.{u}) :
    IsNatural P ↔ ∀ {K X : Type u} (phi : K ≃ X), Transferable (conj phi) (P K) (P X) := by
  constructor
  · intro hP K X phi F hF
    exact (hP phi F).1 hF
  · intro hT K X phi F
    constructor
    · intro hF; exact hT phi F hF
    · intro hF
      have := hT phi.symm (conj phi F) hF
      rwa [conj_conj_symm] at this

/-! ## Structural vs. semantic transport -/

/-- **Structural transport**: transport of a system by conjugation with an
equivalence. It preserves the *structure* (the self-map up to coordinates). -/
def StructuralTransport {K X : Type*} (phi : K ≃ X) : (K → K) → (X → X) := conj phi

/-- **Semantic transport**: any transport `T` that carries the *meaning* `P_K`
into `P_X`, without requiring it to arise from a coordinate change. -/
def SemanticTransport {K X : Type*} (T : (K → K) → (X → X))
    (P_K : DynamicProperty K) (P_X : DynamicProperty X) : Prop :=
  Transferable T P_K P_X

/-- Every natural property admits a **structural** semantic transport along any
equivalence: structural transport is always semantically valid for natural
families. -/
theorem structural_isSemantic_of_natural (P : PropFamily.{u}) (hP : IsNatural P)
    {K X : Type u} (phi : K ≃ X) :
    SemanticTransport (StructuralTransport phi) (P K) (P X) :=
  (isNatural_iff_all_transferable P).1 hP phi

end UAMTransfer
