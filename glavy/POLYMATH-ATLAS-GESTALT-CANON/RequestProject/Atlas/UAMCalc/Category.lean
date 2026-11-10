/-
  UAM.Category — Category `Dyn` of dynamical systems, a genuine functor
  `Dyn ⥤ Prop`, and closure properties of `Transferable`.

  Completed tasks:
  1. `Dyn` is given a lawful `Category` instance.
  2. A concrete, non-trivial functor `Properties : Dyn ⥤ Prop` is built:
     "having a fixed point" is covariant along the equivariant morphisms of
     `Dyn`.  (The naive `PropertiesObj` below is *always* `True`, hence only
     the constant functor; the interesting functor requires a fixed family of
     properties preserved by morphisms, which `hasFixedPoint` provides.)
  3. `Transferable` is closed under `∧` and `∨`; it is **not** closed under
     negation, witnessed by `transferable_not_counterexample`.
  4. Naturality: an isomorphism in `Dyn` induces an iff of the transported
     property (`hasFixedPoint_iff_of_iso`).
-/

import Mathlib
import RequestProject.Atlas.UAMCalc.Core

namespace UAM

open CategoryTheory

/-! ## Category Dyn -/

/-- Object: a pair (carrier, dyn) where dyn is an endomorphism. -/
structure Dyn.Obj where
  carrier : Type*
  dyn    : carrier → carrier

/-- Morphism: a semiconjugation (`map ∘ A.dyn = B.dyn ∘ map`). -/
@[ext]
structure Dyn.Morph (A B : Dyn.Obj) where
  map      : A.carrier → B.carrier
  commutes : ∀ x, map (A.dyn x) = B.dyn (map x)

/-- The category `Dyn` of dynamical systems. -/
instance : Category Dyn.Obj where
  Hom A B := Dyn.Morph A B
  id A := ⟨id, fun _ => rfl⟩
  comp f g := ⟨g.map ∘ f.map, fun x => by
    simp only [Function.comp_apply, f.commutes, g.commutes]⟩

/-! ## The naive "properties" object -/

/-- The "set of all dynamic properties satisfied by `D.dyn`", represented as a
    single `Prop`.  Note this is *always* `True` (take `P := fun _ => True`),
    so it only yields the constant functor and is not informative. -/
def PropertiesObj (D : Dyn.Obj) : Prop :=
  ∃ P : DynamicProperty D.carrier, P D.dyn

theorem propertiesObj_trivial (D : Dyn.Obj) : PropertiesObj D :=
  ⟨fun _ => True, trivial⟩

/-! ## A genuine functor `Dyn ⥤ Prop` -/

/-- The property "the dynamics has a fixed point". -/
def hasFixedPoint (D : Dyn.Obj) : Prop := ∃ x, D.dyn x = x

/-- Fixed points push forward along equivariant maps, giving a real functor
    `Dyn ⥤ Prop`.  Its action on morphisms is `hasFixedPoint A → hasFixedPoint B`,
    which is exactly the categorical statement that having a fixed point is a
    transferable (here: covariant) property. -/
def Properties : Dyn.Obj ⥤ Prop where
  obj D := hasFixedPoint D
  map {A B} f := homOfLE (fun h => by
    obtain ⟨x, hx⟩ := h
    exact ⟨f.map x, by rw [← f.commutes, hx]⟩)
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Naturality / isomorphism-invariance: isomorphic objects of `Dyn` have the
    same fixed-point status.  This is a non-trivial consequence of functoriality
    (it uses both directions of the isomorphism). -/
theorem hasFixedPoint_iff_of_iso {A B : Dyn.Obj} (e : A ≅ B) :
    hasFixedPoint A ↔ hasFixedPoint B :=
  Iff.intro (leOfHom (Properties.map e.hom)) (leOfHom (Properties.map e.inv))

/-! ## Closure of Transferable under logical connectives -/

/-- `Transferable` is closed under conjunction. -/
theorem transferable_and {X K : Type*} [PhiModel X K]
    {P_K Q_K : DynamicProperty K} {P_X Q_X : DynamicProperty X}
    (hP : Transferable X K P_K P_X) (hQ : Transferable X K Q_K Q_X) :
    Transferable X K (fun F => P_K F ∧ Q_K F) (fun F => P_X F ∧ Q_X F) :=
  ⟨fun F h => ⟨hP.transferable F h.1, hQ.transferable F h.2⟩⟩

/-- `Transferable` is closed under disjunction. -/
theorem transferable_or {X K : Type*} [PhiModel X K]
    {P_K Q_K : DynamicProperty K} {P_X Q_X : DynamicProperty X}
    (hP : Transferable X K P_K P_X) (hQ : Transferable X K Q_K Q_X) :
    Transferable X K (fun F => P_K F ∨ Q_K F) (fun F => P_X F ∨ Q_X F) :=
  ⟨fun F h => h.elim (fun h1 => Or.inl (hP.transferable F h1))
                     (fun h2 => Or.inr (hQ.transferable F h2))⟩

/-- The identity `PhiModel` on a single type. -/
def idModel (K : Type*) : PhiModel K K where
  phi := id
  inv := id
  left := fun _ => rfl
  right := fun _ => rfl

/-- `Transferable` is **not** closed under negation in general: there is a
    (source, target) predicate pair that is transferable while its negation is
    not.  Here the source property is unsatisfiable and the target property is
    trivially true, so transferability holds vacuously, yet the negated pair
    ("always true" source, "always false" target) fails on any endomorphism. -/
theorem transferable_not_counterexample :
    ¬ ∀ (X K : Type) [PhiModel X K]
        (P_K : DynamicProperty K) (P_X : DynamicProperty X),
        Transferable X K P_K P_X →
        Transferable X K (fun F => ¬ P_K F) (fun F => ¬ P_X F) := by
  intro h
  letI : PhiModel Bool Bool := idModel Bool
  have hT : Transferable Bool Bool (fun _ => False) (fun _ => True) :=
    ⟨fun _ hF => hF.elim⟩
  have hneg := (h Bool Bool (fun _ => False) (fun _ => True) hT).transferable id
    (by simp)
  exact hneg trivial

end UAM
