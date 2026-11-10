/-
  UAM.Core — Base definitions of Universal Abstraction Machine.
  Architecture: V3 (DynamicProperty as primary object).
  Corresponds to UTT PDF Sections 2–4, Listings 1–3.
-/

import Mathlib

namespace UAM

/-! ## Level 1: Conjugation (PhiModel) -/

/-- PhiModel: a pair of mutually inverse bijections between X and K.
    X is the "working" space (nonlinear), K is the "canonical" space (linear). -/
class PhiModel (X K : Type*) where
  phi   : X → K
  inv   : K → X
  left  : ∀ x, inv (phi x) = x
  right : ∀ k, phi (inv k) = k

/-! ## Level 2: Transport operator -/

/-- Transport dynamics from K to X via conjugation.
    C_phi(F) = phi^{-1} ∘ F ∘ phi  (called `transfer` in the PDF). -/
def transport {X K : Type*} [PhiModel X K] (F : K → K) : X → X :=
  PhiModel.inv ∘ F ∘ PhiModel.phi

/-! ## Level 3: DynamicProperty -/

/-- A dynamic property is a predicate on endomorphisms. -/
abbrev DynamicProperty (K : Type*) := (K → K) → Prop

/-! ## Level 4: Transferable -/

/-- Transferable property: `P_K F` implies `P_X (transport F)`.

    Note on the signature: the transported dynamics `transport F` acts on the
    *working* space `X`, while the source dynamics `F` acts on the *canonical*
    space `K`.  A single predicate on `K` therefore cannot type-check the
    conclusion (it would force `X = K`).  We use the mathematically faithful
    two-predicate form: a source property `P_K` on `K` and a target property
    `P_X` on `X`.  When `X = K` and `P_K = P_X` this reduces to the informal
    single-predicate statement of the PDF. -/
class Transferable (X K : Type*) [PhiModel X K]
    (P_K : DynamicProperty K) (P_X : DynamicProperty X) : Prop where
  transferable : ∀ F, P_K F → P_X (transport F)

/-! ## Level 5: Universal Transfer Theorem -/

/-- UTT: direct consequence of transferability definition (modus ponens). -/
theorem utt {X K : Type*} [PhiModel X K]
    {P_K : DynamicProperty K} {P_X : DynamicProperty X}
    [inst : Transferable X K P_K P_X]
    {F : K → K} (hP : P_K F) :
    P_X (transport F) :=
  inst.transferable F hP

/-! ## Observable and Property Constructors -/

/-- An observable maps states to values in some type V. -/
structure Observable (K V : Type*) where
  map : K → V

/-- Monotone non-increase: Dec(O) = {F | ∀ x, O(F x) ≤ O(x)} -/
def Dec (K V : Type*) [LE V] (O : Observable K V) : DynamicProperty K :=
  fun F => ∀ x, O.map (F x) ≤ O.map x

/-- Monotone non-decrease: Inc(O) = {F | ∀ x, O(F x) ≥ O(x)} -/
def Inc (K V : Type*) [LE V] (O : Observable K V) : DynamicProperty K :=
  fun F => ∀ x, O.map (F x) ≥ O.map x

/-- Conservation: Cons(O) = {F | ∀ x, O(F x) = O(x)} -/
def Cons (K V : Type*) [BEq V] (O : Observable K V) : DynamicProperty K :=
  fun F => ∀ x, O.map (F x) == O.map x

/-- Fixed point: FixPt = {F | ∃ x, F x = x} -/
def FixPt (K : Type*) : DynamicProperty K :=
  fun F => ∃ x, F x = x

/-- Periodicity: Period(n) = {F | F^[n] = id} -/
def Period (K : Type*) (n : ℕ) : DynamicProperty K :=
  fun F => F^[n] = id

/-- Has a fixed point for any positive period. -/
def IsPeriodic (K : Type*) : DynamicProperty K :=
  fun F => ∃ n, 0 < n ∧ F^[n] = id

end UAM