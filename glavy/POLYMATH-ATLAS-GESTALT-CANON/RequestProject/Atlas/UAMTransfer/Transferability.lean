import Mathlib

/-!
# UAM — Transferability Calculus

Core framework for the *Universal Abstraction Machine* (UAM) transferability
calculus. A `DynamicProperty` is a predicate on self-maps `K → K` (discrete-time
dynamical systems). A property `P_K` is *transferable* along a transport
`T : (K → K) → (X → X)` to a property `P_X` when every system satisfying `P_K`
is mapped by `T` to a system satisfying `P_X`.

The canonical transport is *conjugation* `conj φ F = φ ∘ F ∘ φ.symm`, which
models a change of coordinates by an equivalence `φ : K ≃ X`.
-/

namespace UAMTransfer

open Function

/-- A dynamic property of a discrete-time dynamical system is a predicate on the
self-map generating it. -/
def DynamicProperty (K : Type*) : Type _ := (K → K) → Prop

/-- Transport of a dynamical map `F : K → K` along an equivalence `φ : K ≃ X`.
This is the change-of-coordinates (conjugation) `φ ∘ F ∘ φ⁻¹`. -/
def conj {K X : Type*} (phi : K ≃ X) (F : K → K) : X → X :=
  phi ∘ F ∘ phi.symm

@[simp] theorem conj_apply {K X : Type*} (phi : K ≃ X) (F : K → K) (x : X) :
    conj phi F x = phi (F (phi.symm x)) := rfl

/-- `P_K` is *transferable* to `P_X` along the transport `T`. -/
def Transferable {K X : Type*} (T : (K → K) → (X → X))
    (P_K : DynamicProperty K) (P_X : DynamicProperty X) : Prop :=
  ∀ F : K → K, P_K F → P_X (T F)

/-- **Universal Transfer Theorem (UTT).** The single inference rule of the
calculus: modus ponens on transferability. -/
theorem UTT {K X : Type*} {T : (K → K) → (X → X)}
    {P_K : DynamicProperty K} {P_X : DynamicProperty X}
    (hT : Transferable T P_K P_X) {F : K → K} (hF : P_K F) : P_X (T F) :=
  hT F hF

/-! ### Basic algebra of conjugation -/

/-- Conjugation commutes with iteration: `(conj φ F)^[n] = conj φ (F^[n])`. -/
theorem conj_iterate {K X : Type*} (phi : K ≃ X) (F : K → K) (n : ℕ) :
    (conj phi F)^[n] = conj phi (F^[n]) := by
  induction n with
  | zero => ext x; simp [conj]
  | succ n ih =>
      ext x
      rw [Function.iterate_succ', Function.iterate_succ']
      simp only [Function.comp_apply, ih, conj_apply, Equiv.symm_apply_apply]

@[simp] theorem conj_id {K X : Type*} (phi : K ≃ X) :
    conj phi (id : K → K) = id := by
  ext x; simp [conj]

/-! ### Boolean algebra of transferable properties -/

/-- Conjunction of dynamic properties. -/
def DynamicProperty.and {K : Type*} (P Q : DynamicProperty K) : DynamicProperty K :=
  fun F => P F ∧ Q F

/-- Disjunction of dynamic properties. -/
def DynamicProperty.or {K : Type*} (P Q : DynamicProperty K) : DynamicProperty K :=
  fun F => P F ∨ Q F

/-- Implication of dynamic properties. -/
def DynamicProperty.imp {K : Type*} (P Q : DynamicProperty K) : DynamicProperty K :=
  fun F => P F → Q F

/-- Transferability is closed under conjunction (no extra hypotheses). -/
theorem transferable_and {K X : Type*} {T : (K → K) → (X → X)}
    {P_K Q_K : DynamicProperty K} {P_X Q_X : DynamicProperty X}
    (hP : Transferable T P_K P_X) (hQ : Transferable T Q_K Q_X) :
    Transferable T (DynamicProperty.and P_K Q_K) (DynamicProperty.and P_X Q_X) :=
  fun F hF => ⟨hP F hF.1, hQ F hF.2⟩

/-- Transferability is closed under disjunction (no extra hypotheses). -/
theorem transferable_or {K X : Type*} {T : (K → K) → (X → X)}
    {P_K Q_K : DynamicProperty K} {P_X Q_X : DynamicProperty X}
    (hP : Transferable T P_K P_X) (hQ : Transferable T Q_K Q_X) :
    Transferable T (DynamicProperty.or P_K Q_K) (DynamicProperty.or P_X Q_X) :=
  fun F hF => hF.imp (hP F) (hQ F)

/-- Transferability of an implication requires a *backward* transfer of the
antecedent (structural transport). -/
theorem transferable_imp {K X : Type*} {T : (K → K) → (X → X)}
    {P_K Q_K : DynamicProperty K} {P_X Q_X : DynamicProperty X}
    (h1_bwd : ∀ F, P_X (T F) → P_K F)
    (hQ : Transferable T Q_K Q_X) :
    Transferable T (DynamicProperty.imp P_K Q_K) (DynamicProperty.imp P_X Q_X) :=
  fun F hF hPX => hQ F (hF (h1_bwd F hPX))

/-! ### Concrete transferable properties -/

/-- The system has a fixed point. -/
def HasFixedPoint {K : Type*} : DynamicProperty K := fun F => ∃ x, F x = x

/-- The system has a periodic point (of some positive period). -/
def IsPeriodic {K : Type*} : DynamicProperty K :=
  fun F => ∃ (x : K) (n : ℕ), 0 < n ∧ F^[n] x = x

/-- Conjugation preserves fixed points, both ways. -/
theorem HasFixedPoint_conj_iff {K X : Type*} (phi : K ≃ X) (F : K → K) :
    HasFixedPoint (conj phi F) ↔ HasFixedPoint F := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨phi.symm x, ?_⟩
    have := congrArg phi.symm hx
    simpa [conj] using this
  · rintro ⟨x, hx⟩
    refine ⟨phi x, ?_⟩
    simp [conj, hx]

/-- Having a fixed point is transferable along any conjugation. -/
theorem HasFixedPoint_transferable {K X : Type*} (phi : K ≃ X) :
    Transferable (conj phi) (HasFixedPoint) (HasFixedPoint) :=
  fun F hF => (HasFixedPoint_conj_iff phi F).mpr hF

/-- Being periodic is transferable along any conjugation. -/
theorem IsPeriodic_transferable {K X : Type*} (phi : K ≃ X) :
    Transferable (conj phi) (IsPeriodic) (IsPeriodic) := by
  rintro F ⟨x, n, hn, hx⟩
  refine ⟨phi x, n, hn, ?_⟩
  rw [conj_iterate]
  simp [conj, hx]

end UAMTransfer
