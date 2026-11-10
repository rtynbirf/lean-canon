/-
  UAM.Generalized — V3.1 two-predicate Transferable.

  This module contains the GENERALIZED architecture developed in the
  current session. It extends (does not replace) the V3 core.

  The key generalization: Transferable T P_K P_X where T is an ARBITRARY
  map between endomorphism spaces (not just conjugation).
-/

import RequestProject.Atlas.UAMCalc.Core

namespace UAM

/-- Generalized Transferable with two predicates (type-safe).
    T : End(K) → End(X) can be any map, not necessarily a conjugation.
    Two predicates are needed because T F : X → X but P_K expects K → K. -/
def GenTransferable {K X : Type*}
    (T : (K → K) → (X → X))
    (P_K : DynamicProperty K)
    (P_X : DynamicProperty X) : Prop :=
  ∀ F : K → K, P_K F → P_X (T F)

/-- Conjugation as a special case of transport T. -/
def conj {K X : Type*} (φ : K ≃ X) (F : K → K) : X → X :=
  φ ∘ F ∘ φ.symm

-- For a PhiModel, transport = conj with the induced equivalence.
-- (Left as connection exercise.)

/-! ### Boolean algebra of GenTransferable -/

theorem genTransferable_and {K X : Type*} {T : (K → K) → (X → X)}
    {P1_K P2_K : DynamicProperty K}
    {P1_X P2_X : DynamicProperty X}
    (h1 : GenTransferable T P1_K P1_X)
    (h2 : GenTransferable T P2_K P2_X) :
    GenTransferable T (fun F => P1_K F ∧ P2_K F) (fun F => P1_X F ∧ P2_X F) := by
  intro F hF
  exact ⟨h1 F hF.1, h2 F hF.2⟩

theorem genTransferable_or {K X : Type*} {T : (K → K) → (X → X)}
    {P1_K P2_K : DynamicProperty K}
    {P1_X P2_X : DynamicProperty X}
    (h1 : GenTransferable T P1_K P1_X)
    (h2 : GenTransferable T P2_K P2_X) :
    GenTransferable T (fun F => P1_K F ∨ P2_K F) (fun F => P1_X F ∨ P2_X F) := by
  intro F hF
  cases hF with
  | inl h => exact Or.inl (h1 F h)
  | inr h => exact Or.inr (h2 F h)

/-! ### Connection: GenTransferable ↔ old Transferable for conj -/

-- When T = conj(phi), GenTransferable with P_X = P corresponds
-- to the old Transferable class.
-- (Proof left as exercise — it should be definitional.)

end UAM