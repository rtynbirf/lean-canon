/-
  UAM.TransferProofs — Transferability proofs for concrete properties.
  Corresponds to UTT PDF Table 1 and Section 3.

  These use the two-predicate `Transferable X K P_K P_X` from `UAM.Core`:
  a source property `P_K` on the canonical space `K` is transported to a
  target property `P_X` on the working space `X`.
-/

import RequestProject.Atlas.UAMCalc.Core

namespace UAM

open PhiModel

/-! ### Observable-based properties (factoring through phi) -/

/-- `Dec` is transferable when the two observables agree along the model,
    i.e. `O_K(k) = O_X(inv k)`. -/
theorem dec_transferable {X K V : Type*} [PhiModel X K] [LE V]
    (O : Observable K V) (O' : Observable X V)
    (hO : ∀ k, O.map k = O'.map (inv k)) :
    Transferable X K (Dec K V O) (Dec X V O') where
  transferable F h y := by
    have key : O'.map ((transport F) y) = O.map (F (phi y)) := by
      simp only [transport, Function.comp_apply]
      rw [← hO (F (phi y))]
    have keyy : O'.map y = O.map (phi y) := by
      rw [hO (phi y), left]
    rw [key, keyy]
    exact h (phi y)

/-- `Inc` is transferable under the same factoring condition. -/
theorem inc_transferable {X K V : Type*} [PhiModel X K] [LE V]
    (O : Observable K V) (O' : Observable X V)
    (hO : ∀ k, O.map k = O'.map (inv k)) :
    Transferable X K (Inc K V O) (Inc X V O') where
  transferable F h y := by
    have key : O'.map ((transport F) y) = O.map (F (phi y)) := by
      simp only [transport, Function.comp_apply]
      rw [← hO (F (phi y))]
    have keyy : O'.map y = O.map (phi y) := by
      rw [hO (phi y), left]
    rw [key, keyy]
    exact h (phi y)

/-- `Cons` is transferable under the same factoring condition. -/
theorem cons_transferable {X K V : Type*} [PhiModel X K] [BEq V]
    (O : Observable K V) (O' : Observable X V)
    (hO : ∀ k, O.map k = O'.map (inv k)) :
    Transferable X K (Cons K V O) (Cons X V O') where
  transferable F h y := by
    have key : O'.map ((transport F) y) = O.map (F (phi y)) := by
      simp only [transport, Function.comp_apply]
      rw [← hO (F (phi y))]
    have keyy : O'.map y = O.map (phi y) := by
      rw [hO (phi y), left]
    rw [key, keyy]
    exact h (phi y)

/-! ### Structural properties (transferable for any PhiModel) -/

/-- Key iteration identity: transporting and iterating commute (pointwise). -/
theorem transport_iterate {X K : Type*} [PhiModel X K] (F : K → K) (m : ℕ) (x : X) :
    (transport F)^[m] x = inv (F^[m] (phi x)) := by
  induction m with
  | zero => simp [PhiModel.left]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [transport, Function.comp_apply, PhiModel.right,
      Function.iterate_succ_apply']

/-- `FixPt` is transferable for any PhiModel. -/
instance fixPt_transferable {X K : Type*} [PhiModel X K] :
    Transferable X K (FixPt K) (FixPt X) where
  transferable F := fun ⟨x, hx⟩ => ⟨inv x, by
    show (transport F) (inv x) = inv x
    simp only [transport, Function.comp_apply]
    rw [PhiModel.right, hx]⟩

/-- `Period n` is transferable for any PhiModel. -/
instance period_transferable {X K : Type*} [PhiModel X K] (n : ℕ) :
    Transferable X K (Period K n) (Period X n) where
  transferable F h := by
    funext x
    show (transport F)^[n] x = x
    rw [transport_iterate F n x, h]
    simp [PhiModel.left]

/-- `IsPeriodic` is transferable for any PhiModel. -/
instance isPeriodic_transferable {X K : Type*} [PhiModel X K] :
    Transferable X K (IsPeriodic K) (IsPeriodic X) where
  transferable F := fun ⟨n, hn, h⟩ =>
    ⟨n, hn, (period_transferable n).transferable F h⟩

end UAM
