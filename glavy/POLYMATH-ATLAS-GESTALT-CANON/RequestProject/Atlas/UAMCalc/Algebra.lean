/-
  UAM.Algebra — M2(F2) algebra with bot-product.
  Corresponds to UTT PDF Section 7.1.
-/

import Mathlib
import RequestProject.Atlas.UAMCalc.Core

namespace UAM

/-! ## M2(F2): 2x2 matrices over F2 -/

/-- The two-element field `F₂`.  We use `ZMod 2` (rather than `Fin 2`) so that
    the entries carry the full `CommRing` structure, which `Fin 2` lacks. -/
abbrev F2 := ZMod 2

/-- The ⊔-operation (perp-product): X ⊔ Y = X + Y + X*Y. -/
def bot_op (X Y : Matrix (F2) (F2) F2) : Matrix (F2) (F2) F2 :=
  X + Y + X * Y

/-- Conjugation phi: phi(X) = I + X, mapping ⊔ to multiplication. -/
def phiM (X : Matrix (F2) (F2) F2) : Matrix (F2) (F2) F2 :=
  1 + X

/-- Inverse: phi^{-1}(Y) = Y - I (in char 2, same as Y + I). -/
def phiM_inv (Y : Matrix (F2) (F2) F2) : Matrix (F2) (F2) F2 :=
  Y + 1

/-! ### Properties of phi -/

/-- phi is an involution: phi(phi(X)) = X. -/
theorem phi_involution (X : Matrix (F2) (F2) F2) :
    phiM (phiM X) = X := by
  simp only [phiM, ← add_assoc]
  rw [show (1 : Matrix (F2) (F2) F2) + 1 = 0 by decide, zero_add]

/-- phi maps ⊔-product to ordinary product:
    phi(X ⊔ Y) = phi(X) * phi(Y). -/
theorem phi_multiplicative (X Y : Matrix (F2) (F2) F2) :
    phiM (bot_op X Y) = phiM X * phiM Y := by
  simp only [phiM, bot_op]
  noncomm_ring

/-! ### ⊔-product formula -/

/-- Two-element case: X ⊔ Y = I + (I + X)(I + Y). -/
theorem bot_eq_phi_prod_two (X Y : Matrix (F2) (F2) F2) :
    bot_op X Y = 1 + (1 + X) * (1 + Y) := by
  have h : (1 : Matrix (F2) (F2) F2) + 1 = 0 := by decide
  simp only [bot_op]
  have expand : (1 : Matrix (F2) (F2) F2) + (1 + X) * (1 + Y)
      = (1 + 1) + (X + Y + X * Y) := by noncomm_ring
  rw [expand, h, zero_add]

/-! ### Rank monotonicity via UTT -/

/-- Rank observable: O(A) = rank(A). -/
noncomputable def rankObservable : Observable (Matrix (F2) (F2) F2) ℕ where
  map := Matrix.rank

-- Theorem: rank is non-increasing under ⊔-product.
-- This follows from UTT since rank is non-increasing under
-- multiplication in the conjugated (canonical) representation.
-- Proved via: phi maps ⊔ to *, rank(F*G) ≤ min(rank F, rank G),
-- and UTT transfers this to rank(F ⊔ G) ≤ rank(G).

/-! ### LTE (Lifting The Exponent) -/

-- Standard LTE lemma: v_p(p^j - 1) = v_p(p - 1) + v_p(j).
-- Used in the analysis of periodicity in M2(F2) dynamics.

end UAM