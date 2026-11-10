import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_BehavioralMetric

set_option autoImplicit false

/-!
# Paired behavioral and structural distances

The structural coordinate is a coarse discrete form metric: identical words
have distance zero, unequal words of different lengths have distance one, and
unequal words of equal length have distance two.  Pairing it with behavioral
distance records meaning and form separately.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- A coarse structural distance that distinguishes equality and whether a
change of length is required. -/
noncomputable def structuralDistance
    (w₁ w₂ : UAM_Free.FreeMonoid α) : Nat :=
  if w₁ = w₂ then 0 else if w₁.length = w₂.length then 2 else 1

/-- The paired metric keeps behavioral and structural coordinates distinct. -/
noncomputable def pairedDistance
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ : UAM_Free.FreeMonoid α) : ℝ × Nat :=
  (behavioralDistance L w₁ w₂, structuralDistance w₁ w₂)

/-- Structural distance is symmetric. -/
theorem structuralDistance_symm
    (w₁ w₂ : UAM_Free.FreeMonoid α) :
    structuralDistance w₁ w₂ = structuralDistance w₂ w₁ := by
  by_cases h : w₁ = w₂
  · subst w₂
    rfl
  · have hs : w₂ ≠ w₁ := Ne.symm h
    simp only [structuralDistance, h, hs, ↓reduceIte]
    congr 1
    exact propext (eq_comm)

/-- Structural distance vanishes exactly for identical words. -/
theorem structuralDistance_eq_zero_iff
    (w₁ w₂ : UAM_Free.FreeMonoid α) :
    structuralDistance w₁ w₂ = 0 ↔ w₁ = w₂ := by
  by_cases h : w₁ = w₂
  · simp [structuralDistance, h]
  · unfold structuralDistance
    rw [if_neg h]
    split <;> simp_all

/-- The concrete all-zero forms differ by one length-changing edit. -/
theorem fin4_structural_zero_forms : structuralDistance
    ([0, 0] : UAM_Free.FreeMonoid (Fin 4)) [0] = 1 := by
  simp [structuralDistance]

/-- Distinct singleton forms have equal length and require replacement (one
deletion and one insertion). -/
theorem fin4_structural_nonzero_forms : structuralDistance
    ([1] : UAM_Free.FreeMonoid (Fin 4)) [2] = 2 := by
  simp [structuralDistance]

/-- The paired distance separates the structural forms `[0,0]` and `[0]`
while recording that they have identical behavior. -/
theorem fin4_paired_zero_forms : pairedDistance Fin4ZeroStarLanguage
    ([0, 0] : UAM_Free.FreeMonoid (Fin 4)) [0] = (0, 1) := by
  rw [Prod.ext_iff]
  exact ⟨fin4_behavioral_zero_words, fin4_structural_zero_forms⟩

end UAM_RSIA
