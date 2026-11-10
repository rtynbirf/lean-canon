import Mathlib
import RequestProject.Atlas.UAMTransfer.Transferability

/-!
# UAM — Smooth dynamical systems and zone stability

This file develops the sub-framework for *smooth* discrete dynamical systems and
proves the transferability of **zone stability** under conjugation, replacing the
`zone_stability` axiom of the general framework by a genuine theorem.

## On the proof strategy

The informal contour suggested by the theory is: at a fixed point the Jacobian of
`F` is invertible, the Implicit / Inverse Function Theorem yields a local
diffeomorphism, and conjugation `φ F φ⁻¹` transports the Jacobian to
`φ' · J_F · φ'⁻¹`, whose invertibility is preserved.

That heuristic, however, is only about the *linearization* at a fixed point and
does **not** by itself preserve the metric zone-stability estimate: a general
diffeomorphism distorts distances, so an orbit staying inside an `ε`-ball around
`x₀` need not stay inside an `ε`-ball around `φ x₀`. The estimate is preserved
*exactly* when the conjugacy is **rigid** (isometric): then the `ε`-`δ` bound is
carried over verbatim. Every *smooth linear isometry* (`≃ₗᵢ`) is such a rigid
smooth diffeomorphism, giving the intended smooth-diffeomorphism statement as a
corollary (`zone_stability_transferable_smooth`).

We therefore prove the sound, general metric statement
(`zone_stability_transferable`) and specialise it to the smooth setting.
-/

namespace UAMTransfer

open Function

/-! ## Smooth dynamical systems -/

/-- A **smooth dynamical system** on a real normed space: a bundled self-map that
is `C^∞`. This is the structured replacement, in the smooth sub-framework, of a
bare `F : K → K`. -/
class SmoothDyn (K : Type*) [NormedAddCommGroup K] [NormedSpace ℝ K] where
  /-- The generating self-map of the system. -/
  F : K → K
  /-- The generating map is infinitely differentiable. -/
  smooth : ContDiff ℝ ⊤ F

/-! ## Zone stability -/

/-- **Zone stability** of `F` at a base point `x₀`: there is a radius `ε` such that
every point within `ε` of `x₀` stays within `ε` of `x₀` under all forward iterates.
The `ε`-ball around `x₀` is a forward-invariant *stable zone*. -/
def IsZoneStable {K : Type*} [PseudoMetricSpace K] (F : K → K) (x0 : K) : Prop :=
  ∃ ε > 0, ∀ y : K, dist x0 y < ε → ∀ n : ℕ, dist x0 (F^[n] y) < ε

/-- **Zone stability is transferable** under conjugation by an isometric
equivalence (a rigid change of coordinates). The stable zone of radius `ε`
around `x₀` becomes the stable zone of the same radius `ε` around `φ x₀`. This
theorem replaces the `zone_stability` axiom. -/
theorem zone_stability_transferable {K X : Type*} [MetricSpace K] [MetricSpace X]
    (phi : K ≃ᵢ X) (F : K → K) (x0 : K) (h : IsZoneStable F x0) :
    IsZoneStable (conj phi.toEquiv F) (phi x0) := by
  obtain ⟨ε, hε, hmain⟩ := h
  refine ⟨ε, hε, ?_⟩
  intro y hy n
  rw [conj_iterate]
  simp only [conj_apply, IsometryEquiv.coe_toEquiv]
  rw [phi.dist_eq]
  apply hmain
  -- `dist x0 (phi.symm y) < ε` follows from `dist (phi x0) y < ε` by rigidity.
  show dist x0 (phi.symm y) < ε
  have hkey : dist x0 (phi.symm y) = dist (phi x0) y := by
    simpa using phi.symm.dist_eq (phi x0) y
  rw [hkey]
  exact hy

/-- **Zone stability transfers along a smooth (linear) isometric diffeomorphism.**
A `≃ₗᵢ[ℝ]` is both `C^∞` (`LinearIsometryEquiv.contDiff`) and rigid, so it is a
smooth diffeomorphism to which the transfer principle applies. -/
theorem zone_stability_transferable_smooth {K X : Type*}
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (phi : K ≃ₗᵢ[ℝ] X) (F : K → K) (x0 : K) (h : IsZoneStable F x0) :
    IsZoneStable (conj phi.toIsometryEquiv.toEquiv F) (phi x0) :=
  zone_stability_transferable phi.toIsometryEquiv F x0 h

end UAMTransfer
