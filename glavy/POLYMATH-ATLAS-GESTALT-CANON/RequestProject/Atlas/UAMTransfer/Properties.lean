import Mathlib
import RequestProject.Atlas.UAMTransfer.Transferability

/-!
# UAM — Concrete transferable properties

This file implements the transferability of four concrete dynamical-systems
properties under structural transport (conjugation `conj φ`):

* `IsLyapunovStable`  — Lyapunov stability (metric spaces, transferred along
  an isometric equivalence);
* `HasBoundedGrowth`  — bounded growth of the orbits (normed spaces, transferred
  along a continuous linear equivalence);
* `HasConservationLaw` — existence of an invariant measure (measure spaces,
  transferred by pushforward along a measurable equivalence);
* `SpectralInvariant`  — invariance of the spectrum of a bounded linear operator
  under conjugation (Banach spaces).

For each property the transport is conjugation and the extra structure that `φ`
must carry (isometry / linearity / measurability) is stated explicitly in the
hypotheses of the transfer theorem.

TODO (future rounds): `TopolTransitive`, `BoundedOrbit`, `PositiveInvariant`,
`zone_stability` (the last one is developed in `UAM.SmoothDyn`).
-/

namespace UAMTransfer

open Function

/-! ## 1. Lyapunov stability

Requires `[MetricSpace K] [MetricSpace X]`. Transported along an **isometric
equivalence** `φ : K ≃ᵢ X`, because conjugation by an isometry preserves all
distances, hence the `ε`–`δ` estimate is carried over verbatim. -/

section Lyapunov

variable {K X : Type*} [MetricSpace K] [MetricSpace X]

/-- Lyapunov stability of a discrete dynamical system `F`: nearby points stay
uniformly close under all forward iterates. -/
def IsLyapunovStable : DynamicProperty K :=
  fun F => ∀ ε > 0, ∃ δ > 0, ∀ x y : K, dist x y < δ →
    ∀ n : ℕ, dist (F^[n] x) (F^[n] y) < ε

/-- Lyapunov stability is transferable along an isometric equivalence. -/
theorem IsLyapunovStable_transferable (phi : K ≃ᵢ X) :
    Transferable (conj phi.toEquiv) (IsLyapunovStable) (IsLyapunovStable) := by
  intro F hF ε hε
  obtain ⟨δ, hδ, hmain⟩ := hF ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy n
  rw [conj_iterate]
  simp only [conj_apply, IsometryEquiv.coe_toEquiv]
  rw [phi.dist_eq]
  apply hmain
  show dist (phi.symm x) (phi.symm y) < δ
  rw [phi.symm.dist_eq]
  exact hxy

end Lyapunov

/-! ## 2. Bounded growth

Requires `[NormedAddCommGroup K] [NormedAddCommGroup X]` (and a scalar field for
the transport). Transported along a **continuous linear equivalence**
`φ : K ≃L[𝕜] X`: the operator norms of `φ` and `φ⁻¹` turn the growth constant of
`F` into a growth constant of `conj φ F`. -/

section BoundedGrowth

/-- Bounded (at most affine) growth of all forward iterates. -/
def HasBoundedGrowth {K : Type*} [NormedAddCommGroup K] : DynamicProperty K :=
  fun F => ∃ C > 0, ∀ (n : ℕ) (x : K), ‖F^[n] x‖ ≤ C * (‖x‖ + 1)

variable {𝕜 K X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup K] [NormedSpace 𝕜 K]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-
Bounded growth is transferable along a continuous linear equivalence.
-/
theorem HasBoundedGrowth_transferable (phi : K ≃L[𝕜] X) :
    Transferable (conj phi.toEquiv) (HasBoundedGrowth) (HasBoundedGrowth) := by
  intro F hF;
  obtain ⟨ C, hC₀, hC ⟩ := hF;
  refine' ⟨ ‖phi.toContinuousLinearMap‖ * C * ( ‖phi.symm.toContinuousLinearMap‖ + 1) + 1, _, _ ⟩;
  · positivity;
  · intro n x
    have h1 : ‖(conj phi.toEquiv F)^[n] x‖ ≤ ‖phi.toContinuousLinearMap‖ * ‖F^[n] (phi.symm x)‖ := by
      convert phi.toContinuousLinearMap.le_opNorm _ using 1;
      exact congr_arg Norm.norm ( conj_iterate _ _ _ ▸ rfl );
    have h2 : ‖F^[n] (phi.symm x)‖ ≤ C * (‖phi.symm.toContinuousLinearMap‖ * ‖x‖ + 1) := by
      exact le_trans ( hC n _ ) ( mul_le_mul_of_nonneg_left ( add_le_add ( by simpa using phi.symm.toContinuousLinearMap.le_opNorm x ) le_rfl ) hC₀.le );
    nlinarith [ norm_nonneg x, norm_nonneg ( phi : K →L[𝕜] X ), norm_nonneg ( phi.symm : X →L[𝕜] K ), mul_nonneg ( norm_nonneg ( phi : K →L[𝕜] X ) ) ( norm_nonneg ( phi.symm : X →L[𝕜] K ) ), mul_nonneg ( norm_nonneg ( phi : K →L[𝕜] X ) ) hC₀.le, mul_nonneg ( norm_nonneg ( phi.symm : X →L[𝕜] K ) ) hC₀.le ]

end BoundedGrowth

/-! ## 3. Conservation law (invariant measure)

Requires `[MeasureSpace K] [MeasureSpace X]`. Transported by **pushforward**
along a **measurable equivalence** `φ : K ≃ᵐ X`: if `μ` is a nonzero
`F`-invariant measure, then `φ_* μ` is a nonzero `conj φ F`-invariant measure. -/

section Conservation

open MeasureTheory

variable {K X : Type*} [MeasureSpace K] [MeasureSpace X]

/-- Existence of a nonzero invariant (conserved) measure. -/
def HasConservationLaw : DynamicProperty K :=
  fun F => ∃ μ : Measure K, μ ≠ 0 ∧ MeasurePreserving F μ μ

/-
A conservation law is transferable along a measurable equivalence, by
pushing the invariant measure forward.
-/
theorem HasConservationLaw_transferable (phi : K ≃ᵐ X) :
    Transferable (conj phi.toEquiv) (HasConservationLaw) (HasConservationLaw) := by
  intro F hF
  obtain ⟨μ, hμ_nonzero, hμ_preserve⟩ := hF
  refine ⟨MeasureTheory.Measure.map phi μ, ?_, ?_⟩
  · simp_all +decide [MeasureTheory.Measure.ext_iff]
    obtain ⟨x, hx₁, hx₂⟩ := hμ_nonzero
    exact ⟨phi '' x, by simp_all +decide [MeasurableEquiv.measurable]⟩
  · refine MeasureTheory.MeasurePreserving.comp (μb := μ)
      ⟨phi.measurable, by simp +decide⟩
      (hμ_preserve.comp ⟨phi.symm.measurable, by simp +decide⟩)

end Conservation

/-! ## 4. Spectral invariance

Requires a Banach space `[NormedSpace 𝕜 K] [CompleteSpace K]`. The spectrum of a
bounded linear operator is invariant under conjugation by a continuous linear
automorphism: `σ(φ ∘ F ∘ φ⁻¹) = σ(F)`. This is the operator-theoretic incarnation
of the transfer principle. -/

section Spectral

variable {𝕜 K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup K] [NormedSpace 𝕜 K] [CompleteSpace K]

/-- Conjugation of a bounded linear operator by a continuous linear
automorphism. -/
noncomputable def conjCLM (phi : K ≃L[𝕜] K) (F : K →L[𝕜] K) : K →L[𝕜] K :=
  (phi : K →L[𝕜] K).comp (F.comp (phi.symm : K →L[𝕜] K))

omit [CompleteSpace K] in
/-- **Spectral invariance.** The spectrum of a bounded operator on a Banach space
is unchanged by conjugation with a continuous linear automorphism. (The
`CompleteSpace` hypothesis records the intended Banach-space setting; the equality
of spectra is a purely algebraic consequence of conjugation by a unit.) -/
theorem SpectralInvariant (phi : K ≃L[𝕜] K) (F : K →L[𝕜] K) :
    spectrum 𝕜 (conjCLM phi F) = spectrum 𝕜 F := by
  have hconj : conjCLM phi F
      = (↑phi.toUnit) * F * (↑phi.toUnit⁻¹ : (K →L[𝕜] K)ˣ) := by
    ext x
    rfl
  rw [hconj, spectrum.units_conjugate]

end Spectral

end UAMTransfer