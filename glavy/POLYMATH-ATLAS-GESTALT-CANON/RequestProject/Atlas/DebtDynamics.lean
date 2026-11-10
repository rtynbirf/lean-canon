import Mathlib

open scoped BigOperators
open Filter Topology

/-!
# H1 — The Fiscal Spiral (Domar debt dynamics), formalized

This file gives an *operational, falsifiable* formalization of the "fiscal spiral"
hypothesis (H1).

## Model

We track the public **debt-to-GDP ratio** `d : ℕ → ℝ`, period by period.  The
standard accounting law of motion for this ratio is

  `d (n+1) = ρ * d n - p n`,

where

* `ρ = (1 + r) / (1 + g)` is the *debt-augmenting factor*, built from the
  effective nominal interest rate `r` on the debt and the nominal GDP growth
  rate `g`;
* `p n` is the **primary balance** (primary *surplus*) in period `n`, expressed
  as a fraction of GDP.  A primary surplus is `p n > 0`; "no primary surplus"
  means `p n ≤ 0`.

## The operational hypothesis

H1 in operational form: *if*

* the effective interest rate exceeds the growth rate, `g < r` (equivalently
  `ρ > 1`), **and**
* there is no primary surplus in any period, `p n ≤ 0`, **and**
* the country starts with positive debt, `d 0 > 0`,

*then* the debt-to-GDP ratio diverges to `+∞` (`H1_debt_diverges`), and in fact
does so at least geometrically, `ρ ^ n * d 0 ≤ d n` (`H1_geometric_lower_bound`).

## Falsifiability (the contrapositive)

`H1_falsifiable` states the operational, testable content demanded of a
scientific hypothesis: **if** the debt-to-GDP ratio stays bounded above, **then**
either the interest rate did not exceed growth (`r ≤ g`) *or* there was a primary
surplus in some period (`∃ n, 0 < p n`).  Observing a bounded debt ratio while
`r > g` and no surplus ever occurred would falsify the model.
-/

namespace DebtDynamics

variable {r g : ℝ}

/-- The debt-augmenting factor `ρ = (1+r)/(1+g)`. -/
noncomputable def rho (r g : ℝ) : ℝ := (1 + r) / (1 + g)

/-- If growth is above `-100%` (`-1 < g`) and the interest rate exceeds the
growth rate (`g < r`), then the debt-augmenting factor exceeds one. -/
theorem one_lt_rho (hg : -1 < g) (hrg : g < r) : 1 < rho r g := by
  rw [ rho, lt_div_iff₀ ] <;> linarith

/--
**Geometric lower bound.** Under the law of motion and no primary surplus
(`p n ≤ 0`), the debt-to-GDP ratio dominates the geometric sequence
`ρ ^ n * d 0` (this holds for any sign of `d 0`).
-/
theorem H1_geometric_lower_bound (hg : -1 < g) (hrg : g < r)
    {d p : ℕ → ℝ}
    (hlaw : ∀ n, d (n + 1) = rho r g * d n - p n)
    (hp : ∀ n, p n ≤ 0) :
    ∀ n, rho r g ^ n * d 0 ≤ d n := by
  intro n;
  induction' n with n ih;
  · grind +locals;
  · rw [ pow_succ', mul_assoc ];
    nlinarith [ hlaw n, hp n, show 0 < rho r g from div_pos ( by linarith ) ( by linarith ) ]

/--
**H1, main statement: the debt-to-GDP ratio diverges to `+∞`.**
-/
theorem H1_debt_diverges (hg : -1 < g) (hrg : g < r)
    {d p : ℕ → ℝ} (hd0 : 0 < d 0)
    (hlaw : ∀ n, d (n + 1) = rho r g * d n - p n)
    (hp : ∀ n, p n ≤ 0) :
    Tendsto d atTop atTop := by
  refine Filter.tendsto_atTop_mono (fun n ↦ ?_)
    ((tendsto_pow_atTop_atTop_of_one_lt (one_lt_rho hg hrg)).atTop_mul_const hd0)
  exact H1_geometric_lower_bound hg hrg hlaw hp n

/--
**Falsifiability (contrapositive of H1).** If the debt-to-GDP ratio stays
bounded above while satisfying the law of motion with positive initial debt,
then the model's premises must fail: either the interest rate did not exceed the
growth rate (`r ≤ g`), or there was a primary surplus in some period.
-/
theorem H1_falsifiable (hg : -1 < g)
    {d p : ℕ → ℝ} (hd0 : 0 < d 0)
    (hlaw : ∀ n, d (n + 1) = rho r g * d n - p n)
    (hbdd : ∃ M, ∀ n, d n ≤ M) :
    r ≤ g ∨ ∃ n, 0 < p n := by
  contrapose! hbdd;
  exact fun M => by have := H1_debt_diverges hg hbdd.1 hd0 hlaw hbdd.2; exact this.eventually_gt_atTop M |> fun h => h.exists;

end DebtDynamics