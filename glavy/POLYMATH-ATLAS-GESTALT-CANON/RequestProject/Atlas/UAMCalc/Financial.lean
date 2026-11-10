/-
  UAM.Financial — Debt dynamics, liquidity buffer, hypotheses H1–H7.
  Corresponds to UTT PDF Section 7.3 and Methodology PDF Section 10.1.

  The former `zone_stability` axiom has been removed and replaced by theorems
  (see the "zone stability" section below).  Analysing the dynamics shows the
  stationary point is a *repelling* fixed point (eigenvalue `1 + r > 1`), so no
  genuine ε-stable neighbourhood exists; we prove this precisely
  (`zone_stability_refuted`) together with the true, degenerate stable orbit
  through the fixed point (`stationaryState_orbit`).
-/

import Mathlib
import RequestProject.Atlas.UAMCalc.Core

namespace UAM

/-! ## Financial state space -/

/-- Debt state: (debt, buffer, interest_rate, growth_rate). -/
structure DebtState where
  debt   : ℝ  -- d_n: current debt
  buffer : ℝ  -- liqBuf: liquidity buffer
  r      : ℝ  -- interest rate
  g      : ℝ  -- growth rate

attribute [ext] DebtState

/-! ## Debt dynamics -/

/-- One-step debt dynamics:
    d_{n+1} = (1 + r) * d_n - p
    where p is the payment.
    Liquidity buffer: liqBuf(S) = d*(r - g)/(1+g) - p
-/
noncomputable def debtDynamics (S : DebtState) (p : ℝ) : DebtState where
  debt   := (1 + S.r) * S.debt - p
  buffer := S.debt * (S.r - S.g) / (1 + S.g) - p
  r      := S.r
  g      := S.g

/-- The one-step map with the payment `p` fixed, as an endomorphism of
    `DebtState` (suitable for iteration). -/
noncomputable def debtStep (p : ℝ) : DebtState → DebtState := fun S => debtDynamics S p

/-- Stationary debt level: the fixed point `d = (1+r)d - p`, i.e. `d = p/r`. -/
noncomputable def stationaryDebt (r _g p : ℝ) : ℝ :=
  p / r  -- assuming r > 0; `_g` kept for uniform (r, g, p) signature

/-- The full stationary state: debt `p/r`, buffer at that debt, and unchanged
    `r`, `g`. -/
noncomputable def stationaryState (r g p : ℝ) : DebtState where
  debt   := p / r
  buffer := p / r * (r - g) / (1 + g) - p
  r      := r
  g      := g

/-! ## Hypotheses H1–H7 -/

/-
Original H1 (COMMENTED OUT — false as stated).  The stationary buffer
   `(p/r)*(r-g)/(1+g) - p` simplifies to `-p·g·(1+r) / (r·(1+g))`, which is
   positive iff `g < 0`.  For `g ≥ 0` (with `r,p > 0`, `g > -1`) it is ≤ 0, so
   the original claim fails.  The corrected statement adds `g < 0`.

theorem H1 (r g p : ℝ) (hr : 0 < r) (hg : -1 < g) (hp : 0 < p) :
    0 < stationaryDebt r g p * (r - g) / (1 + g) - p
  -- (no proof: the statement is false without `g < 0`)
-/

/-- H1 (corrected): existence of a stationary surplus.  A positive stationary
    liquidity buffer requires a negative growth rate `g < 0` (added hypothesis);
    under `0 < r`, `-1 < g < 0`, `0 < p` the stationary buffer is positive. -/
theorem H1 (r g p : ℝ) (hr : 0 < r) (hg : -1 < g) (hg0 : g < 0) (hp : 0 < p) :
    0 < stationaryDebt r g p * (r - g) / (1 + g) - p := by
  unfold stationaryDebt;
  rw [ div_mul_eq_mul_div, div_div, lt_sub_iff_add_lt, lt_div_iff₀ ] <;> nlinarith [ mul_pos hp ( neg_pos.mpr hg0 ), mul_div_cancel₀ p hr.ne' ]

/-
Original H2 (COMMENTED OUT — false as stated: with only `0 < r`, `p` could
   be ≤ 0, making `p/r ≤ 0`).  The corrected statement adds `0 < p`.

theorem H2 (r g p : ℝ) (hr : 0 < r) : 0 < stationaryDebt r g p
  -- (no proof: the statement is false without `0 < p`)
-/

/-- H2 (corrected): positivity of the stationary debt level, given `0 < r` and
    `0 < p`. -/
theorem H2 (r g p : ℝ) (hr : 0 < r) (hp : 0 < p) : 0 < stationaryDebt r g p := by
  exact div_pos hp hr

/-- H3: Buffer monotonicity in canonical representation (placeholder). -/
theorem H3 : True := trivial  -- placeholder

/-- H4: Conjugation preserves stability (placeholder). -/
theorem H4 : True := trivial  -- placeholder

/-- H5: Spectral criterion for linearized model (placeholder). -/
theorem H5 : True := trivial  -- placeholder

/-- H6: Transferability of stability property (placeholder). -/
theorem H6 : True := trivial  -- placeholder

/-! ### H7: Refuted -/

/-- Spectral stability of the linearised model: it is governed by the
    drift/eigenvalue `μ` (first coordinate) and is *independent* of the
    volatility `σ` (second coordinate).  This is precisely why `σ` is not a
    reliable stability indicator. -/
def IsStable (s : ℝ × ℝ) : Prop := |s.1| < 1

/-
H7 (REFUTED): volatility `σ` is a reliable stability indicator.  The
    refutation exhibits a stable system with nonzero volatility, e.g. `μ = 0`,
    `σ = 1`: stability holds (`|0| < 1`) despite `σ ≠ 0`.
-/
theorem H7_refuted : ¬(∀ (μ σ : ℝ), σ ≠ 0 → ¬IsStable (μ, σ)) := by
  simp +zetaDelta at *;
  exact ⟨ 0, 1, by norm_num, by norm_num [ IsStable ] ⟩

/-! ## Zone stability (former axiom, now theorems) -/

/-- The one-step map leaves the interest rate unchanged. -/
theorem debtStep_r (p : ℝ) (S : DebtState) : (debtStep p S).r = S.r := rfl

/-- The interest rate is preserved along the orbit. -/
theorem debtStep_iterate_r (p : ℝ) (S : DebtState) (n : ℕ) :
    ((debtStep p)^[n] S).r = S.r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', debtStep_r, ih]

/-
Closed form of the debt orbit: the deviation from the stationary debt grows
    geometrically with ratio `1 + r`.
-/
theorem debt_orbit (r p : ℝ) (hr : r ≠ 0) (S : DebtState) (hrS : S.r = r) (n : ℕ) :
    ((debtStep p)^[n] S).debt = p / r + (1 + r) ^ n * (S.debt - p / r) := by
  induction n <;> simp_all +decide [ Function.iterate_succ_apply', pow_succ', debtStep ];
  have := debtStep_iterate_r p S ‹_›; simp_all +decide [ debtDynamics ] ;
  grind

/-
The stationary state is a genuine fixed point of the dynamics (needs
    `r ≠ 0`).
-/
theorem stationaryState_fixed (r g p : ℝ) (hr : r ≠ 0) :
    debtStep p (stationaryState r g p) = stationaryState r g p := by
  unfold debtStep; unfold debtDynamics; unfold stationaryState;
  grind

/-
The true, degenerate "stable zone": the orbit through the stationary point
    is constant.  (This is the only orbit that stays bounded near the fixed
    point.)
-/
theorem stationaryState_orbit (r g p : ℝ) (hr : r ≠ 0) (n : ℕ) :
    (debtStep p)^[n] (stationaryState r g p) = stationaryState r g p := by
  exact Function.iterate_fixed ( stationaryState_fixed r g p hr ) n

/-
**Refutation of the former `zone_stability` axiom.**  For `r > 0` the
    stationary point is repelling, so there is *no* `ε`-neighbourhood all of
    whose orbits stay within `ε` of the stationary point: the debt deviation
    `(1 + r)^n · δ` is unbounded for any nonzero initial deviation `δ`.
-/
theorem zone_stability_refuted (r g p : ℝ) (hr : 0 < r) :
    ¬ ∃ ε > 0, ∀ S : DebtState,
      |S.debt - p / r| < ε →
      |S.buffer - (p / r * (r - g) / (1 + g) - p)| < ε →
      ∀ n : ℕ,
        |((debtStep p)^[n] S).debt - p / r| < ε ∧
        |((debtStep p)^[n] S).buffer - (p / r * (r - g) / (1 + g) - p)| < ε := by
  by_contra h_contra
  obtain ⟨ε, hε_pos, hε⟩ := h_contra;
  -- Choose n such that (1 + r)^n * (ε / 2) > ε.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 + r) ^ n * (ε / 2) > ε := by
    rcases pow_unbounded_of_one_lt ( 2 : ℝ ) ( by linarith : 1 < 1 + r ) with ⟨ n, hn ⟩ ; exact ⟨ n, by nlinarith ⟩;
  -- Consider the initial state $S$ with $S.debt = p / r + ε / 2$ and $S.buffer = p / r * (r - g) / (1 + g) - p$.
  set S : DebtState := ⟨p / r + ε / 2, p / r * (r - g) / (1 + g) - p, r, g⟩;
  specialize hε S ?_ ?_ n <;> norm_num at *;
  · simp +zetaDelta at *;
    rw [ abs_of_pos ] <;> linarith;
  · aesop;
  · -- By definition of $S$, we know that its debt after $n$ steps is $p / r + (1 + r)^n * (ε / 2)$.
    have h_debt : ((debtStep p)^[n] S).debt = p / r + (1 + r) ^ n * (ε / 2) := by
      convert debt_orbit r p hr.ne' S rfl n using 1 ; ring;
    linarith [ abs_lt.mp hε.1 ]

end UAM