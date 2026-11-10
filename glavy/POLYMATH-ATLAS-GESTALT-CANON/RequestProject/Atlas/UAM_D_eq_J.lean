import Mathlib.Tactic
import RequestProject.Atlas.UAM_Green
import RequestProject.Atlas.UAM_FiniteSemigroup
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Reachability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_D_eq_J

open UAM_Green UAM_Directionality UAM_Reachability UAM_Ideal UAM_Idempotent

universe u

private theorem finite_sandwich_data {M : Type u} [Monoid M] [Fintype M]
    {a p q : M} (h : a = p * a * q) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotent (p ^ n) ∧ IsIdempotent (q ^ n) ∧
      p ^ n * a = a ∧ a * q ^ n = a := by
  -- By UAM_FiniteSemigroup.exists_idempotent_pow, there exists a positive integer n such that (p^n, q^n) is idempotent.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < n ∧ IsIdempotent (p ^ n) ∧ IsIdempotent (q ^ n) := by
    have := UAM_FiniteSemigroup.exists_idempotent_pow (p, q);
    obtain ⟨ n, hn, hn' ⟩ := this; use n; simp_all +singlePass [ IsIdempotent ] ;
  refine' ⟨ n, hn.1, hn.2.1, hn.2.2, _, _ ⟩;
  · -- By induction on $n$, we can show that $a = p^n * a * q^n$.
    have h_ind : ∀ k : ℕ, a = p ^ k * a * q ^ k := by
      intro k;
      induction' k with k ih;
      · simp +decide;
      · convert h.trans ( congr_arg₂ ( · * · ) ( congr_arg₂ ( · * · ) rfl ih ) rfl ) using 1 ; simp +decide [ pow_succ', mul_assoc ];
        rw [ ← pow_succ', ← pow_succ ];
    convert congr_arg ( fun x => p ^ n * x ) ( h_ind n ) using 1 ; simp +decide [ mul_assoc ];
    convert h_ind n using 1 ; simp +decide [ ← mul_assoc ];
    rw [ hn.2.1 ];
  · -- By induction on n, we can show that a = p^n * a * q^n for all n.
    have h_ind : ∀ n : ℕ, a = p ^ n * a * q ^ n := by
      intro n
      induction' n with n ih;
      · simp +decide;
      · convert congr_arg ( fun x => p * x * q ) ih using 1 ; simp +decide [ pow_succ', mul_assoc ];
        rw [ ← pow_succ', ← pow_succ ];
    rw [ h_ind n, mul_assoc, hn.2.2 ]

private theorem sandwich_gives_D {M : Type u} [Monoid M] [Fintype M]
    {a b x y u v : M} (hb : b = x * a * y) (ha : a = u * b * v) :
    D_eq a b := by
  revert ha hb u v x y;
  intro x y u v hb ha
  obtain ⟨n, hn_pos, hn_idempotent_p, hn_idempotent_q, hp, hq⟩ :=
    finite_sandwich_data (show a = (u * x) * a * (y * v) by
      simpa only [hb, mul_assoc] using ha)
  -- Let $c = x * a * (y * v)^n$. We will show that $a L c$ and $c R b$.
  set c := x * a * (y * v) ^ n
  have hL : L_eq a c := by
    ext z
    simp [reachLeft];
    constructor <;> rintro ⟨ w, rfl ⟩;
    · use w * (u * x) ^ (n - 1) * u;
      rcases n <;> simp +decide [ pow_succ, mul_assoc ] at *;
      simp +zetaDelta at *;
      simp +decide [ ← mul_assoc, pow_succ ];
      simp +decide [ mul_assoc, hp, hq ];
    · use w * x
      simp only [c, mul_assoc, hq]
  have hR : R_eq c b := by
    ext z;
    constructor <;> rintro ⟨ w, rfl ⟩;
    · -- Substitute $c = x * a * (y * v)^n$ into the goal.
      simp [c];
      rw [ hb ];
      use v * (y * v) ^ (n - 1) * w;
      cases n <;> simp +decide [ pow_succ', mul_assoc ] at *;
    · use y * w
      simp only [c, mul_assoc, hq, hb]
  exact D_eq_trans ( L_subset_D hL ) ( R_subset_D hR )

/-
In a finite monoid, equality of principal two-sided ideals implies Green's
`D` relation.
-/
theorem J_eq_implies_D_eq_finite {M : Type u} [Monoid M] [Fintype M]
    {a b : M} (h : J_eq a b) : D_eq a b := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : M, b = x * a * y := by
    obtain ⟨ x, hx ⟩ := Set.ext_iff.mp h b;
    obtain ⟨ x, y, hxy ⟩ := hx ( by exact ⟨ 1, 1, by simp +decide ⟩ ) ; exact ⟨ x, y, hxy.symm ⟩ ;
  obtain ⟨u, v, huv⟩ : ∃ u v : M, a = u * b * v := by
    replace h := Set.ext_iff.mp h a;
    exact h.mp ⟨ 1, 1, by simp +decide ⟩ |> fun ⟨ u, v, h ⟩ => ⟨ u, v, h ▸ by simp +decide ⟩
  exact sandwich_gives_D hxy huv

/-- For finite monoids, Green's relations `D` and `J` coincide. -/
theorem D_eq_iff_J_eq_finite {M : Type u} [Monoid M] [Fintype M]
    {a b : M} : D_eq a b ↔ J_eq a b := by
  constructor
  · exact D_eq_implies_J_eq
  · exact J_eq_implies_D_eq_finite

end UAM_D_eq_J