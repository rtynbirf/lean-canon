import Mathlib

namespace UAM_Nilpotent

universe u

/- §0. Локальные определения (дублируются из других модулей UAM). -/

-- Из UAM_Directionality
def algLe {M : Type u} [Monoid M] (a b : M) : Prop := ∃ c : M, a * c = b

-- Из UAM_Reachability
def reach {M : Type u} [Monoid M] (a : M) : Set M := { b | algLe a b }

-- Из UAM_Zero
def IsZero {M : Type u} [Monoid M] (z : M) : Prop :=
  (∀ x : M, z * x = z) ∧ (∀ x : M, x * z = z)

-- Из UAM_Idempotent
def IsIdempotent {M : Type u} [Monoid M] (a : M) : Prop := a * a = a

-- Из UAM_Units
def IsInvertible {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ b : M, a * b = 1 ∧ b * a = 1

-- Из UAM_Regular
def IsRegular' {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ x : M, a * x * a = a

/- §1. Определение. -/

/-- `a` является нильпотентным относительно `z`: некоторая положительная
    степень `a` равна `z`. -/
def IsNilpotentOf {M : Type u} [Monoid M] (a z : M) : Prop :=
  ∃ n : ℕ, 0 < n ∧ a ^ n = z

/-- `a` нильпотентен: существует поглощающий элемент, в который `a` переходит
    при возведении в некоторую положительную степень. -/
def IsNilpotent {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ z : M, IsZero z ∧ IsNilpotentOf a z

/-
Теорема 1.
-/
theorem nilpotent_iff_pow_is_zero {M : Type u} [Monoid M] (a : M) :
    IsNilpotent a ↔ ∃ n : ℕ, 0 < n ∧ IsZero (a ^ n) := by
      constructor;
      · rintro ⟨ z, hz, n, hn, rfl ⟩;
        use n;
      · exact fun ⟨ n, hn, h ⟩ => ⟨ _, h, n, hn, rfl ⟩

/-
§2. Базовые свойства.

Теорема 2.
-/
theorem zero_is_nilpotent {M : Type u} [Monoid M] {z : M}
    (hz : IsZero z) : IsNilpotent z := by
      use z, hz, 1; simp

/-
Теорема 3. (Гипотеза `hn : 0 < n` сохранена по спецификации, хотя
доказательство её не использует.)
-/
theorem nilpotent_pow_stabilizes {M : Type u} [Monoid M] {a z : M}
    (hz : IsZero z) {n : ℕ} : 0 < n → a ^ n = z →
    ∀ (m : ℕ), n ≤ m → a ^ m = z := by
      intro _ h m hm
      rw [ ← Nat.sub_add_cancel hm, pow_add, h ];
      exact hz.2 _

/-
Теорема 4.
-/
theorem nilpotent_idempotent_is_zero {M : Type u} [Monoid M] {a : M}
    (hnilp : IsNilpotent a) (hidem : IsIdempotent a) : IsZero a := by
      -- Since $a$ is idempotent, we have $a^k = a$ for all $k \geq 1$.
      have h_pow : ∀ k : ℕ, 0 < k → a ^ k = a := by
        intro k hk; induction hk <;> simp_all +decide [ pow_succ' ] ;
        exact hidem;
      obtain ⟨ z, hz₁, hz₂ ⟩ := hnilp; specialize h_pow ( Classical.choose hz₂ ) ( Classical.choose_spec hz₂ |>.1 ) ; have := Classical.choose_spec hz₂ |>.2; aesop;

/-
Теорема 5. (Гипотеза `hnilp` сохранена по спецификации, хотя
доказательство её не использует — равенство верно для любого `a`.)
-/
theorem nilpotent_commutes_with_zero {M : Type u} [Monoid M] {a z : M}
    (hz : IsZero z) : IsNilpotent a → a * z = z * a := by
      intro _
      rw [ hz.1, hz.2 ]

/-
Теорема 6.
-/
theorem nilpotent_invertible_zero_eq_one {M : Type u} [Monoid M] {a : M}
    (hnilp : IsNilpotent a) (hinv : IsInvertible a) : IsZero (1 : M) := by
      obtain ⟨ z, hz₁, hz₂ ⟩ := hnilp;
      have h_nilpotent_pow : ∀ n : ℕ, 0 < n → a ^ n * (hinv.choose ^ n) = 1 := by
        grind +suggestions;
      obtain ⟨ n, hn₁, hn₂ ⟩ := hz₂; specialize h_nilpotent_pow n hn₁; simp_all +decide [ IsZero ] ;

/-
§3. Коммутативный моноид.

Теорема 7.
-/
theorem commutative_nilpotent_mul {M : Type u} [CommMonoid M] {a b : M}
    (ha : IsNilpotent a) (hb : IsNilpotent b) : IsNilpotent (a * b) := by
      -- By definition of nilpotent, there exist zeros $z₁$ and $z₂$ such that $a^n = z₁$ and $b^m = z₂$, with $n, m > 0$.
      obtain ⟨z₁, hz₁⟩ := ha
      obtain ⟨z₂, hz₂⟩ := hb
      have hz₁_eq_z₂ : z₁ = z₂ := by
        have := hz₁.1.2 z₂; have := hz₂.1.1 z₁; aesop;
      refine' ⟨ z₁, _, _ ⟩ <;> simp_all +decide [ IsNilpotentOf ];
      obtain ⟨ n, hn, hn' ⟩ := hz₁; obtain ⟨ _, m, hm, hm' ⟩ := hz₂; use n + m; simp_all +decide [ pow_add, mul_pow ] ;
      simp_all +decide [ IsZero ]

/-
Теорема 8.
-/
theorem commutative_nilpotent_regular_is_zero {M : Type u} [CommMonoid M] {a : M}
    (hnilp : IsNilpotent a) (hreg : IsRegular' a) : IsZero a := by
      -- By definition of `IsNilpotent`, we have `∃ n : ℕ, 0 < n ∧ a ^ n = z` for some zero `z`.
      obtain ⟨z, hz⟩ := hnilp
      have hz_pow : IsZero (a ^ hz.right.choose) := by
        grind;
      -- Using the regularity of `a`, we can express `a` as `a = a^k * x^(k-1)` for any `k ≥ 1`.
      have h_expansion : ∀ k ≥ 1, a = a ^ k * (Classical.choose hreg) ^ (k - 1) := by
        intro k hk
        induction' hk with k hk ih;
        · simp +decide;
        · rcases k with ( _ | k ) <;> simp +decide [ pow_succ, mul_assoc ] at *;
          grind;
      specialize h_expansion ( hz.right.choose ) hz.right.choose_spec.1;
      exact h_expansion.symm ▸ by constructor <;> simp +decide [ hz_pow.1, hz_pow.2 ] ;

/-
§4. Степени нильпотентных элементов.

Теорема 9.
-/
theorem nilpotent_pow {M : Type u} [Monoid M] {a : M} {k : ℕ}
    (hnilp : IsNilpotent a) (hk : 1 ≤ k) : IsNilpotent (a ^ k) := by
      obtain ⟨ z, hz, n, hn, h ⟩ := hnilp;
      refine' ⟨ z, hz, n, hn, _ ⟩;
      rw [ ← pow_mul, mul_comm, pow_mul, h ];
      exact Nat.le_induction ( by simp ) ( fun m hm ih => by rw [ pow_succ', ih, hz.1 ] ) k hk

/-
Теорема 10.
-/
theorem nilpotent_of_pow {M : Type u} [Monoid M] {a : M} {k : ℕ}
    (hk : 1 ≤ k) (hnilp : IsNilpotent (a ^ k)) : IsNilpotent a := by
      obtain ⟨ z, hz, n, hn, hz' ⟩ := hnilp;
      exact ⟨ z, hz, k * n, by positivity, by rw [ pow_mul, hz' ] ⟩

/-
§5. Связь с достижимостью.

Теорема 11.
-/
theorem zero_reach_eq_singleton {M : Type u} [Monoid M] {z : M}
    (hz : IsZero z) : reach z = {z} := by
      ext b
      simp [reach, algLe];
      exact ⟨ fun ⟨ c, hc ⟩ => hc ▸ hz.1 c, fun hb => ⟨ 1, by simp +decide [ hb, hz.1 ] ⟩ ⟩

/-
Теорема 12.
-/
theorem zero_in_reach_of_nilpotentOf {M : Type u} [Monoid M] {a z : M}
    (h : IsNilpotentOf a z) : z ∈ reach a := by
      rcases h with ⟨ n, hn, rfl ⟩;
      exact ⟨ a ^ ( n - 1 ), by cases n <;> simp_all +decide [ pow_succ' ] ⟩

/-
Теорема 13.
-/
theorem nilpotent_reach_zero_subset {M : Type u} [Monoid M] {a : M}
    (hnilp : IsNilpotent a) (z : M) (hz : IsZero z) : reach z ⊆ reach a := by
      intro b hb;
      obtain ⟨ c, rfl ⟩ := hb;
      obtain ⟨ n, hn, h ⟩ := hnilp;
      obtain ⟨ m, hm ⟩ := h;
      obtain ⟨ k, hk ⟩ := hz;
      use a ^ ( m - 1 ) * c * z; simp_all +decide ;

/-
§6. Примеры.

Теорема 14.
-/
theorem Nat.nilpotent_iff_eq_zero (a : Nat) :
    IsNilpotent a ↔ a = 0 := by
      by_cases ha : a = 0 <;> simp_all +decide [ IsNilpotent ];
      · exact ⟨ 0, ⟨ by norm_num, by norm_num ⟩, 1, by norm_num ⟩;
      · intros x hx hnilpotent
        obtain ⟨n, hn_pos, hn_eq⟩ := hnilpotent
        have h_contra : a^n = 0 := by
          cases hx ; aesop;
        exact absurd h_contra ( pow_ne_zero _ ha )

/-
Теорема 15.
-/
theorem FreeMonoid.not_nilpotent_of_nonempty {α : Type u} [Nonempty α]
    (w : FreeMonoid α) : ¬ IsNilpotent w := by
      intro h_nilpotent
      obtain ⟨z, hz⟩ := h_nilpotent;
      have := hz.1.1 ( FreeMonoid.of ( Classical.arbitrary α ) ) ; ( have := hz.1.2 ( FreeMonoid.of ( Classical.arbitrary α ) ) ; simp_all +decide ; )

/-
§7. Самодвойственность.

Теорема 16.
-/
theorem nilpotent_iff_op {M : Type u} [Monoid M] (a : M) :
    IsNilpotent a ↔ IsNilpotent (MulOpposite.op a) := by
      constructor <;> intro h;
      · obtain ⟨ z, hz₁, hz₂ ⟩ := h;
        refine' ⟨ MulOpposite.op z, _, _ ⟩;
        · exact ⟨ fun x => by simpa using congr_arg MulOpposite.op ( hz₁.2 ( MulOpposite.unop x ) ), fun x => by simpa using congr_arg MulOpposite.op ( hz₁.1 ( MulOpposite.unop x ) ) ⟩;
        · obtain ⟨ n, hn, hn' ⟩ := hz₂;
          exact ⟨ n, hn, by simp [ ← hn' ] ⟩;
      · obtain ⟨ z, hz₁, hz₂ ⟩ := h;
        obtain ⟨ n, hn, h ⟩ := hz₂;
        refine' ⟨ MulOpposite.unop z, _, n, hn, _ ⟩;
        · constructor <;> simp_all +decide [ IsZero ];
          · exact fun x => by simpa using congr_arg MulOpposite.unop ( hz₁.2 x ) ;
          · intro x; have := hz₁.2 x; rw [ ← MulOpposite.op_inj ] ; aesop;
        · rw [ ← h, MulOpposite.unop_pow ];
          rfl

end UAM_Nilpotent