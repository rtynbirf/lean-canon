import Mathlib

universe u

namespace UAM_Periodic

/-! ## §0. Локальные определения (дублируются из других файлов UAM) -/

-- Из UAM_Zero
def IsZero {M : Type u} [Monoid M] (z : M) : Prop :=
  (∀ x : M, z * x = z) ∧ (∀ x : M, x * z = z)

-- Из UAM_Idempotent
def IsIdempotent {M : Type u} [Monoid M] (a : M) : Prop := a * a = a

-- Из UAM_Units
def IsInvertible {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ b : M, a * b = 1 ∧ b * a = 1

-- Из UAM_Nilpotent
def IsNilpotentOf {M : Type u} [Monoid M] (a z : M) : Prop :=
  ∃ n : ℕ, 0 < n ∧ a ^ n = z

def IsNilpotent {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ z : M, IsZero z ∧ IsNilpotentOf a z

/-! ## §1. Определение -/

/-- Элемент `a` периодический: его степени обладают периодом —
    существуют такие `m > 0` и `p > 0`, что `a^(m+p) = a^m`. -/
def IsPeriodic {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ m p : ℕ, 0 < m ∧ 0 < p ∧ a ^ (m + p) = a ^ m

/-- Элемент `a` является элементом кручения (torsion): некоторая его
    положительная степень равна `1`. -/
def IsTorsion {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ n : ℕ, 0 < n ∧ a ^ n = 1

/-! ## §2. Базовые свойства -/

/-
**Теорема 1.** Элемент кручения периодичен.
-/
theorem torsion_is_periodic {M : Type u} [Monoid M] {a : M}
    (h : IsTorsion a) : IsPeriodic a := by
      obtain ⟨ n, hn, hn' ⟩ := h; exact ⟨ 1, n, by norm_num, hn, by simp_all +decide [ pow_add ] ⟩ ;

/-
**Теорема 2.** Идемпотент периодичен.
-/
theorem idempotent_is_periodic {M : Type u} [Monoid M] {a : M}
    (h : IsIdempotent a) : IsPeriodic a := by
      use 1, 1;
      simp_all +decide [ pow_succ, IsIdempotent ]

/-
**Теорема 3.** Нильпотентный элемент периодичен.
-/
theorem nilpotent_is_periodic {M : Type u} [Monoid M] {a : M}
    (h : IsNilpotent a) : IsPeriodic a := by
      obtain ⟨z, hz₁, hz₂⟩ := h;
      obtain ⟨ n, hn₁, hn₂ ⟩ := hz₂; use n, 1; simp_all +decide;
      simp +decide [ pow_succ, hn₂, hz₁.1 ]

/-
**Теорема 4.** Элемент кручения обратим.
-/
theorem torsion_is_invertible {M : Type u} [Monoid M] {a : M}
    (h : IsTorsion a) : IsInvertible a := by
      cases' h with n hn;
      induction' hn.1 with n hn ih;
      · exact ⟨ 1, by aesop ⟩;
      · exact ⟨ a ^ n, by simp_all +decide [ pow_succ' ], by simp_all +decide [ pow_succ ] ⟩

/-
**Теорема 5.** Периодический обратимый элемент — элемент кручения.
-/
theorem periodic_invertible_is_torsion {M : Type u} [Monoid M] {a : M}
    (hper : IsPeriodic a) (hinv : IsInvertible a) : IsTorsion a := by
      -- Let $b$ be the inverse of $a$.
      obtain ⟨b, hb⟩ : ∃ b, a * b = 1 ∧ b * a = 1 := hinv;
      -- By induction on $m$, we can show that $b^m * a^m = 1$.
      have h_ind : ∀ m : ℕ, b^m * a^m = 1 := by
        grind +suggestions;
      obtain ⟨ m, p, hm, hp, h ⟩ := hper;
      refine' ⟨ p, hp, _ ⟩;
      grind +suggestions

/-! ## §3. Идемпотентная степень -/

/-
**Теорема 6.** Каждый периодический элемент порождает идемпотент.
-/
theorem periodic_idempotent_power {M : Type u} [Monoid M] {a : M}
    (h : IsPeriodic a) : ∃ k : ℕ, 1 ≤ k ∧ IsIdempotent (a ^ k) := by
      -- Given a^(m+p) = a^m with m,p>0. First prove by induction that a^(m + k*p) = a^m for all k≥0.
      obtain ⟨m, p, hm, hp, h_period⟩ : ∃ m p : ℕ, 0 < m ∧ 0 < p ∧ a ^ (m + p) = a ^ m := h
      have h_ind : ∀ k : ℕ, a ^ (m + k * p) = a ^ m := by
        intro k; induction k <;> simp_all +decide [ Nat.succ_mul, ← add_assoc ] ;
        grind +suggestions;
      use m * p;
      have := h_ind ( m + m ) ; simp_all +decide [ pow_add, pow_mul ] ;
      have h_ind : ∀ k : ℕ, (a ^ m) ^ p * (a ^ k) ^ p = (a ^ m) ^ p := by
        intro k; induction' p with p hp <;> simp_all +decide [ pow_succ, mul_assoc ] ;
      exact ⟨ Nat.mul_pos hm hp, h_ind m ⟩

/-! ## §4. Конфликты -/

/-
**Теорема 7.** Torsion + Nilpotent ⇒ `1` является нулём.
-/
theorem torsion_nilpotent_zero_eq_one {M : Type u} [Monoid M] {a : M}
    (ht : IsTorsion a) (hn : IsNilpotent a) : IsZero (1 : M) := by
      obtain ⟨ z, hz₁, hz₂ ⟩ := hn;
      obtain ⟨ n, hn, h ⟩ := hz₂;
      obtain ⟨ b, hb₁, hb₂ ⟩ := torsion_is_invertible ht;
      have hz1 : z * (b ^ n) = 1 := by
        rw [ ← h ]
        exact pow_mul_pow_eq_one n hb₁
      have := hz₁.1 ( b ^ n ) ; aesop;

/-! ## §5. Коммутативный моноид -/

/-
**Теорема 8.** Произведение элементов кручения — элемент кручения.
-/
theorem commutative_torsion_mul {M : Type u} [CommMonoid M] {a b : M}
    (ha : IsTorsion a) (hb : IsTorsion b) : IsTorsion (a * b) := by
      obtain ⟨ n, hn, hn' ⟩ := ha
      obtain ⟨ m, hm, hm' ⟩ := hb
      use n * m
      simp;
      simp_all +decide [ pow_mul', mul_pow ];
      rw [ ← pow_mul, mul_comm, pow_mul, hn', one_pow ]

/-! ## §6. Конечные моноиды -/

/-
**Теорема 9.** В конечном моноиде каждый элемент периодичен.
-/
theorem fintype_is_periodic {M : Type u} [Monoid M] [Fintype M]
    (a : M) : IsPeriodic a := by
      -- By definition of exponentiation in a finite monoid, the sequence $a, a^2, a^3, \ldots$ must eventually repeat.
      have h_seq_repeat : ∃ i j : ℕ, i < j ∧ a ^ i = a ^ j := by
        by_contra h_contra;
        exact absurd ( Set.infinite_range_of_injective ( fun i j hij => le_antisymm ( not_lt.1 fun hi => h_contra ⟨ j, i, hi, hij.symm ⟩ ) ( not_lt.1 fun hj => h_contra ⟨ i, j, hj, hij ⟩ ) ) ) ( Set.not_infinite.mpr <| Set.toFinite _ );
      obtain ⟨ i, j, hij, h ⟩ := h_seq_repeat;
      use i + 1, j - i;
      simp +decide [ add_right_comm, pow_add, hij.le, h ];
      exact hij

/-
**Теорема 10.** В конечном моноиде обратимый элемент — элемент кручения.
-/
theorem fintype_torsion_of_invertible {M : Type u} [Monoid M] [Fintype M] {a : M}
    (hinv : IsInvertible a) : IsTorsion a := by
      convert fintype_is_periodic a |> fun h => periodic_invertible_is_torsion h hinv

/-! ## §7. Примеры -/

/-
**Теорема 11.** В `ℕ` элемент периодичен тогда и только тогда, когда `a ≤ 1`.
-/
theorem Nat.periodic_iff_le_one (a : ℕ) :
    IsPeriodic a ↔ a ≤ 1 := by
      constructor <;> intro h;
      · cases' h with m hm;
        rcases a with ( _ | _ | a ) <;> simp_all +decide [ pow_add ];
      · interval_cases a <;> exists 1, 1

/-
**Теорема 12.** В свободном моноиде элемент периодичен ⇔ он равен `1`.
-/
theorem FreeMonoid.periodic_iff_eq_one {α : Type u} [Nonempty α]
    (w : FreeMonoid α) : IsPeriodic w ↔ w = 1 := by
      constructor <;> intro h;
      · have := h;
        obtain ⟨ m, p, hm, hp, hmp ⟩ := this;
        replace hmp := congr_arg FreeMonoid.length hmp ; simp_all +decide [ pow_add ];
        induction hp <;> simp_all +decide [ pow_succ' ];
      · exact ⟨ 1, 1, by simp +decide [ h ] ⟩

/-! ## §8. Степени периодических элементов -/

/-
**Теорема 13.** Положительная степень периодического элемента периодична.
-/
theorem periodic_pow {M : Type u} [Monoid M] {a : M} {k : ℕ}
    (h : IsPeriodic a) (hk : 1 ≤ k) : IsPeriodic (a ^ k) := by
      obtain ⟨ m, p, hm, hp, hmp ⟩ := h;
      -- By induction on $t$, we can show that $a^{m+tp} = a^m$ for all $t \geq 0$.
      have h_ind : ∀ t : ℕ, a ^ (m + t * p) = a ^ m := by
        intro t; induction t <;> simp_all +decide [ Nat.succ_mul, ← add_assoc ] ;
        simp_all +decide [ pow_add ];
      refine' ⟨ m, k * p, hm, by positivity, _ ⟩;
      rw [ ← pow_mul, mul_comm, pow_mul ];
      rw [ h_ind k, ← pow_mul, mul_comm, pow_mul ]

/-
**Теорема 14.** `a^k` — элемент кручения ⇔ `a` — элемент кручения.
-/
theorem torsion_pow_iff {M : Type u} [Monoid M] (a : M) (k : ℕ) (hk : 1 ≤ k) :
    IsTorsion (a ^ k) ↔ IsTorsion a := by
      constructor <;> intro h;
      · obtain ⟨ n, hn, hn' ⟩ := h;
        exact ⟨ k * n, Nat.mul_pos hk hn, by rw [ pow_mul, hn' ] ⟩;
      · obtain ⟨ n, hn, hn' ⟩ := h;
        exact ⟨ n, hn, by rw [ pow_right_comm, hn', one_pow ] ⟩

/-! ## §9. Самодвойственность -/

/-
**Теорема 15.** Периодичность самодвойственна.
-/
theorem periodic_iff_op {M : Type u} [Monoid M] (a : M) :
    IsPeriodic a ↔ IsPeriodic (MulOpposite.op a) := by
      simp +decide only [IsPeriodic, ← MulOpposite.op_pow];
      simp +decide only [MulOpposite.op_inj]

/-
**Теорема 16.** Кручение самодвойственно.
-/
theorem torsion_iff_op {M : Type u} [Monoid M] (a : M) :
    IsTorsion a ↔ IsTorsion (MulOpposite.op a) := by
      simp +decide [ IsTorsion ];
      simp +decide [ ← MulOpposite.op_pow ]

end UAM_Periodic