import Mathlib

/-!
# UAM_Product — Прямое произведение моноидов

Прямое произведение двух моноидов `M × N` — моноид с поточечным умножением.
UAM-концепции (достижимость, свойства элементов, отношения Грина) разлагаются
по компонентам. Файл самодостаточен: все определения дублируются здесь.

Ключевое наблюдение: `reach (a, b) = reach a ×ˢ reach b` (декартово произведение).
Из этого механически выводятся разложения отношений Грина и свойств элементов.

Примечания к формулировкам:
* В исходном промпте некоторые леммы (`reach a ×ˢ reach N b`) записаны с лишним
  аргументом `N`; здесь используется корректная запись `reach a ×ˢ reach b`.
* Теорема 18 (`D_rel_prod`) в промпте ошибочно записана через `R_eq` в правой части;
  корректная формулировка — разложение `D_rel` по компонентам.
* Теоремы 19–20 (двойственность) в промпте опирались на несуществующие в Mathlib
  имена; здесь даны корректные, доказуемые формулировки того же содержания.
-/

namespace UAM_Product
universe u

open scoped Pointwise

/-! ## §0. Определения и инфраструктура -/

-- Из UAM_Directionality
def algLe {M : Type u} [Monoid M] (a b : M) : Prop := ∃ c : M, a * c = b

-- Из UAM_Reachability
def reach {M : Type u} [Monoid M] (a : M) : Set M := { b | algLe a b }

def reachLeft {M : Type u} [Monoid M] (a : M) : Set M :=
  { b | ∃ c : M, c * a = b }

-- R-отношение Грина
def R_eq {M : Type u} [Monoid M] (a b : M) : Prop := reach a = reach b

-- L-отношение Грина
def L_eq {M : Type u} [Monoid M] (a b : M) : Prop := reachLeft a = reachLeft b

-- H-отношение Грина
def H_eq {M : Type u} [Monoid M] (a b : M) : Prop := R_eq a b ∧ L_eq a b

-- D-отношение Грина: наименьшая эквивалентность, содержащая R ∪ L
def D_rel {M : Type u} [Monoid M] (a b : M) : Prop :=
  Relation.EqvGen (fun x y => R_eq x y ∨ L_eq x y) a b

/-- reach непусто: `a ∈ reach a`. -/
theorem mem_reach_self {M : Type u} [Monoid M] (a : M) : a ∈ reach a :=
  ⟨1, mul_one a⟩

theorem reach_nonempty {M : Type u} [Monoid M] (a : M) : (reach a).Nonempty :=
  ⟨a, mem_reach_self a⟩

/-! ### Теорема 1. `reach_prod` — фундаментальная лемма -/

theorem reach_prod {M N : Type u} [Monoid M] [Monoid N] (a : M) (b : N) :
    reach (a, b) = reach a ×ˢ reach b := by
      ext ⟨ x, y ⟩ ; simp +decide [ reach, algLe ]

/-! ### Теорема 2. `reachLeft_prod` -/

theorem reachLeft_prod {M N : Type u} [Monoid M] [Monoid N] (a : M) (b : N) :
    reachLeft (a, b) = reachLeft a ×ˢ reachLeft b := by
      ext ⟨x, y⟩; simp [reachLeft]

/-! ### Теорема 3. `algLe_prod` -/

theorem algLe_prod {M N : Type u} [Monoid M] [Monoid N] (a : M) (b : N) (x : M) (y : N) :
    algLe (a, b) (x, y) ↔ algLe a x ∧ algLe b y := by
      constructor <;> intro h;
      · exact ⟨ by obtain ⟨ c, hc ⟩ := h; exact ⟨ c.1, by simpa using congr_arg Prod.fst hc ⟩, by obtain ⟨ c, hc ⟩ := h; exact ⟨ c.2, by simpa using congr_arg Prod.snd hc ⟩ ⟩;
      · exact ⟨ ⟨ h.1.choose, h.2.choose ⟩, Prod.ext h.1.choose_spec h.2.choose_spec ⟩

/-! ## §1. Свойства элементов в произведении -/

def IsIdempotent {M : Type u} [Monoid M] (a : M) : Prop := a * a = a
def IsUnit' {M : Type u} [Monoid M] (a : M) : Prop := ∃ b : M, a * b = 1 ∧ b * a = 1
def IsZero {M : Type u} [Monoid M] (z : M) : Prop := ∀ a : M, z * a = z ∧ a * z = z
def IsPeriodic {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ m p : Nat, 0 < m ∧ 0 < p ∧ a ^ (m + p) = a ^ m
def IsTorsion {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ n : Nat, 0 < n ∧ a ^ n = 1
def IsRegular' {M : Type u} [Monoid M] (a : M) : Prop := ∃ x : M, a * x * a = a
def IsNilpotent {M : Type u} [Monoid M] (a : M) : Prop :=
  ∃ z : M, IsZero z ∧ ∃ n : Nat, 0 < n ∧ a ^ n = z

/-! ### Вспомогательные леммы о степенях (для периодичности/нильпотентности) -/

/-
Сдвиг периода: из `a^(m+p) = a^m` следует `a^(k+p) = a^k` для всех `k ≥ m`.
-/
theorem pow_period_shift {M : Type u} [Monoid M] {a : M} {m p : ℕ}
    (h : a ^ (m + p) = a ^ m) {k : ℕ} (hk : m ≤ k) : a ^ (k + p) = a ^ k := by
      induction hk <;> simp_all +decide [ Nat.succ_add, pow_add ]

/-
Кратный период: из `a^(m+p) = a^m` следует `a^(k + j*p) = a^k` для всех `k ≥ m`.
-/
theorem pow_period_mult {M : Type u} [Monoid M] {a : M} {m p : ℕ}
    (h : a ^ (m + p) = a ^ m) (j : ℕ) {k : ℕ} (hk : m ≤ k) : a ^ (k + j * p) = a ^ k := by
      induction' j with j ih;
      · simp +decide;
      · convert pow_period_shift h ( show m ≤ k + j * p from by nlinarith ) using 1 ; ring_nf;
        exact ih.symm

/-
Стабилизация нуля: если `a^n = z` и `z` — нуль, то `a^k = z` для всех `k ≥ n`.
-/
theorem pow_zero_stab {M : Type u} [Monoid M] {a z : M} {n : ℕ}
    (hz : IsZero z) (h : a ^ n = z) {k : ℕ} (hk : n ≤ k) : a ^ k = z := by
      induction hk <;> simp_all +decide [ pow_succ, IsZero ]

/-! ### Теорема 4. `isIdempotent_prod` -/

theorem isIdempotent_prod {M N : Type u} [Monoid M] [Monoid N] (p : M × N) :
    IsIdempotent p ↔ IsIdempotent p.1 ∧ IsIdempotent p.2 := by
      unfold IsIdempotent; aesop;

/-! ### Теорема 5. `isUnit_prod` -/

theorem isUnit_prod {M N : Type u} [Monoid M] [Monoid N] (p : M × N) :
    IsUnit' p ↔ IsUnit' p.1 ∧ IsUnit' p.2 := by
      constructor;
      · rintro ⟨ b, hb₁, hb₂ ⟩;
        exact ⟨ ⟨ b.1, by simpa using congr_arg Prod.fst hb₁, by simpa using congr_arg Prod.fst hb₂ ⟩, ⟨ b.2, by simpa using congr_arg Prod.snd hb₁, by simpa using congr_arg Prod.snd hb₂ ⟩ ⟩;
      · rintro ⟨ ⟨ x, hx ⟩, ⟨ y, hy ⟩ ⟩;
        exact ⟨ ⟨ x, y ⟩, Prod.ext hx.1 hy.1, Prod.ext hx.2 hy.2 ⟩

/-! ### Теорема 6. `isZero_prod` -/

theorem isZero_prod {M N : Type u} [Monoid M] [Monoid N] (p : M × N) :
    IsZero p ↔ IsZero p.1 ∧ IsZero p.2 := by
      constructor <;> intro h <;> simp_all +decide [ IsZero ];
      · simp_all +decide [ Prod.ext_iff ];
        exact ⟨ fun a => ⟨ h a 1 |>.1.1, h a 1 |>.2.1 ⟩, fun a => ⟨ h 1 a |>.1.2, h 1 a |>.2.2 ⟩ ⟩;
      · aesop

/-! ### Теорема 7. `isPeriodic_prod` -/

theorem isPeriodic_prod {M N : Type u} [Monoid M] [Monoid N] (p : M × N) :
    IsPeriodic p ↔ IsPeriodic p.1 ∧ IsPeriodic p.2 := by
      constructor <;> intro h;
      · obtain ⟨ m, p, hm, hp, h ⟩ := h;
        exact ⟨ ⟨ m, p, hm, hp, by simpa using congr_arg Prod.fst h ⟩, ⟨ m, p, hm, hp, by simpa using congr_arg Prod.snd h ⟩ ⟩;
      · obtain ⟨ ⟨ m1, p1, h1, h2, h3 ⟩, ⟨ m2, p2, h4, h5, h6 ⟩ ⟩ := h;
        refine' ⟨ m1 + m2, p1 * p2, _, _, _ ⟩;
        · positivity;
        · positivity;
        · -- Using pow_period_mult, we get a^(M + q2*q1)=a^M from the a-hypothesis with j=q2, k=M≥m1; and b^(M + q1*q2)=b^M from b with j=q1, k=M≥m2.
          have h_a : p.1 ^ (m1 + m2 + p1 * p2) = p.1 ^ (m1 + m2) := by
            convert pow_period_mult h3 p2 ( by linarith : m1 ≤ m1 + m2 ) using 2;
            ring
          have h_b : p.2 ^ (m1 + m2 + p1 * p2) = p.2 ^ (m1 + m2) := by
            convert pow_period_mult h6 p1 ( by linarith : m2 ≤ m1 + m2 ) using 1;
          exact Prod.ext h_a h_b

/-! ### Теорема 8. `isTorsion_prod` -/

theorem isTorsion_prod {M N : Type u} [Monoid M] [Monoid N] (p : M × N) :
    IsTorsion p ↔ IsTorsion p.1 ∧ IsTorsion p.2 := by
      refine' ⟨ fun ⟨ n, hn, hn' ⟩ => ⟨ ⟨ n, hn, _ ⟩, ⟨ n, hn, _ ⟩ ⟩, fun ⟨ ⟨ n, hn, hn' ⟩, ⟨ m, hm, hm' ⟩ ⟩ => ⟨ n * m, Nat.mul_pos hn hm, _ ⟩ ⟩ <;> simp_all +decide [ Prod.ext_iff, pow_mul ];
      rw [ ← pow_mul, mul_comm, pow_mul, hm', one_pow ]

/-! ### Теорема 9. `isRegular_prod` -/

theorem isRegular_prod {M N : Type u} [Monoid M] [Monoid N] (p : M × N) :
    IsRegular' p ↔ IsRegular' p.1 ∧ IsRegular' p.2 := by
      unfold IsRegular'; constructor <;> intro H <;> simp_all +decide [ Prod.ext_iff ] ;

/-! ### Теорема 10. `isNilpotent_prod` -/

theorem isNilpotent_prod {M N : Type u} [Monoid M] [Monoid N] (p : M × N) :
    IsNilpotent p ↔ IsNilpotent p.1 ∧ IsNilpotent p.2 := by
      constructor <;> intro h;
      · obtain ⟨ z, hz, n, hn, h ⟩ := h;
        refine' ⟨ ⟨ z.1, _, n, hn, _ ⟩, ⟨ z.2, _, n, hn, _ ⟩ ⟩;
        · intro a; have := hz ( a, 1 ) ; aesop;
        · exact congr_arg Prod.fst h;
        · exact fun a => by have := hz ( 1, a ) ; aesop;
        · aesop;
      · rcases h with ⟨ ⟨ z1, hz1, n1, hn1, hz1' ⟩, ⟨ z2, hz2, n2, hn2, hz2' ⟩ ⟩ ; refine' ⟨ ⟨ z1, z2 ⟩, _, n1 + n2, _, _ ⟩ <;> simp_all +decide [ IsZero ] ;
        simp +decide [ *, pow_add, Prod.ext_iff ]

/-! ### Теорема 11. `commutes_prod` -/

def Commutes {M : Type u} [Monoid M] (a b : M) : Prop := a * b = b * a

theorem commutes_prod {M N : Type u} [Monoid M] [Monoid N]
    (p q : M × N) : Commutes p q ↔ Commutes p.1 q.1 ∧ Commutes p.2 q.2 := by
      simp +decide [ Commutes, Prod.ext_iff ]

/-! ## §2. Отношения Грина в произведении -/

/-! ### Теорема 12. `R_eq_prod` -/

theorem R_eq_prod {M N : Type u} [Monoid M] [Monoid N] (p q : M × N) :
    R_eq p q ↔ R_eq p.1 q.1 ∧ R_eq p.2 q.2 := by
      constructor;
      · intro h_eq
        have h_reach_eq : reach p.1 ×ˢ reach p.2 = reach q.1 ×ˢ reach q.2 := by
          rw [ ← reach_prod, ← reach_prod, h_eq ];
        apply Set.prod_eq_prod_iff_of_nonempty (Set.Nonempty.prod (reach_nonempty p.1) (reach_nonempty p.2)) |>.1 h_reach_eq;
      · intro h
        unfold R_eq at *;
        rw [ reach_prod, reach_prod, h.1, h.2 ]

/-! ### Теорема 13. `L_eq_prod` -/

theorem L_eq_prod {M N : Type u} [Monoid M] [Monoid N] (p q : M × N) :
    L_eq p q ↔ L_eq p.1 q.1 ∧ L_eq p.2 q.2 := by
      convert Set.prod_eq_prod_iff_of_nonempty _;
      · rw [ ← reachLeft_prod, ← reachLeft_prod ];
        rfl;
      · exact ⟨ p, ⟨ 1, by simp +decide ⟩, ⟨ 1, by simp +decide ⟩ ⟩

/-! ### Теорема 14. `H_eq_prod` -/

theorem H_eq_prod {M N : Type u} [Monoid M] [Monoid N] (p q : M × N) :
    H_eq p q ↔ H_eq p.1 q.1 ∧ H_eq p.2 q.2 := by
      unfold H_eq; simp +decide [ R_eq_prod, L_eq_prod ] ;
      grind

/-! ### Теорема 15. `R_eq_fst` -/

theorem R_eq_fst {M N : Type u} [Monoid M] [Monoid N] (p q : M × N)
    (h : R_eq p q) : R_eq p.1 q.1 := ((R_eq_prod p q).1 h).1

/-! ### Теорема 16. `R_eq_snd` -/

theorem R_eq_snd {M N : Type u} [Monoid M] [Monoid N] (p q : M × N)
    (h : R_eq p q) : R_eq p.2 q.2 := ((R_eq_prod p q).1 h).2

/-! ### Теорема 17. `R_eq_pair` -/

theorem R_eq_pair {M N : Type u} [Monoid M] [Monoid N]
    {a₁ a₂ : M} {b₁ b₂ : N}
    (h1 : R_eq a₁ a₂) (h2 : R_eq b₁ b₂) : R_eq (a₁, b₁) (a₂, b₂) :=
  (R_eq_prod _ _).2 ⟨h1, h2⟩

/-! Аналоги для L (нужны для D_rel). -/

theorem L_eq_fst {M N : Type u} [Monoid M] [Monoid N] (p q : M × N)
    (h : L_eq p q) : L_eq p.1 q.1 := ((L_eq_prod p q).1 h).1

theorem L_eq_snd {M N : Type u} [Monoid M] [Monoid N] (p q : M × N)
    (h : L_eq p q) : L_eq p.2 q.2 := ((L_eq_prod p q).1 h).2

theorem L_eq_pair {M N : Type u} [Monoid M] [Monoid N]
    {a₁ a₂ : M} {b₁ b₂ : N}
    (h1 : L_eq a₁ a₂) (h2 : L_eq b₁ b₂) : L_eq (a₁, b₁) (a₂, b₂) :=
  (L_eq_prod _ _).2 ⟨h1, h2⟩

/-! ### Вспомогательные леммы для D_rel -/

/-
Проекция на первую компоненту сохраняет D.
-/
theorem D_rel_proj_fst {M N : Type u} [Monoid M] [Monoid N] {p q : M × N}
    (h : D_rel p q) : D_rel p.1 q.1 := by
      induction h with
      | rel x y hxy =>
        cases hxy with
        | inl hxy => exact Relation.EqvGen.rel _ _ (Or.inl (R_eq_fst _ _ hxy))
        | inr hxy => exact Relation.EqvGen.rel _ _ (Or.inr (L_eq_fst _ _ hxy))
      | refl x => exact Relation.EqvGen.refl _
      | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-
Проекция на вторую компоненту сохраняет D.
-/
theorem D_rel_proj_snd {M N : Type u} [Monoid M] [Monoid N] {p q : M × N}
    (h : D_rel p q) : D_rel p.2 q.2 := by
      induction h;
      · rename_i x y hxy;
        cases' hxy with hxy hxy;
        · exact Relation.EqvGen.rel _ _ ( Or.inl <| R_eq_snd _ _ hxy );
        · exact Relation.EqvGen.rel _ _ ( Or.inr ( L_eq_snd _ _ hxy ) );
      · exact Relation.EqvGen.refl _;
      · exact Relation.EqvGen.symm _ _ ‹_›;
      · exact Relation.EqvGen.trans _ _ _ ‹_› ‹_›

/-
Подъём D по первой компоненте (вторая фиксирована).
-/
theorem D_rel_lift_fst {M N : Type u} [Monoid M] [Monoid N] {a₁ a₂ : M} (b : N)
    (h : D_rel a₁ a₂) : D_rel (a₁, b) (a₂, b) := by
      induction h;
      · rename_i x y h;
        cases' h with h h;
        · exact Relation.EqvGen.rel _ _ ( Or.inl <| R_eq_pair h <| by rfl );
        · apply Relation.EqvGen.rel;
          exact Or.inr ( L_eq_pair h ( by rfl ) );
      · exact Relation.EqvGen.refl _;
      · exact Relation.EqvGen.symm _ _ ‹_›;
      · exact Relation.EqvGen.trans _ _ _ ‹_› ‹_›

/-
Подъём D по второй компоненте (первая фиксирована).
-/
theorem D_rel_lift_snd {M N : Type u} [Monoid M] [Monoid N] (a : M) {b₁ b₂ : N}
    (h : D_rel b₁ b₂) : D_rel (a, b₁) (a, b₂) := by
      induction h;
      · rename_i x y hxy;
        exact Relation.EqvGen.rel _ _ ( hxy.elim ( fun h => Or.inl <| R_eq_pair ( by rfl ) h ) fun h => Or.inr <| L_eq_pair ( by rfl ) h );
      · exact Relation.EqvGen.refl _;
      · exact Relation.EqvGen.symm _ _ ‹_›;
      · exact Relation.EqvGen.trans _ _ _ ‹_› ‹_›

/-! ### Теорема 18. `D_rel_prod`
Корректная формулировка (исправлена относительно промпта): разложение `D_rel`. -/

theorem D_rel_prod {M N : Type u} [Monoid M] [Monoid N] (p q : M × N) :
    D_rel p q ↔ D_rel p.1 q.1 ∧ D_rel p.2 q.2 := by
      refine' ⟨ fun h => ⟨ D_rel_proj_fst h, D_rel_proj_snd h ⟩, _ ⟩;
      intro h
      obtain ⟨h1, h2⟩ := h
      have h3 : D_rel (p.1, p.2) (q.1, p.2) := D_rel_lift_fst p.2 h1
      have h4 : D_rel (q.1, p.2) (q.1, q.2) := D_rel_lift_snd q.1 h2
      exact Relation.EqvGen.trans _ _ _ h3 h4

/-! ## §3. Двойственность произведения -/

/-! ### Теорема 19. `prodOpEquiv` — `(M × N)ᵐᵒᵖ ≃* Mᵐᵒᵖ × Nᵐᵒᵖ`
(Корректная формулировка двойственности произведения; в Mathlib нет готового имени.) -/

noncomputable def prodOpEquiv (M N : Type u) [Monoid M] [Monoid N] :
    (M × N)ᵐᵒᵖ ≃* Mᵐᵒᵖ × Nᵐᵒᵖ where
  toFun p := (MulOpposite.op (MulOpposite.unop p).1, MulOpposite.op (MulOpposite.unop p).2)
  invFun q := MulOpposite.op ((MulOpposite.unop q.1), (MulOpposite.unop q.2))
  left_inv p := by simp
  right_inv q := by simp
  map_mul' p q := by simp

/-! ### Теорема 20. `reach_op` — двойственность reach/reachLeft
`reach (op a) = op '' reachLeft a`: достижимость в противоположном моноиде отвечает
левой достижимости. -/

theorem reach_op {M : Type u} [Monoid M] (a : M) :
    reach (MulOpposite.op a) = MulOpposite.op '' reachLeft a := by
      ext x;
      simp +decide [ reach, reachLeft, algLe ]

/-! ## §4. Коммутативное произведение -/

/-! ### Теорема 21. `commutative_reach_prod` -/

theorem commutative_reach_prod {M N : Type u} [CommMonoid M] [CommMonoid N] (a : M) (b : N) :
    reach (a, b) = reach a ×ˢ reach b := reach_prod a b

/-! ### Теорема 22. `commutative_R_eq_prod` -/

theorem commutative_R_eq_prod {M N : Type u} [CommMonoid M] [CommMonoid N] (p q : M × N) :
    R_eq p q ↔ R_eq p.1 q.1 ∧ R_eq p.2 q.2 := R_eq_prod p q

/-! ### Теорема 23. `commutative_D_eq_R_prod` -/

theorem commutative_D_eq_R_prod {M N : Type u} [CommMonoid M] [CommMonoid N] (p q : M × N) :
    D_rel p q ↔ R_eq p q := by
      refine' ⟨ fun h => _, fun h => _ ⟩;
      · induction h;
        · rename_i x y hxy;
          cases hxy <;> simp_all +decide [ R_eq, L_eq, reach, reachLeft, algLe, mul_comm ];
        · rfl;
        · exact Eq.symm ‹_›;
        · exact Eq.trans ‹_› ‹_›;
      · exact Relation.EqvGen.rel _ _ ( Or.inl h )

end UAM_Product