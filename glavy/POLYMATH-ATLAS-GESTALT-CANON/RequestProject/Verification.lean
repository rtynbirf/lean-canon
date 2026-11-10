import RequestProject.ProofGraph

/-!
# Разрешимость верификации: алгоритм проверки замкнутости доказательств

Предикат `ProofGraph.Grounded` («утверждение обосновано») определён
индуктивно — как *наименьший* предикат, замкнутый относительно двух правил
(аксиома; доказанное утверждение со всеми обоснованными посылками).  Такое
определение ничего не говорит о том, как обоснованность **проверить**.

Этот модуль строит алгоритм и доказывает его корректность:

* `step` — один шаг вывода: множество утверждений, обоснованных при уже
  обоснованном множестве `S`;
* `iterate` — итерация шага от пустого множества;
* `groundedSet` — результат `claims.card` итераций;
* `mem_groundedSet_iff` — **корректность и полнота**: `c ∈ groundedSet`
  тогда и только тогда, когда `Grounded c`;
* `instDecidableGrounded` — как следствие, обоснованность **разрешима**;
* `groundedSet_step` и `grounded_least` — `groundedSet` есть наименьшая
  неподвижная точка оператора вывода, то есть индуктивное определение
  обоснованности и алгоритм описывают один и тот же объект;
* `verified` — булев вердикт верификации всего графа доказательств, и
  `verified_eq_true_iff` — его согласованность с математическим определением;
* мост к графу знаний: `KnowledgeGraph.verifiedBy` — проверка того, что все
  объекты графа знаний обоснованы, вместе с доказательством согласованности.

Ни одной новой аксиомы модуль не вводит.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

namespace ProofGraph

variable (P : ProofGraph)

/-! ## Оператор вывода -/

/-- Один шаг вывода: аксиомы и те доказанные утверждения, все посылки
которых уже лежат в `S`. -/
def step (S : Finset ℕ) : Finset ℕ :=
  P.axioms ∪ P.proved.filter (fun c => P.premises c ⊆ S)

theorem mem_step_iff (S : Finset ℕ) (c : ℕ) :
    c ∈ P.step S ↔ c ∈ P.axioms ∨ (c ∈ P.proved ∧ P.premises c ⊆ S) := by
  simp [step, Finset.mem_union, Finset.mem_filter]

/-- Оператор вывода монотонен: чем больше уже обосновано, тем больше
выводится за один шаг. -/
theorem step_mono {S T : Finset ℕ} (h : S ⊆ T) : P.step S ⊆ P.step T := by
  intro c hc
  rw [mem_step_iff] at hc ⊢
  rcases hc with hax | ⟨hpr, hsub⟩
  · exact Or.inl hax
  · exact Or.inr ⟨hpr, hsub.trans h⟩

/-- Шаг вывода не выходит за пределы графа. -/
theorem step_subset_claims (S : Finset ℕ) : P.step S ⊆ P.claims := by
  intro c hc
  rw [mem_step_iff] at hc
  rcases hc with hax | ⟨hpr, -⟩
  · exact P.axioms_subset hax
  · exact P.proved_subset hpr

/-- Итерация оператора вывода, начиная с пустого множества. -/
def iterate (Q : ProofGraph) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => Q.step (Q.iterate n)

@[simp] theorem iterate_zero : P.iterate 0 = ∅ := by simp [iterate]

@[simp] theorem iterate_succ (n : ℕ) : P.iterate (n + 1) = P.step (P.iterate n) := by
  simp [iterate]

theorem iterate_subset_claims (n : ℕ) : P.iterate n ⊆ P.claims := by
  cases n with
  | zero => simp
  | succ m => exact P.step_subset_claims _

/-- Итерация возрастает. -/
theorem iterate_subset_succ (n : ℕ) : P.iterate n ⊆ P.iterate (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih => exact P.step_mono ih

theorem iterate_mono {m n : ℕ} (h : m ≤ n) : P.iterate m ⊆ P.iterate n := by
  induction n, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k hk ih => exact ih.trans (P.iterate_subset_succ k)

/-! ## Корректность: всё вычисленное обосновано -/

/-- **Корректность алгоритма.**  Всё, что итерация выводит, действительно
обосновано: алгоритм не «выдумывает» доказательств. -/
theorem grounded_of_mem_iterate : ∀ (n : ℕ) {c : ℕ}, c ∈ P.iterate n → P.Grounded c := by
  intro n
  induction n with
  | zero => intro c hc; simp at hc
  | succ m ih =>
      intro c hc
      rw [iterate_succ, mem_step_iff] at hc
      rcases hc with hax | ⟨hpr, hsub⟩
      · exact Grounded.ax hax
      · exact Grounded.inf hpr (fun p hp => ih (hsub hp))

/-! ## Полнота: всё обоснованное вычисляется -/

/-- **Полнота алгоритма.**  Всякое обоснованное утверждение появляется на
некотором шаге итерации. -/
theorem exists_iterate_of_grounded {c : ℕ} (h : P.Grounded c) :
    ∃ n, c ∈ P.iterate n := by
  classical
  induction h with
  | @ax c hc => exact ⟨1, by rw [iterate_succ, mem_step_iff]; exact Or.inl hc⟩
  | @inf c hc _ ih =>
      set f : ℕ → ℕ := fun p => if h : ∃ n, p ∈ P.iterate n then h.choose else 0 with hf
      refine ⟨(P.premises c).sup f + 1, ?_⟩
      rw [iterate_succ, mem_step_iff]
      refine Or.inr ⟨hc, ?_⟩
      intro p hp
      have hex : ∃ n, p ∈ P.iterate n := ih p hp
      have hfp : p ∈ P.iterate (f p) := by
        rw [hf]
        simp only [dif_pos hex]
        exact hex.choose_spec
      exact P.iterate_mono (Finset.le_sup (f := f) hp) hfp

/-! ## Стабилизация итерации -/

theorem iterate_eq_of_stable {n : ℕ} (h : P.iterate n = P.iterate (n + 1)) :
    ∀ m, n ≤ m → P.iterate m = P.iterate n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [iterate_succ, ih, ← iterate_succ, ← h]

theorem card_lt_card_of_ne {n : ℕ} (h : P.iterate n ≠ P.iterate (n + 1)) :
    (P.iterate n).card < (P.iterate (n + 1)).card :=
  Finset.card_lt_card ⟨P.iterate_subset_succ n, fun hsub => h (Finset.Subset.antisymm
    (P.iterate_subset_succ n) hsub)⟩

theorem le_card_iterate {n : ℕ} (h : ∀ k < n, P.iterate k ≠ P.iterate (k + 1)) :
    n ≤ (P.iterate n).card := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ m ih =>
      have hm : m ≤ (P.iterate m).card := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hlt := P.card_lt_card_of_ne (h m (Nat.lt_succ_self m))
      omega

/-- Итерация стабилизируется не позже, чем через `claims.card` шагов:
множества строго растут внутри конечного носителя. -/
theorem exists_stable : ∃ n ≤ P.claims.card, P.iterate n = P.iterate (n + 1) := by
  by_contra hcon
  push_neg at hcon
  have h : ∀ k < P.claims.card + 1, P.iterate k ≠ P.iterate (k + 1) := by
    intro k hk
    exact hcon k (Nat.lt_succ_iff.mp hk)
  have hle := P.le_card_iterate h
  have hcard : (P.iterate (P.claims.card + 1)).card ≤ P.claims.card :=
    Finset.card_le_card (P.iterate_subset_claims _)
  omega

/-! ## Вычисленное множество обоснованных утверждений -/

/-- Множество обоснованных утверждений, вычисленное итерацией оператора
вывода. -/
def groundedSet : Finset ℕ := P.iterate P.claims.card

/-- `groundedSet` — неподвижная точка оператора вывода. -/
theorem groundedSet_step : P.step P.groundedSet = P.groundedSet := by
  obtain ⟨n, hn, heq⟩ := P.exists_stable
  have h₁ : P.iterate P.claims.card = P.iterate n := P.iterate_eq_of_stable heq _ hn
  have h₂ : P.iterate (P.claims.card + 1) = P.iterate n :=
    P.iterate_eq_of_stable heq _ (le_trans hn (Nat.le_succ _))
  calc P.step P.groundedSet = P.iterate (P.claims.card + 1) := (P.iterate_succ _).symm
    _ = P.iterate n := h₂
    _ = P.iterate P.claims.card := h₁.symm
    _ = P.groundedSet := rfl

theorem iterate_subset_groundedSet (n : ℕ) : P.iterate n ⊆ P.groundedSet := by
  rcases le_or_gt n P.claims.card with h | h
  · exact P.iterate_mono h
  · obtain ⟨k, hk, heq⟩ := P.exists_stable
    have h₁ : P.iterate n = P.iterate k :=
      P.iterate_eq_of_stable heq _ (le_of_lt (lt_of_le_of_lt hk h))
    have h₂ : P.iterate P.claims.card = P.iterate k := P.iterate_eq_of_stable heq _ hk
    rw [groundedSet, h₁, h₂]

/-- **Корректность и полнота верификации.**  Вычисленное множество — в
точности множество обоснованных утверждений. -/
theorem mem_groundedSet_iff (c : ℕ) : c ∈ P.groundedSet ↔ P.Grounded c := by
  constructor
  · exact P.grounded_of_mem_iterate _
  · intro h
    obtain ⟨n, hn⟩ := P.exists_iterate_of_grounded h
    exact P.iterate_subset_groundedSet n hn

/-- **Обоснованность разрешима.**  Замкнутость доказательства проверяется
вычислением. -/
instance instDecidableGrounded (c : ℕ) : Decidable (P.Grounded c) :=
  decidable_of_iff (c ∈ P.groundedSet) (P.mem_groundedSet_iff c)

/-- **Наименьшая неподвижная точка.**  Любое множество, замкнутое
относительно правил вывода, содержит все обоснованные утверждения: `Grounded`
не «шире», чем нужно. -/
theorem grounded_least {S : Finset ℕ} (h : P.step S ⊆ S) : P.groundedSet ⊆ S := by
  have key : ∀ n, P.iterate n ⊆ S := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [iterate_succ]; exact (P.step_mono ih).trans h
  exact key _

/-- Индуктивное определение обоснованности и алгоритм описывают один объект:
множество обоснованных утверждений — наименьшее из замкнутых. -/
theorem grounded_is_least_closed :
    P.step P.groundedSet = P.groundedSet ∧
    ∀ S : Finset ℕ, P.step S ⊆ S → ∀ c, P.Grounded c → c ∈ S := by
  refine ⟨P.groundedSet_step, ?_⟩
  intro S hS c hc
  exact P.grounded_least hS ((P.mem_groundedSet_iff c).2 hc)

/-! ## Вердикт верификации графа доказательств -/

/-- Булев вердикт: все ли утверждения графа обоснованы. -/
def verified : Bool := P.claims ⊆ P.groundedSet

/-- **Согласованность вердикта.**  Вычислимая проверка совпадает с
математическим определением полной обоснованности. -/
theorem verified_eq_true_iff : P.verified = true ↔ ∀ c ∈ P.claims, P.Grounded c := by
  rw [verified, decide_eq_true_iff]
  constructor
  · intro h c hc; exact (P.mem_groundedSet_iff c).1 (h hc)
  · intro h c hc; exact (P.mem_groundedSet_iff c).2 (h c hc)

/-- Необоснованное утверждение — это в точности контрпример к вердикту, и он
вычислим. -/
theorem not_verified_iff_exists_ungrounded :
    P.verified = false ↔ ∃ c ∈ P.claims, ¬ P.Grounded c := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have : P.verified = true := P.verified_eq_true_iff.2 (fun c hc => hcon c hc)
    rw [this] at h
    exact Bool.noConfusion h
  · rintro ⟨c, hc, hng⟩
    cases hv : P.verified with
    | false => rfl
    | true => exact absurd (P.verified_eq_true_iff.1 hv c hc) hng

/-- Полностью верифицированный граф доказательств: вердикт совпадает с
теоремой о полноте верификации из `ProofGraph.lean`. -/
theorem verified_of_acyclic (hac : P.Acyclic)
    (hjust : ∀ c ∈ P.claims, c ∈ P.axioms ∨ c ∈ P.proved) : P.verified = true :=
  P.verified_eq_true_iff.2 (P.all_grounded_of_acyclic hac hjust)

end ProofGraph

/-! ## Мост: верификация графа знаний -/

namespace KnowledgeGraph

variable (g : KnowledgeGraph)

/-- Вердикт верификации графа знаний относительно объявленных аксиом и
доказанных объектов. -/
def verifiedBy (ax pr : Finset ℕ) (hax : ax ⊆ g.ids) (hpr : pr ⊆ g.ids)
    (haxleaf : ∀ c ∈ ax, g.premises c = ∅) : Bool :=
  (g.toProofGraph ax pr hax hpr haxleaf).verified

/-- **Верификация графа знаний разрешима и корректна.**  Вердикт истинен
тогда и только тогда, когда каждый объект графа обоснован. -/
theorem verifiedBy_eq_true_iff (ax pr : Finset ℕ) (hax : ax ⊆ g.ids) (hpr : pr ⊆ g.ids)
    (haxleaf : ∀ c ∈ ax, g.premises c = ∅) :
    g.verifiedBy ax pr hax hpr haxleaf = true ↔
      ∀ o ∈ g.objects, (g.toProofGraph ax pr hax hpr haxleaf).Grounded o.id := by
  rw [verifiedBy, ProofGraph.verified_eq_true_iff]
  constructor
  · intro h o ho
    exact h o.id ((g.mem_ids_iff o.id).2 ⟨o, ho, rfl⟩)
  · intro h c hc
    obtain ⟨o, ho, rfl⟩ := (g.mem_ids_iff c).1 hc
    exact h o ho

/-- Ациклический граф знаний, каждый объект которого объявлен аксиомой или
снабжён доказательством, проходит верификацию — теперь это проверяется
вычислением. -/
theorem verifiedBy_of_acyclic (ax pr : Finset ℕ) (hax : ax ⊆ g.ids) (hpr : pr ⊆ g.ids)
    (haxleaf : ∀ c ∈ ax, g.premises c = ∅) (hacg : g.Acyclic)
    (hjust : ∀ c ∈ g.ids, c ∈ ax ∨ c ∈ pr) :
    g.verifiedBy ax pr hax hpr haxleaf = true :=
  ProofGraph.verified_of_acyclic _ (g.toPGraph_acyclic ax pr hax hpr haxleaf hacg) hjust

end KnowledgeGraph

end Polymath
