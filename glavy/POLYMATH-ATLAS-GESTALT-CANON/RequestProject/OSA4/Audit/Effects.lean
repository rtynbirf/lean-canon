/-
# OSA-4.0 — аудит алгебры эффектов

Запрос аудита: «проверь unit element: `aggregate [] = unitEffect`» и
«проверь identity: `aggregate [unitEffect, e] = e`».

Единица агрегации эффектов в ядре — уровень `E0` (эффект отсутствует);
здесь она названа `unitEffect`, и обе требуемые проверки доказаны, вместе с
полным набором законов коммутативного идемпотентного моноида, единственностью
единицы, нейтральностью единицы в любой позиции списка и критерием
`aggregate l = unitEffect`.
-/
import RequestProject.OSA4.Effects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

namespace EffectLevel

/-- Единица агрегации эффектов: «эффекта нет». -/
def unitEffect : EffectLevel := .E0

/-- **Unit element.**  Агрегат пустого списка операторов — единица. -/
@[simp] theorem aggregate_nil_eq_unit : aggregate [] = unitEffect := rfl

/-- **Identity (слева).**  `aggregate [unitEffect, e] = e`. -/
@[simp] theorem aggregate_unit_cons (e : EffectLevel) : aggregate [unitEffect, e] = e := by
  cases e <;> rfl

/-- **Identity (справа).**  `aggregate [e, unitEffect] = e`. -/
@[simp] theorem aggregate_cons_unit (e : EffectLevel) : aggregate [e, unitEffect] = e := by
  cases e <;> rfl

/-- Единица нейтральна относительно слияния слева. -/
@[simp] theorem unit_join (a : EffectLevel) : join unitEffect a = a := E0_join a

/-- Единица нейтральна относительно слияния справа. -/
@[simp] theorem join_unit (a : EffectLevel) : join a unitEffect = a := join_E0 a

/-- **Единственность единицы.**  Никакой другой уровень эффекта нейтральным
не является. -/
theorem unit_unique (u : EffectLevel) (h : ∀ a : EffectLevel, join u a = a) :
    u = unitEffect := by
  have := h .E0
  cases u <;> simp_all [join, unitEffect, rank]

/-- **Алгебра эффектов — коммутативный идемпотентный моноид** с единицей
`unitEffect`. -/
theorem effect_commutative_idempotent_monoid :
    (∀ a : EffectLevel, join unitEffect a = a) ∧
    (∀ a : EffectLevel, join a unitEffect = a) ∧
    (∀ a b c : EffectLevel, join (join a b) c = join a (join b c)) ∧
    (∀ a b : EffectLevel, join a b = join b a) ∧
    (∀ a : EffectLevel, join a a = a) :=
  ⟨unit_join, join_unit, join_assoc, join_comm, join_idem⟩

/-- Единица не меняет агрегат, где бы она ни стояла в списке. -/
theorem aggregate_insert_unit (l₁ l₂ : List EffectLevel) :
    aggregate (l₁ ++ unitEffect :: l₂) = aggregate (l₁ ++ l₂) := by
  rw [aggregate_append, aggregate_cons, unit_join, aggregate_append]

/-- Удаление всех единиц не меняет агрегат. -/
theorem aggregate_filter_unit (l : List EffectLevel) :
    aggregate (l.filter (fun e => e != unitEffect)) = aggregate l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases h : a = unitEffect
      · subst h; simp [aggregate_cons, ih]
      · rw [List.filter_cons_of_pos (by simpa using h), aggregate_cons, ih, aggregate_cons]

/-- Агрегат равен единице тогда и только тогда, когда все эффекты — единичные:
композиция безобидных шагов безобидна, и только она. -/
theorem aggregate_eq_unit_iff (l : List EffectLevel) :
    aggregate l = unitEffect ↔ ∀ e ∈ l, e = unitEffect := by
  induction l with
  | nil => simp [aggregate, unitEffect]
  | cons a t ih =>
      rw [aggregate_cons]
      constructor
      · intro h
        have ha : a = unitEffect := by
          revert h; cases a <;> cases hAgg : aggregate t <;> simp_all [join, unitEffect, rank]
        subst ha
        rw [unit_join] at h
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨by trivial, ih.mp h⟩
      · intro h
        rw [h a (by simp), unit_join]
        exact ih.mpr fun e he => h e (by simp [he])

/-- Ранг агрегата — максимум рангов: агрегация есть взятие наибольшего
уровня эффекта. -/
theorem rank_aggregate_eq_max (l : List EffectLevel) :
    (aggregate l).rank = l.foldl (fun m e => max m e.rank) 0 := by
  suffices h : ∀ (l : List EffectLevel) (x : EffectLevel),
      (l.foldl join x).rank = l.foldl (fun m e => max m e.rank) x.rank by
    simpa [aggregate, unitEffect, rank] using h l .E0
  intro l
  induction l with
  | nil => intro x; rfl
  | cons a t ih =>
      intro x
      rw [List.foldl_cons, ih, List.foldl_cons]
      congr 1
      cases x <;> cases a <;> rfl

end EffectLevel

/-- Политика эффектов выполняется ровно тогда, когда её соблюдает каждый
отдельный оператор: агрегация не может «спрятать» запрещённый эффект. -/
theorem EffectPolicy.allows_iff (p : EffectPolicy) (l : List EffectLevel) :
    p.allows l = true ↔ ∀ e ∈ l, e.rank ≤ p.maxLevel.rank := by
  induction l with
  | nil => simp [EffectPolicy.allows, EffectLevel.aggregate, EffectLevel.rank]
  | cons a t ih =>
      simp only [EffectPolicy.allows, EffectLevel.aggregate_cons, List.mem_cons,
        forall_eq_or_imp, decide_eq_true_eq] at *
      constructor
      · intro h
        have h₁ : a.rank ≤ (EffectLevel.join a (EffectLevel.aggregate t)).rank :=
          EffectLevel.rank_le_join _ _
        have h₂ : (EffectLevel.aggregate t).rank
            ≤ (EffectLevel.join a (EffectLevel.aggregate t)).rank := by
          rw [EffectLevel.join_comm]; exact EffectLevel.rank_le_join _ _
        exact ⟨le_trans h₁ h, ih.mp (le_trans h₂ h)⟩
      · rintro ⟨ha, ht⟩
        have := ih.mpr ht
        unfold EffectLevel.join
        split <;> omega

end Polymath.OSA4
