import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Reachability
import RequestProject.Atlas.UAM_Green
import RequestProject.Atlas.UAM_Free

/-!
# UAM — Бесконечное начало

Этот модуль дополняет `UAM_AutomatonStops`: конечное вычисление неизбежно
оседает на идемпотенте, тогда как бесконечная алгебраическая структура может
течь, не оседая. В свободном моноиде единственный идемпотент — пустое слово,
то есть бездействие; всякое непустое действие при повторении изменяется.

Кроме того, отношения Грина свободного моноида совпадают с равенством:
у каждого слова своё собственное множество правых и левых продолжений.
-/

namespace UAM_InfiniteBeginning
universe u

open UAM_Idempotent UAM_Directionality UAM_Reachability UAM_Green

/-! ### §1. Слабая структура начала -/

/-- В слабой структуре начала единственный идемпотент — единица. -/
def IsWeakBeginningStructure (M : Type u) [Monoid M] : Prop :=
  ∀ a : M, IsIdempotent a → a = 1

/-- Пустое слово идемпотентно. -/
theorem empty_word_idempotent {α : Type u} :
    IsIdempotent ([] : UAM_Free.FreeMonoid α) := by
  rfl

/--
Непустое слово свободного моноида не бывает идемпотентным.
-/
theorem not_idempotent_of_ne {α : Type u} {w : UAM_Free.FreeMonoid α}
    (hw : w ≠ []) : ¬ IsIdempotent w := by
  cases w <;> simp_all +decide;
  rename_i x xs; intro h; have := congr_arg List.length h; simp +decide at this;
  exact absurd this ( by erw [ show ( x :: xs ) * ( x :: xs ) = x :: xs ++ x :: xs from rfl ] ; simp +arith +decide )

/--
Свободный моноид является слабой структурой начала.
Предположение о непустоте алфавита сохраняется как часть содержательной
постановки, хотя само доказательство его не использует.
-/
theorem free_monoid_weak_beginning {α : Type u} [Nonempty α] :
    IsWeakBeginningStructure (UAM_Free.FreeMonoid α) := by
  intro w hw;
  exact Classical.not_not.1 fun h => not_idempotent_of_ne h hw

/-! ### §2. Достижимость свободных слов -/

/--
У непустого слова множество правых продолжений не одноэлементно.
-/
theorem free_reach_ne_singleton {α : Type u} [Nonempty α]
    {w : UAM_Free.FreeMonoid α} (hw : w ≠ []) :
    reach w ≠ {w} := by
  contrapose! hw;
  simp_all +decide [ Set.ext_iff, reach ];
  exact absurd ( hw ( w ++ [ Classical.arbitrary α ] ) |>.1 ⟨ _, rfl ⟩ ) (by simp +decide)

/--
Из пустого слова достижимо каждое слово.
-/
theorem free_reach_empty_is_univ {α : Type u} :
    reach ([] : UAM_Free.FreeMonoid α) = Set.univ := by
  exact Set.eq_univ_iff_forall.mpr fun x => ⟨ x, by rfl ⟩

/-! ### §3. Тривиальность отношений Грина -/

/--
R-эквивалентные слова свободного моноида равны.
-/
theorem free_R_eq_trivial {α : Type u} {a b : UAM_Free.FreeMonoid α}
    (h : UAM_Green.R_eq a b) : a = b := by
  unfold R_eq at h;
  obtain ⟨c, hc⟩ : ∃ c : UAM_Free.FreeMonoid α, b ++ c = a := by
    rw [ Set.ext_iff ] at h;
    specialize h a;
    exact h.mp ⟨ 1, by simp +decide ⟩ |> fun ⟨ c, hc ⟩ => ⟨ c, hc ⟩
  obtain ⟨d, hd⟩ : ∃ d : UAM_Free.FreeMonoid α, a ++ d = b := by
    exact h.symm.subset ( Set.mem_setOf.mpr ⟨ 1, by simp +decide ⟩ );
  have hlen_c := congr_arg List.length hc
  have hlen_d := congr_arg List.length hd
  simp only [List.length_append] at hlen_c hlen_d
  have hc_zero : c.length = 0 := by
    apply Nat.add_left_cancel (n := b.length)
    apply Nat.le_antisymm
    · calc
        b.length + c.length = a.length := hlen_c
        _ ≤ a.length + d.length := Nat.le_add_right _ _
        _ = b.length := hlen_d
        _ = b.length + 0 := (Nat.add_zero _).symm
    · exact Nat.le_add_right _ _
  have hc_nil : c = [] := List.eq_nil_of_length_eq_zero hc_zero
  simpa [hc_nil] using hc.symm

/--
L-эквивалентные слова свободного моноида равны.
-/
theorem free_L_eq_trivial {α : Type u} {a b : UAM_Free.FreeMonoid α}
    (h : UAM_Green.L_eq a b) : a = b := by
  unfold L_eq at h;
  obtain ⟨c, hc⟩ : ∃ c : UAM_Free.FreeMonoid α, c ++ b = a := by
    exact h.subset ⟨ 1, by simp +decide ⟩
  obtain ⟨d, hd⟩ : ∃ d : UAM_Free.FreeMonoid α, d ++ a = b := by
    exact h.symm.subset ( Set.mem_setOf.mpr ⟨ 1, by simp +decide ⟩ );
  subst_vars;
  replace hd := congr_arg List.length hd ; simp_all +decide;
  cases c <;> cases d <;> simp_all +arith +decide

/--
H-эквивалентные слова свободного моноида равны.
-/
theorem free_H_eq_trivial {α : Type u} {a b : UAM_Free.FreeMonoid α}
    (h : UAM_Green.H_eq a b) : a = b := by
  exact free_R_eq_trivial h.1

/-! ### §4. Бесконечность даёт возможность течения -/

/--
Если свободный моноид не допускает конечной структуры, он является
слабой структурой начала. Здесь существование `Fintype` записано как
`Nonempty (Fintype ...)`, поскольку `Fintype M` — тип данных, а не `Prop`.
-/
theorem infinite_can_be_beginning {α : Type u} [Nonempty α] :
    ¬ Nonempty (Fintype (UAM_Free.FreeMonoid α)) →
    IsWeakBeginningStructure (UAM_Free.FreeMonoid α) := by
  exact fun h => free_monoid_weak_beginning

/--
Свободный моноид над непустым алфавитом не допускает конечной структуры.
Формулировка использует `¬ Nonempty (Fintype ...)`, так как отрицать сам тип
`Fintype ...` в Lean нельзя.
-/
theorem no_finite_free_monoid {α : Type u} [Nonempty α] :
    ¬ Nonempty (Fintype (UAM_Free.FreeMonoid α)) := by
  intro h
  obtain ⟨fin⟩ := h;
  exact fin.false

end UAM_InfiniteBeginning