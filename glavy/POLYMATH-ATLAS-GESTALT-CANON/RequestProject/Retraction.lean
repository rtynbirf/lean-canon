import RequestProject.Certificate

/-!
# Отзыв утверждения: точная зона поражения

Модель знаний обязана отвечать на вопрос «что сломается, если утверждение
отозвано?».  В слое зависимостей это множество `Impact` (обратная
трассировка).  Здесь тот же вопрос решается на уровне *обоснованности*:
отзыв — это удаление утверждения из аксиом и из доказанных (посылки и состав
графа не меняются: утверждение остаётся в графе, но перестаёт быть
обоснованием).

Главный результат — `grounded_retract_iff`: после отзыва `x` утверждение `c`
остаётся обоснованным **тогда и только тогда**, когда оно было обосновано,
не совпадает с `x` и не опирается на `x` даже косвенно.  Отсюда
`retraction_impact_exact`: зона поражения в точности равна
`{x} ∪ Impact x`, не больше и не меньше.  Это делает анализ последствий
отзыва точным, а не консервативной оценкой сверху.

Ни одной новой аксиомы модуль не вводит.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

namespace ProofGraph

variable (P : ProofGraph)

/-! ## Операция отзыва -/

/-- Отзыв утверждения `x`: оно перестаёт быть аксиомой и перестаёт считаться
доказанным.  Состав графа и посылки не меняются. -/
def retract (x : ℕ) : ProofGraph where
  claims := P.claims
  axioms := P.axioms.erase x
  proved := P.proved.erase x
  premises := P.premises
  axioms_subset := (Finset.erase_subset _ _).trans P.axioms_subset
  proved_subset := (Finset.erase_subset _ _).trans P.proved_subset
  premises_subset := P.premises_subset
  premises_outside := P.premises_outside
  axioms_leaf := fun c hc => P.axioms_leaf c (Finset.mem_of_mem_erase hc)

@[simp] theorem retract_claims (x : ℕ) : (P.retract x).claims = P.claims := rfl

@[simp] theorem retract_premises (x : ℕ) : (P.retract x).premises = P.premises := rfl

/-- Отзыв не меняет структуры зависимостей. -/
theorem retract_dep (x a b : ℕ) : (P.retract x).Dep a b ↔ P.Dep a b := Iff.rfl

theorem retract_reaches (x a b : ℕ) : (P.retract x).Reaches a b ↔ P.Reaches a b := by
  constructor
  · exact fun h => Relation.TransGen.mono (fun _ _ hxy => (P.retract_dep x _ _).1 hxy) h
  · exact fun h => Relation.TransGen.mono (fun _ _ hxy => (P.retract_dep x _ _).2 hxy) h

/-- Отозванное утверждение больше не обосновано. -/
theorem retract_not_grounded_self (x : ℕ) : ¬ (P.retract x).Grounded x := by
  intro h
  cases h with
  | ax hax => exact (Finset.notMem_erase x P.axioms) hax
  | inf hpr _ => exact (Finset.notMem_erase x P.proved) hpr

/-- Отзыв ничего не добавляет: обоснованное после отзыва было обосновано
и до него. -/
theorem grounded_of_retract {x c : ℕ} (h : (P.retract x).Grounded c) : P.Grounded c := by
  induction h with
  | ax hax => exact Grounded.ax (Finset.mem_of_mem_erase hax)
  | inf hpr _ ih => exact Grounded.inf (Finset.mem_of_mem_erase hpr) ih

/-- **Точный критерий выживания при отзыве.**  После отзыва `x` утверждение
остаётся обоснованным ровно тогда, когда оно было обосновано, не совпадает
с `x` и не опирается на `x` даже косвенно. -/
theorem grounded_retract_iff (x c : ℕ) :
    (P.retract x).Grounded c ↔ P.Grounded c ∧ c ≠ x ∧ ¬ P.Reaches c x := by
  constructor
  · intro h
    refine ⟨P.grounded_of_retract h, ?_, ?_⟩
    · rintro rfl
      exact P.retract_not_grounded_self c h
    · intro hr
      have : (P.retract x).Grounded x :=
        (P.retract x).grounded_of_reaches h ((P.retract_reaches x c x).2 hr)
      exact P.retract_not_grounded_self x this
  · rintro ⟨h, hne, hnr⟩
    induction h with
    | @ax c hax => exact Grounded.ax (Finset.mem_erase.2 ⟨hne, hax⟩)
    | @inf c hpr hall ih =>
        refine Grounded.inf (Finset.mem_erase.2 ⟨hne, hpr⟩) ?_
        intro p hp
        have hdep : P.Dep c p := hp
        have hpne : p ≠ x := by
          rintro rfl
          exact hnr (Relation.TransGen.single hdep)
        have hpnr : ¬ P.Reaches p x := fun hr =>
          hnr (Relation.TransGen.head hdep hr)
        exact ih p hp hpne hpnr

/-- **Зона поражения отзыва точна.**  Обоснованность теряют в точности те
утверждения, которые совпадают с отозванным или опираются на него: это
множество `{x} ∪ Impact x`, не больше и не меньше. -/
theorem retraction_impact_exact (x c : ℕ) :
    (P.Grounded c ∧ ¬ (P.retract x).Grounded c) ↔
      (P.Grounded c ∧ (c = x ∨ P.Reaches c x)) := by
  rw [grounded_retract_iff]
  constructor
  · rintro ⟨hg, hfail⟩
    refine ⟨hg, ?_⟩
    by_contra hcon
    push_neg at hcon
    exact hfail ⟨hg, hcon.1, hcon.2⟩
  · rintro ⟨hg, hcase⟩
    refine ⟨hg, ?_⟩
    rintro ⟨-, hne, hnr⟩
    rcases hcase with rfl | hr
    · exact hne rfl
    · exact hnr hr

/-- Утверждение вне зоны поражения переживает отзыв: локальность правки. -/
theorem grounded_retract_of_independent {x c : ℕ} (hg : P.Grounded c) (hne : c ≠ x)
    (hnr : ¬ P.Reaches c x) : (P.retract x).Grounded c :=
  (P.grounded_retract_iff x c).2 ⟨hg, hne, hnr⟩

/-- Отзыв «листа» — утверждения, на которое никто не опирается, — не
затрагивает обоснованность ничего другого. -/
theorem retract_leaf_preserves {x : ℕ} (hleaf : ∀ a, ¬ P.Reaches a x) (c : ℕ) (hne : c ≠ x)
    (hg : P.Grounded c) : (P.retract x).Grounded c :=
  P.grounded_retract_of_independent hg hne (hleaf c)

end ProofGraph

end Polymath
