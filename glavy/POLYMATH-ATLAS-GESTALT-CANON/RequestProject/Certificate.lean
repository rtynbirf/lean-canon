import RequestProject.Verification

/-!
# Сертификат обоснованности: порядок вывода и отсутствие кругов

Модуль `RequestProject/Verification.lean` даёт вердикт «обосновано / не
обосновано».  Вердикта мало: аудит требует **предъявить порядок вывода** —
последовательность утверждений, в которой каждое опирается только на уже
выведенное.  Здесь такой сертификат строится и его корректность доказывается.

Ключевое понятие — `derivRank c`: номер шага итерации, на котором утверждение
`c` впервые выводится, то есть «глубина доказательства».  Из него следуют:

* `premise_derivRank_lt` — всякая посылка обоснованного утверждения выводится
  строго раньше него;
* `grounded_not_reaches_self` — **обоснованное утверждение не участвует
  в собственном доказательстве**: круговых рассуждений среди обоснованных
  утверждений не бывает вовсе (это усиление `not_grounded_of_circular`:
  там круг исключался по предположению, здесь — доказывается);
* `groundedSet_acyclic` — обоснованная часть графа ациклична;
* `exists_derivation_order` и `derivOrder_is_certificate` — существует
  перечисление всех обоснованных утверждений без повторов, в котором посылки
  каждого утверждения стоят строго раньше него.

Ни одной новой аксиомы модуль не вводит.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

namespace ProofGraph

variable (P : ProofGraph)

/-! ## Глубина вывода -/

open Classical in
/-- Глубина вывода утверждения: наименьший номер шага итерации, на котором
утверждение выводится (и `0` для утверждений, которые не выводятся никогда). -/
noncomputable def derivRank (c : ℕ) : ℕ :=
  if h : ∃ n, c ∈ P.iterate n then Nat.find h else 0

theorem mem_iterate_derivRank {c : ℕ} (h : P.Grounded c) :
    c ∈ P.iterate (P.derivRank c) := by
  classical
  have hex : ∃ n, c ∈ P.iterate n := P.exists_iterate_of_grounded h
  rw [derivRank, dif_pos hex]
  exact Nat.find_spec hex

theorem derivRank_le_of_mem {c n : ℕ} (h : c ∈ P.iterate n) : P.derivRank c ≤ n := by
  classical
  have hex : ∃ m, c ∈ P.iterate m := ⟨n, h⟩
  rw [derivRank, dif_pos hex]
  exact Nat.find_le h

/-- Обоснованное утверждение выводится не на нулевом шаге: на нулевом шаге
не выведено ничего. -/
theorem derivRank_pos {c : ℕ} (h : P.Grounded c) : 0 < P.derivRank c := by
  rcases Nat.eq_zero_or_pos (P.derivRank c) with h0 | hpos
  · exfalso
    have := P.mem_iterate_derivRank h
    rw [h0, iterate_zero] at this
    exact absurd this (Finset.notMem_empty c)
  · exact hpos

/-- **Посылка выводится строго раньше.**  Это и есть свойство, превращающее
`derivRank` в сертификат порядка вывода. -/
theorem premise_derivRank_lt {c p : ℕ} (h : P.Grounded c) (hp : p ∈ P.premises c) :
    P.derivRank p < P.derivRank c := by
  obtain ⟨m, hm⟩ : ∃ m, P.derivRank c = m + 1 :=
    ⟨P.derivRank c - 1, by have := P.derivRank_pos h; omega⟩
  have hmem : c ∈ P.iterate (m + 1) := by
    have := P.mem_iterate_derivRank h
    rwa [hm] at this
  rw [iterate_succ, mem_step_iff] at hmem
  rcases hmem with hax | ⟨-, hsub⟩
  · exfalso
    rw [P.axioms_leaf c hax] at hp
    exact absurd hp (Finset.notMem_empty p)
  · have : P.derivRank p ≤ m := P.derivRank_le_of_mem (hsub hp)
    omega

/-! ## Отсутствие кругов среди обоснованных утверждений -/

/-- Всё, до чего дотягивается обоснованное утверждение, само обосновано
и выведено строго раньше. -/
theorem reaches_derivRank_lt {c d : ℕ} (h : P.Grounded c) (hr : P.Reaches c d) :
    P.Grounded d ∧ P.derivRank d < P.derivRank c := by
  induction hr with
  | single hcd => exact ⟨P.grounded_of_dep h hcd, P.premise_derivRank_lt h hcd⟩
  | tail _ hlast ih =>
      exact ⟨P.grounded_of_dep ih.1 hlast, lt_trans (P.premise_derivRank_lt ih.1 hlast) ih.2⟩

/-- **Обоснованное утверждение не участвует в собственном доказательстве.**
В отличие от `not_grounded_of_circular`, где круг исключался предположением,
здесь отсутствие круга — следствие обоснованности. -/
theorem grounded_not_reaches_self {c : ℕ} (h : P.Grounded c) : ¬ P.Reaches c c :=
  fun hr => lt_irrefl (P.derivRank c) (P.reaches_derivRank_lt h hr).2

/-- Обоснованная часть графа доказательств ациклична. -/
theorem groundedSet_acyclic : ∀ c ∈ P.groundedSet, ¬ P.Reaches c c :=
  fun c hc => P.grounded_not_reaches_self ((P.mem_groundedSet_iff c).1 hc)

/-! ## Порядок вывода -/

/-- Сравнение по глубине вывода. -/
noncomputable def rankLE (a b : ℕ) : Bool := decide (P.derivRank a ≤ P.derivRank b)

theorem rankLE_trans (a b c : ℕ) (hab : P.rankLE a b = true) (hbc : P.rankLE b c = true) :
    P.rankLE a c = true := by
  simp only [rankLE, decide_eq_true_eq] at *
  omega

theorem rankLE_total (a b : ℕ) : (P.rankLE a b || P.rankLE b a) = true := by
  simp only [rankLE, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- **Порядок вывода**: все обоснованные утверждения, перечисленные по
возрастанию глубины вывода. -/
noncomputable def derivOrder : List ℕ :=
  P.groundedSet.toList.mergeSort P.rankLE

theorem derivOrder_perm : P.derivOrder.Perm P.groundedSet.toList :=
  List.mergeSort_perm _ _

theorem derivOrder_nodup : P.derivOrder.Nodup :=
  P.derivOrder_perm.nodup_iff.2 (Finset.nodup_toList _)

theorem mem_derivOrder_iff (c : ℕ) : c ∈ P.derivOrder ↔ P.Grounded c := by
  rw [P.derivOrder_perm.mem_iff, Finset.mem_toList]
  exact P.mem_groundedSet_iff c

/-- **Корректность сертификата.**  В построенном порядке ни одно утверждение
не опирается на утверждение, стоящее позже: посылки всегда выведены раньше. -/
theorem derivOrder_pairwise : P.derivOrder.Pairwise (fun a b => b ∉ P.premises a) := by
  have hsorted : P.derivOrder.Pairwise (fun a b => P.rankLE a b = true) :=
    List.pairwise_mergeSort (le := P.rankLE) P.rankLE_trans P.rankLE_total _
  refine hsorted.imp_of_mem ?_
  intro a b ha _ hle hmem
  have hga : P.Grounded a := (P.mem_derivOrder_iff a).1 ha
  have hlt : P.derivRank b < P.derivRank a := P.premise_derivRank_lt hga hmem
  simp only [rankLE, decide_eq_true_eq] at hle
  omega

/-- **Сертификат обоснованности.**  Существует перечисление всех обоснованных
утверждений — без повторов и такое, что посылки каждого утверждения стоят
строго раньше него.  Это машинно проверяемое свидетельство того, что
доказательства замкнуты. -/
theorem exists_derivation_order :
    ∃ l : List ℕ, l.Nodup ∧ (∀ c, c ∈ l ↔ P.Grounded c) ∧
      l.Pairwise (fun a b => b ∉ P.premises a) :=
  ⟨P.derivOrder, P.derivOrder_nodup, P.mem_derivOrder_iff, P.derivOrder_pairwise⟩

/-- Сводка: построенный список и есть сертификат. -/
theorem derivOrder_is_certificate :
    P.derivOrder.Nodup ∧ (∀ c, c ∈ P.derivOrder ↔ P.Grounded c) ∧
      P.derivOrder.Pairwise (fun a b => b ∉ P.premises a) :=
  ⟨P.derivOrder_nodup, P.mem_derivOrder_iff, P.derivOrder_pairwise⟩

end ProofGraph

end Polymath
