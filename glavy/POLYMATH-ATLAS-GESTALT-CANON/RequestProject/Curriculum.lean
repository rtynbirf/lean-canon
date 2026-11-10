import RequestProject.Dependency

/-!
# Траектория изучения (curriculum) графа знаний

Практическое следствие ацикличности: объекты графа знаний можно выстроить
в линейную последовательность так, что каждая предпосылка изучается строго
раньше того, что на неё опирается (топологический порядок). Именно это
превращает граф знаний в учебную траекторию.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

namespace KnowledgeGraph

variable (g : KnowledgeGraph)

/-- Траектория изучения: перечисление всех объектов графа без повторов,
в котором любая предпосылка стоит строго раньше зависящего от неё объекта. -/
def Curriculum (l : List ℕ) : Prop :=
  (∀ i, i ∈ l ↔ i ∈ g.ids) ∧ l.Nodup ∧ ∀ a b, g.Dep a b → l.idxOf b < l.idxOf a

/-- **Существование корректной траектории изучения.** Любой ациклический
граф знаний допускает линейный порядок изучения, согласованный со всеми
зависимостями. -/
theorem exists_curriculum (hac : g.Acyclic) : ∃ l : List ℕ, g.Curriculum l := by
  classical
  obtain ⟨rank, hrank⟩ := g.acyclic_iff_stratifiable.1 hac
  let r : ℕ → ℕ → Prop := fun a b => rank a ≤ rank b
  haveI : DecidableRel r := fun a b => Nat.decLe (rank a) (rank b)
  haveI : Std.Total r := ⟨fun a b => Nat.le_total (rank a) (rank b)⟩
  haveI : IsTrans ℕ r := ⟨fun _ _ _ hab hbc => Nat.le_trans hab hbc⟩
  refine ⟨List.insertionSort r g.ids.toList, ?_, ?_, ?_⟩
  · intro i
    rw [(List.perm_insertionSort r g.ids.toList).mem_iff, Finset.mem_toList]
  · exact (List.perm_insertionSort r g.ids.toList).nodup_iff.2 g.ids.nodup_toList
  · intro a b hd
    set l := List.insertionSort r g.ids.toList with hl
    have hpair : List.Pairwise r l := List.pairwise_insertionSort r _
    have hmem : ∀ i, i ∈ l ↔ i ∈ g.ids := by
      intro i
      rw [hl, (List.perm_insertionSort r g.ids.toList).mem_iff, Finset.mem_toList]
    have hsupp := g.dep_support hd
    have hal : a ∈ l := (hmem a).2 hsupp.1
    have hbl : b ∈ l := (hmem b).2 hsupp.2
    have hia : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 hal
    have hib : l.idxOf b < l.length := List.idxOf_lt_length_iff.2 hbl
    have hga : l[l.idxOf a] = a := List.getElem_idxOf hia
    have hgb : l[l.idxOf b] = b := List.getElem_idxOf hib
    have hlt : rank b < rank a := hrank a b hd
    by_contra hcon
    push_neg at hcon
    rcases Nat.lt_or_ge (l.idxOf a) (l.idxOf b) with hab | hab
    · have := List.pairwise_iff_getElem.1 hpair _ _ hia hib hab
      rw [hga, hgb] at this
      exact absurd this (by omega)
    · have heq : l.idxOf a = l.idxOf b := le_antisymm hcon hab
      have hget : l[l.idxOf a]'hia = l[l.idxOf b]'hib := by
        generalize hx : l.idxOf a = x at hia heq
        subst heq
        rfl
      have hab' : a = b := by rw [← hga, ← hgb]; exact hget
      rw [hab'] at hlt
      exact lt_irrefl _ hlt

/-- В корректной траектории все предпосылки объекта изучены раньше него. -/
theorem curriculum_premises_earlier {l : List ℕ} (h : g.Curriculum l) {a b : ℕ}
    (hd : g.Dep a b) : l.idxOf b < l.idxOf a := h.2.2 a b hd

end KnowledgeGraph

end Polymath
