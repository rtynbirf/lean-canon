import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality

namespace UAMP_Reachability
universe u

/-- Right reachability set: {b | ∃ c, a * c = b} -/
def reach {M : Type u} [Monoid M] (a : M) : Set M := {b | ∃ c, a * c = b}

/-- Left reachability set: {b | ∃ c, c * a = b} -/
def reachLeft {M : Type u} [Monoid M] (a : M) : Set M := {b | ∃ c, c * a = b}

theorem mem_reach_self {M : Type u} [Monoid M] (a : M) : a ∈ reach a := ⟨1, by rw [mul_one]⟩

theorem mem_reachLeft_self {M : Type u} [Monoid M] (a : M) : a ∈ reachLeft a :=
  ⟨1, by rw [one_mul]⟩

theorem reach_mono {M : Type u} [Monoid M] {a b : M} (h : a ∈ reach b) :
    reach a ⊆ reach b := by
  rintro c ⟨d, hd⟩
  obtain ⟨e, he⟩ := h
  exact ⟨e * d, by rw [← mul_assoc, he, hd]⟩

theorem reach_left_mono {M : Type u} [Monoid M] {a b : M} (h : a ∈ reachLeft b) :
    reachLeft a ⊆ reachLeft b := by
  rintro c ⟨d, hd⟩
  obtain ⟨e, he⟩ := h
  exact ⟨d * e, by rw [mul_assoc, he, hd]⟩

theorem reach_subset_algLe {M : Type u} [Monoid M] {a b : M} (h : b ∈ reach a) :
    UAMP_Directionality.algLe a b := h

theorem reachLeft_subset_algLe {M : Type u} [Monoid M] {a b : M} (h : b ∈ reachLeft a) :
    ∃ c : M, c * a = b := h

end UAMP_Reachability
