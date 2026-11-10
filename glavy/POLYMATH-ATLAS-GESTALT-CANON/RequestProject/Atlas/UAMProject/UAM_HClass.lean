import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Green
import RequestProject.Atlas.UAMProject.UAM_Idempotent

namespace UAMP_HClass
universe u

open UAMP_Green UAMP_Idempotent

/-- H-class of element a: {b | H_eq a b} -/
def HClass {M : Type u} [Monoid M] (a : M) : Set M := {b | H_eq a b}

/-- R is an equivalence relation -/
theorem R_isEquivalence {M : Type u} [Monoid M] :
    Equivalence (R_eq (M := M)) := ⟨R_eq.refl, R_eq.symm, R_eq.trans⟩

/-- L is an equivalence relation -/
theorem L_isEquivalence {M : Type u} [Monoid M] :
    Equivalence (L_eq (M := M)) := ⟨L_eq.refl, L_eq.symm, L_eq.trans⟩

/-- H is an equivalence relation -/
theorem H_isEquivalence {M : Type u} [Monoid M] :
    Equivalence (H_eq (M := M)) := ⟨H_eq.refl, H_eq.symm, H_eq.trans⟩

/-- Green's theorem: an idempotent is a two-sided identity on its H-class -/
theorem green_theorem {M : Type u} [Monoid M] {e a : M}
    (he : IsIdempotent e) (ha : a ∈ HClass e) : e * a = a ∧ a * e = a := by
  -- a ∈ H-class of e means R(e,a) and L(e,a)
  -- R(e,a): reach(e) = reach(a), so a ∈ reach(e), ∃ c, e * c = a
  -- L(e,a): reachLeft(e) = reachLeft(a), so a ∈ reachLeft(e), ∃ d, d * e = a
  obtain ⟨hR, hL⟩ := ha
  -- From R(e,a): a ∈ reach(e), so ∃ c, e * c = a
  have ha_in_reach_e : a ∈ UAMP_Reachability.reach e := by
    rw [hR]
    exact UAMP_Reachability.mem_reach_self a
  obtain ⟨c, hc⟩ := ha_in_reach_e
  -- From L(e,a): a ∈ reachLeft(e), so ∃ d, d * e = a
  have ha_in_reachLeft_e : a ∈ UAMP_Reachability.reachLeft e := by
    rw [hL]
    exact UAMP_Reachability.mem_reachLeft_self a
  obtain ⟨d, hd⟩ := ha_in_reachLeft_e
  -- a = e * c and a = d * e
  -- Want: e * a = a and a * e = a
  -- From e * a = e * (e * c) = (e * e) * c = e * c = a (using he: e * e = e)
  constructor
  · rw [← hc, ← mul_assoc, he]
  · rw [← hd, mul_assoc, he]

end UAMP_HClass
