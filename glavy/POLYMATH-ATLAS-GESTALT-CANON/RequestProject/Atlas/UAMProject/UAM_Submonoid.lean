import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Green

namespace UAMP_Submonoid
universe u

/-- Custom Submonoid structure (NOT Mathlib's Submonoid) -/
structure Submonoid (M : Type u) [Monoid M] where
  carrier : Set M
  one_mem : (1 : M) ∈ carrier
  mul_mem : ∀ a b : M, a ∈ carrier → b ∈ carrier → a * b ∈ carrier

/-- Trivial submonoid: {1} -/
def trivial (M : Type u) [Monoid M] : Submonoid M where
  carrier := {1}
  one_mem := rfl
  mul_mem := by
    intros a b ha hb
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb, Set.mem_singleton_iff, mul_one]

/-- Top submonoid: the whole monoid -/
def top (M : Type u) [Monoid M] : Submonoid M where
  carrier := Set.univ
  one_mem := Set.mem_univ _
  mul_mem := by
    intros _ _ _ _
    exact Set.mem_univ _

/-- Intersection of two submonoids -/
def inter {M : Type u} [Monoid M] (S T : Submonoid M) : Submonoid M where
  carrier := S.carrier ∩ T.carrier
  one_mem := ⟨S.one_mem, T.one_mem⟩
  mul_mem := by
    intros a b ha hb
    exact ⟨S.mul_mem a b ha.1 hb.1, T.mul_mem a b ha.2 hb.2⟩

/-- Image of a Mathlib monoid homomorphism -/
def image {M N : Type u} [Monoid M] [Monoid N] (f : M →* N) (S : Submonoid M) :
    Submonoid N where
  carrier := f '' S.carrier
  one_mem := ⟨1, S.one_mem, f.map_one⟩
  mul_mem := by
    intros a b ha hb
    obtain ⟨x, hx, hx'⟩ := ha
    obtain ⟨y, hy, hy'⟩ := hb
    refine ⟨x * y, S.mul_mem x y hx hy, ?_⟩
    rw [f.map_mul, hx', hy']

/-- Preimage of a Mathlib monoid homomorphism -/
def preimage {M N : Type u} [Monoid M] [Monoid N] (f : M →* N) (T : Submonoid N) :
    Submonoid M where
  carrier := f ⁻¹' T.carrier
  one_mem := by
    simp only [Set.mem_preimage, map_one]
    exact T.one_mem
  mul_mem := by
    intros a b ha hb
    simp only [Set.mem_preimage] at ha hb ⊢
    rw [f.map_mul]
    exact T.mul_mem _ _ ha hb

/-- Local right monoid eMe: {e * m * e | m ∈ M}. Note: 1 ∉ eMe in general. -/
def eMe {M : Type u} [Monoid M] (e : M) : Set M :=
  {b | ∃ m : M, e * m * e = b}

/- Архивная формулировка

theorem H_subset_eMe (h : H_eq e a) : a ∈ eMe e

неверна без предположения об идемпотентности `e`: например, в свободном моноиде
H-классы одноэлементны, и для `e = a = [x]` имеем `a ∉ eMe e`.
Ниже доказана верная версия (для идемпотентного `e`) вместе с леммами Грина. -/

theorem idem_mul_left {M : Type u} [Monoid M] {e a : M} (he : e * e = e)
    (h : UAMP_Green.H_eq e a) : e * a = a := by
  have ha_in : a ∈ UAMP_Reachability.reach e := by
    rw [h.1]; exact UAMP_Reachability.mem_reach_self a
  obtain ⟨c, hc⟩ := ha_in
  rw [← hc, ← mul_assoc, he]

theorem idem_mul_right {M : Type u} [Monoid M] {e a : M} (he : e * e = e)
    (h : UAMP_Green.H_eq e a) : a * e = a := by
  have ha_in : a ∈ UAMP_Reachability.reachLeft e := by
    rw [h.2]; exact UAMP_Reachability.mem_reachLeft_self a
  obtain ⟨d, hd⟩ := ha_in
  rw [← hd, mul_assoc, he]

theorem H_subset_eMe {M : Type u} [Monoid M] {e a : M} (he : e * e = e)
    (h : UAMP_Green.H_eq e a) : a ∈ eMe e :=
  ⟨a, by rw [idem_mul_left he h, idem_mul_right he h]⟩

end UAMP_Submonoid
