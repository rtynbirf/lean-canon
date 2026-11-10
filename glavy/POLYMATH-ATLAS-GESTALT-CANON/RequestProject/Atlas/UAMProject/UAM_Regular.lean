import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Directionality
import RequestProject.Atlas.UAMProject.UAM_Idempotent
import RequestProject.Atlas.UAMProject.UAM_Group

namespace UAMP_Regular
universe u

/-- Element a is regular: ∃ x, a * x * a = a -/
def IsRegular {M : Type u} [Monoid M] (a : M) : Prop := ∃ x, a * x * a = a

/-- Element z is a zero: ∀ a, z * a = z ∧ a * z = z -/
def IsZero {M : Type u} [Monoid M] (z : M) : Prop := ∀ a, z * a = z ∧ a * z = z

/-- Right stabilizer of a: {x | a * x * a = a} -/
def rightStabilizer {M : Type u} [Monoid M] (a : M) : Set M := {x | a * x * a = a}

/-- Left stabilizer of a: {x | x * a * x = x} -/
def leftStabilizer {M : Type u} [Monoid M] (a : M) : Set M := {x | x * a * x = x}

theorem unit_isRegular {M : Type u} [Monoid M] (a : M) (ha : UAMP_Group.IsUnit' a) :
    IsRegular a := by
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, by rw [hb.1, one_mul]⟩

theorem idempotent_isRegular {M : Type u} [Monoid M] {a : M}
    (ha : UAMP_Idempotent.IsIdempotent a) : IsRegular a := ⟨a, by rw [ha, ha]⟩

theorem zero_isRegular {M : Type u} [Monoid M] {z : M} (hz : IsZero z) : IsRegular z := by
  -- Need: ∃ x, z * x * z = z. Use any x; z * x = z (from hz), then z * z = z (need to show)
  obtain ⟨hzl, hzr⟩ := hz z
  -- hzl: z * z = z, hzr: z * z = z (same)
  exact ⟨1, by rw [mul_one, hzl]⟩

theorem regular_produces_idempotent_pair {M : Type u} [Monoid M] {a : M}
    (h : IsRegular a) : ∃ x, UAMP_Idempotent.IsIdempotent (a * x) ∧
                          UAMP_Idempotent.IsIdempotent (x * a) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x * a * x, ?_, ?_⟩
  · -- (a * (x * a * x)) * (a * (x * a * x)) should equal a * (x * a * x)
    -- a * x * a = a (from hx), so a * (x * a * x) = (a * x * a) * x = a * x
    -- Need to show (a * x) * (a * x) = a * x
    -- (a * x) * (a * x) = a * (x * a) * x = a * x (using hx via a * x * a = a)
    show a * (x * a * x) * (a * (x * a * x)) = a * (x * a * x)
    simp only [← mul_assoc, hx]
  · -- ((x * a * x) * a) * ((x * a * x) * a) should equal (x * a * x) * a
    -- (x * a * x) * a = x * (a * x * a) = x * a (using hx)
    have h2 : x * a * x * a = x * a := by rw [mul_assoc, mul_assoc, ← mul_assoc a x a, hx]
    show x * a * x * a * (x * a * x * a) = x * a * x * a
    rw [h2, ← mul_assoc, h2]

theorem regular_dual {M : Type u} [Monoid M] {a : M} (h : IsRegular a) :
    IsRegular (MulOpposite.op a) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨MulOpposite.op x, ?_⟩
  simp only [← MulOpposite.op_mul, ← mul_assoc]
  rw [hx]

end UAMP_Regular
