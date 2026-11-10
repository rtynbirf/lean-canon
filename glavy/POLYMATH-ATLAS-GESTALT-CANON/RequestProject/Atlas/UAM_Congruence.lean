import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Green
import RequestProject.Atlas.UAM_Idempotent

/-!
# UAM — Layer 6: Конгруэнции (Congruence)

Конгруэнция — отношение эквивалентности на моноиде, совместимое с умножением.
Фактор-моноид по конгруэнции — новый моноид с индуцированным умножением.
Строим на Mathlib `Quotient` / `Setoid`, НЕ используя Mathlib `Con`.
-/

namespace UAM_Congruence
universe u

open UAM_Idempotent

/-- Конгруэнция на моноиде: эквивалентность, совместимая с умножением. -/
structure IsCongruence (M : Type u) [Monoid M] where
  r : M → M → Prop
  refl : ∀ a, r a a
  symm : ∀ a b, r a b → r b a
  trans : ∀ a b c, r a b → r b c → r a c
  mul_compat : ∀ a b c d, r a b → r c d → r (a * c) (b * d)
  one_compat : r 1 1

variable {M : Type u} [Monoid M] {θ : IsCongruence M}

/-! ### §0. Setoid и фактор-моноид -/

/-- Setoid, индуцированный конгруэнцией. -/
def congruenceSetoid (θ : IsCongruence M) : Setoid M where
  r := θ.r
  iseqv := ⟨θ.refl, fun h => θ.symm _ _ h, fun h1 h2 => θ.trans _ _ _ h1 h2⟩

/-- Фактор-моноид M/θ. -/
def QuotientMonoid (θ : IsCongruence M) : Type u :=
  Quotient (congruenceSetoid θ)

namespace QuotientMonoid

/-- Каноническая проекция M → M/θ. -/
def mk (a : M) : QuotientMonoid θ := Quotient.mk (congruenceSetoid θ) a

/-- Индуцированное умножение на фактор-моноиде. -/
instance instMonoid : Monoid (QuotientMonoid θ) where
  mul := Quotient.lift₂ (s₁ := congruenceSetoid θ) (s₂ := congruenceSetoid θ)
      (fun a b => mk (a * b))
      (by
        intro a b c d h1 h2
        exact Quotient.sound (θ.mul_compat a c b d h1 h2))
  mul_assoc := by
    refine fun x y z => Quotient.inductionOn₃ x y z ?_
    intro a b c
    show mk (a * b * c) = mk (a * (b * c))
    apply Quotient.sound
    show θ.r (a * b * c) (a * (b * c))
    rw [mul_assoc]
    exact θ.refl _
  one := mk 1
  one_mul := by
    refine fun x => Quotient.inductionOn x ?_
    intro a
    show mk (1 * a) = mk a
    apply Quotient.sound
    show θ.r (1 * a) a
    rw [one_mul]
    exact θ.refl _
  mul_one := by
    refine fun x => Quotient.inductionOn x ?_
    intro a
    show mk (a * 1) = mk a
    apply Quotient.sound
    show θ.r (a * 1) a
    rw [mul_one]
    exact θ.refl _

/-- `mk` перестановочно с умножением. -/
theorem mk_mul (a b : M) : (mk (a * b) : QuotientMonoid θ) = mk a * mk b := rfl

/-- Образ единицы — единица фактор-моноида. -/
theorem mk_one : (mk 1 : QuotientMonoid θ) = 1 := rfl

/-- Проекция сюръективна. -/
theorem mk_surjective : Function.Surjective (mk : M → QuotientMonoid θ) :=
  fun q => Quotient.exists_rep q

/-- Равенство классов эквивалентно конгруэнтности представителей. -/
theorem mk_eq_iff {a b : M} : (mk a : QuotientMonoid θ) = mk b ↔ θ.r a b := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

/-- Образ идемпотента — идемпотент. -/
theorem idempotent_mk {a : M} (h : IsIdempotent a) :
    IsIdempotent (mk a : QuotientMonoid θ) := by
  unfold IsIdempotent at h ⊢
  rw [← mk_mul, h]

/-- Если `mk a` идемпотентен, то `a * a ~_θ a`. -/
theorem idempotent_lift {a : M} (h : IsIdempotent (mk a : QuotientMonoid θ)) :
    θ.r (a * a) a := by
  have h1 : (mk (a * a) : QuotientMonoid θ) = mk a * mk a := mk_mul a a
  have h2 : (mk a : QuotientMonoid θ) * mk a = mk a := h
  exact mk_eq_iff.mp (h1.trans h2)

end QuotientMonoid

/-! ### §1. Базовые свойства конгруэнции -/

/-- Конгруэнция задаёт отношение эквивалентности. -/
theorem congruence_eqv (θ : IsCongruence M) : Equivalence θ.r :=
  ⟨θ.refl, fun h => θ.symm _ _ h, fun h1 h2 => θ.trans _ _ _ h1 h2⟩

/-- Совместимость слева. -/
theorem mul_compat_left {a b c : M} (h : θ.r a b) : θ.r (c * a) (c * b) :=
  θ.mul_compat c c a b (θ.refl c) h

/-- Совместимость справа. -/
theorem mul_compat_right {a b c : M} (h : θ.r a b) : θ.r (a * c) (b * c) :=
  θ.mul_compat a b c c h (θ.refl c)

/-- Совместимость со степенями. -/
theorem congruence_pow_compat {a b : M} (h : θ.r a b) : ∀ n : ℕ, θ.r (a ^ n) (b ^ n)
  | 0 => by simpa using θ.one_compat
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact θ.mul_compat (a ^ n) (b ^ n) a b (congruence_pow_compat h n) h

/-! ### §2. Тривиальные конгруэнции -/

/-- Тривиальная конгруэнция — равенство. -/
def trivial_congruence (M : Type u) [Monoid M] : IsCongruence M where
  r := Eq
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  trans := fun _ _ _ h1 h2 => h1.trans h2
  mul_compat := fun _ _ _ _ h1 h2 => by rw [h1, h2]
  one_compat := rfl

/-- Универсальная конгруэнция — всё связано. -/
def universal_congruence (M : Type u) [Monoid M] : IsCongruence M where
  r := fun _ _ => True
  refl := fun _ => trivial
  symm := fun _ _ _ => trivial
  trans := fun _ _ _ _ _ => trivial
  mul_compat := fun _ _ _ _ _ _ => trivial
  one_compat := trivial

end UAM_Congruence
