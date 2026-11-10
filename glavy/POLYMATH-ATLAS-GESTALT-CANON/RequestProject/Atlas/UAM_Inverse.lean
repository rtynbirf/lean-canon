import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_Regular           -- IsRegular
import RequestProject.Atlas.UAM_Group            -- IsUnit'
import RequestProject.Atlas.UAM_Green             -- R_eq, L_eq, H_eq

/-!
# UAM — Layer 7: Обратные полугруппы (Inverse)

Обратная полугруппа — полугруппа, в которой каждый элемент имеет единственный
внутренний обратный. Это сильнее регулярности. Ключевая теорема: идемпотенты
коммутируют, что задаёт естественный частичный порядок на них.
-/

namespace UAM_Inverse
universe u

open UAM_Directionality UAM_Idempotent UAM_Regular UAM_Group UAM_Green

variable {M : Type u} [Monoid M]

/-! ### §0. Собственные определения -/

/-- `x` является обратным элемента `a`: оба обратных соотношения выполнены. -/
def IsInverse (a x : M) : Prop :=
  a * x * a = a ∧ x * a * x = x

/-- Обратная полугруппа: каждый элемент имеет единственный обратный. -/
def IsInverseSemigroup (M : Type u) [Monoid M] : Prop :=
  ∀ a : M, ∃! x, IsInverse a x

/-! ### §1. Свойства IsInverse -/

/-- Отношение «быть обратным» симметрично. -/
theorem isInverse_symm {a x : M} (h : IsInverse a x) : IsInverse x a :=
  ⟨h.2, h.1⟩

/-- Если `x` обратен `a`, то `a * x` идемпотентен. -/
theorem isInverse_idempotent_left {a x : M} (h : IsInverse a x) :
    IsIdempotent (a * x) := by
  show a * x * (a * x) = a * x
  rw [← mul_assoc, h.1]

/-- Если `x` обратен `a`, то `x * a` идемпотентен. -/
theorem isInverse_idempotent_right {a x : M} (h : IsInverse a x) :
    IsIdempotent (x * a) := by
  show x * a * (x * a) = x * a
  rw [mul_assoc, ← mul_assoc a x a, h.1]

/-- Пара идемпотентов, порождённая обратной парой. -/
theorem isInverse_idempotent_pair {a x : M} (h : IsInverse a x) :
    IsIdempotent (a * x) ∧ IsIdempotent (x * a) :=
  ⟨isInverse_idempotent_left h, isInverse_idempotent_right h⟩

/-- Наличие обратного влечёт регулярность. -/
theorem isInverse_regular {a x : M} (h : IsInverse a x) : UAM_Regular.IsRegular a :=
  ⟨x, h.1⟩

/-- Двусторонний обратный (в смысле `IsUnit'`) является внутренним обратным. -/
theorem isInverse_of_isUnit' {a b : M} (h : a * b = 1 ∧ b * a = 1) :
    IsInverse a b := by
  constructor
  · rw [h.1, one_mul]
  · rw [h.2, one_mul]

/-- Идемпотент является обратным самому себе. -/
theorem isInverse_idempotent_self {e : M} (he : IsIdempotent e) : IsInverse e e := by
  constructor
  · show e * e * e = e; rw [he, he]
  · show e * e * e = e; rw [he, he]

/-! ### §2. Свойства обратных полугрупп -/

/-- В обратной полугруппе каждый элемент регулярен. -/
theorem inverse_semigroup_is_regular (hS : IsInverseSemigroup M) (a : M) :
    UAM_Regular.IsRegular a := by
  obtain ⟨x, hx, _⟩ := hS a
  exact ⟨x, hx.1⟩

/-- В обратной полугруппе обратный идемпотента — он сам. -/
theorem inverse_semigroup_idempotent_inverse (hS : IsInverseSemigroup M)
    {e : M} (he : IsIdempotent e) (x : M) (hx : IsInverse e x) : x = e :=
  (hS e).unique hx (isInverse_idempotent_self he)

/-- В обратной полугруппе внутренний обратный обратимого элемента совпадает
    с его групповым обратным. -/
theorem inverse_semigroup_unit_unique (hS : IsInverseSemigroup M) {a b c : M}
    (hb : IsInverse a b) (h2 : a * c = 1 ∧ c * a = 1) : b = c :=
  (hS a).unique hb (isInverse_of_isUnit' h2)

/-! ### §3. Коммутативность идемпотентов -/

/-- Произведение двух идемпотентов в обратной полугруппе снова идемпотентно. -/
theorem prod_idempotent (hS : IsInverseSemigroup M) (e f : M)
    (he : IsIdempotent e) (hf : IsIdempotent f) : IsIdempotent (e * f) := by
  -- Единственный обратный `x` элемента `e * f`.
  obtain ⟨x, hx, huniq⟩ := hS (e * f)
  have he' : e * e = e := he
  have hf' : f * f = f := hf
  -- Шаг 1: `f * x * e` — тоже обратный к `e * f`, значит совпадает с `x`.
  have hC : f * x * e = x := by
    apply huniq
    constructor
    · calc e * f * (f * x * e) * (e * f)
          = e * (f * f) * x * (e * e) * f := by simp only [mul_assoc]
        _ = e * f * x * (e * f) := by rw [hf', he']; simp only [mul_assoc]
        _ = e * f := hx.1
    · calc f * x * e * (e * f) * (f * x * e)
          = f * x * (e * e) * (f * f) * x * e := by simp only [mul_assoc]
        _ = f * x * e * f * x * e := by rw [he', hf']
        _ = f * (x * (e * f) * x) * e := by simp only [mul_assoc]
        _ = f * x * e := by rw [hx.2]
  -- Шаг 2: `x` идемпотентен.
  have hxid : IsIdempotent x := by
    show x * x = x
    calc x * x = (f * x * e) * (f * x * e) := by rw [hC]
      _ = f * (x * (e * f) * x) * e := by simp only [mul_assoc]
      _ = f * x * e := by rw [hx.2]
      _ = x := hC
  -- Шаг 3: обратный идемпотента единствен, значит `e * f = x`.
  have hefx : e * f = x :=
    inverse_semigroup_idempotent_inverse hS hxid (e * f) (isInverse_symm hx)
  show (e * f) * (e * f) = e * f
  rw [hefx]; exact hxid

/-- В обратной полугруппе идемпотенты коммутируют. -/
theorem idempotents_commute (hS : IsInverseSemigroup M) (e f : M)
    (he : IsIdempotent e) (hf : IsIdempotent f) : e * f = f * e := by
  -- Произведения идемпотентов идемпотентны.
  have hef : IsIdempotent (e * f) := prod_idempotent hS e f he hf
  have hfe : IsIdempotent (f * e) := prod_idempotent hS f e hf he
  have he' : e * e = e := he
  have hf' : f * f = f := hf
  -- `f * e` является обратным к `e * f`.
  have hinv : IsInverse (e * f) (f * e) := by
    constructor
    · calc e * f * (f * e) * (e * f)
          = e * (f * f) * (e * e) * f := by simp only [mul_assoc]
        _ = e * f * (e * f) := by rw [hf', he']; simp only [mul_assoc]
        _ = e * f := hef
    · calc f * e * (e * f) * (f * e)
          = f * (e * e) * (f * f) * e := by simp only [mul_assoc]
        _ = f * e * (f * e) := by rw [he', hf']; simp only [mul_assoc]
        _ = f * e := hfe
  -- `e * f` идемпотентен, значит его единственный обратный — он сам.
  have hfe_eq : f * e = e * f :=
    inverse_semigroup_idempotent_inverse hS hef (f * e) hinv
  exact hfe_eq.symm

/-! ### §4. Естественный порядок на идемпотентах -/

/-- Естественный порядок на идемпотентах: `e ≤ f ↔ e = e * f`. -/
def naturalOrder (e f : M) : Prop := e = e * f

/-- Рефлексивность естественного порядка на идемпотентах. -/
theorem natural_order_refl {e : M} (he : IsIdempotent e) : naturalOrder e e :=
  he.symm

/-- Транзитивность естественного порядка (не требует коммутативности). -/
theorem natural_order_trans {e f g : M}
    (h1 : naturalOrder e f) (h2 : naturalOrder f g) : naturalOrder e g := by
  show e = e * g
  calc e = e * f := h1
    _ = e * (f * g) := by rw [← h2]
    _ = (e * f) * g := by rw [mul_assoc]
    _ = e * g := by rw [← h1]

/-- Антисимметричность естественного порядка (использует коммутативность идемпотентов). -/
theorem natural_order_antisymm (hS : IsInverseSemigroup M) {e f : M}
    (he : IsIdempotent e) (hf : IsIdempotent f)
    (h1 : naturalOrder e f) (h2 : naturalOrder f e) : e = f := by
  calc e = e * f := h1
    _ = f * e := idempotents_commute hS e f he hf
    _ = f := h2.symm

/-- Антисимметричность без явных гипотез идемпотентности: они выводятся из
    `naturalOrder`. -/
theorem natural_order_of_antisymm (hS : IsInverseSemigroup M) {e f : M}
    (h1 : naturalOrder e f) (h2 : naturalOrder f e) : e = f := by
  -- Идемпотентность выводится: e * e = (e * f) * e = e * (f * e) = e * f = e.
  have he : IsIdempotent e := by
    show e * e = e
    calc e * e = (e * f) * e := by rw [← h1]
      _ = e * (f * e) := by rw [mul_assoc]
      _ = e * f := by rw [← h2]
      _ = e := h1.symm
  have hf : IsIdempotent f := by
    show f * f = f
    calc f * f = (f * e) * f := by rw [← h2]
      _ = f * (e * f) := by rw [mul_assoc]
      _ = f * e := by rw [← h1]
      _ = f := h2.symm
  exact natural_order_antisymm hS he hf h1 h2

end UAM_Inverse