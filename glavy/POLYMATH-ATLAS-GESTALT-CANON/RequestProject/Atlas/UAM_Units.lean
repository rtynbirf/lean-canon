import Mathlib

/-!
# UAM_Units — Единицы моноида (обратимые элементы)

Самодостаточный файл о единицах (обратимых элементах) моноида.
Все нужные определения из предыдущих UAM-файлов продублированы с пометкой
`-- duplicated from UAM_...`.
-/

namespace UAMUnits

universe u

variable {M : Type u}

/-! ### §0. Продублированные определения -/

/-- Правый порядок достижимости: `algLe a b := ∃ c, a * c = b`.
    -- duplicated from UAM_Directionality -/
def algLe [Monoid M] (a b : M) : Prop := ∃ c, a * c = b

/-- Правый стабилизатор элемента `a`.
    -- duplicated from UAM_Loop -/
def rightStabilizer [Monoid M] (a : M) : Set M := { c | a * c = a }

/-- Левый стабилизатор элемента `a`.
    -- duplicated from UAM_Loop -/
def leftStabilizer [Monoid M] (a : M) : Set M := { c | c * a = a }

/-- Идемпотентность.
    -- duplicated from UAM_Idempotent -/
def IsIdempotent [Monoid M] (a : M) : Prop := a * a = a

/-! ### §1. Основные определения -/

/-- `a` имеет правый обратный. -/
def HasRightInverse [Monoid M] (a : M) : Prop := ∃ b, a * b = 1

/-- `a` имеет левый обратный. -/
def HasLeftInverse [Monoid M] (a : M) : Prop := ∃ b, b * a = 1

/-- `a` двусторонне обратим. -/
def IsInvertible [Monoid M] (a : M) : Prop := ∃ b, a * b = 1 ∧ b * a = 1

/-- Множество единиц (обратимых элементов). -/
def invertibles [Monoid M] : Set M := { a | IsInvertible a }

/-! ### §2. Базовые свойства -/

/-
Единица обратима (свидетель = 1).
-/
theorem one_is_invertible [Monoid M] : IsInvertible (1 : M) := by
  exact ⟨ 1, by simp +decide ⟩

/-
Обратный к обратному — исходный элемент.
-/
theorem inv_symm [Monoid M] {a b : M} (h : a * b = 1 ∧ b * a = 1) :
    IsInvertible b := by
      exact ⟨ a, h.2, h.1 ⟩

/-
Произведение обратимых элементов обратимо.
-/
theorem mul_is_invertible [Monoid M] {a b : M}
    (ha : IsInvertible a) (hb : IsInvertible b) : IsInvertible (a * b) := by
      obtain ⟨ c, hc ⟩ := ha
      obtain ⟨ d, hd ⟩ := hb;
      use d * c;
      grind +splitImp

/-
Двусторонняя обратимость эквивалентна одновременной право- и левообратимости.
-/
theorem invertible_iff_both [Monoid M] {a : M} :
    IsInvertible a ↔ HasRightInverse a ∧ HasLeftInverse a := by
      constructor;
      · exact fun ⟨ b, hb₁, hb₂ ⟩ => ⟨ ⟨ b, hb₁ ⟩, ⟨ b, hb₂ ⟩ ⟩;
      · rintro ⟨ ⟨ b, hb ⟩, ⟨ c, hc ⟩ ⟩;
        refine' ⟨ b, hb, _ ⟩;
        have := mul_assoc c a b; aesop;

/-
Обратный единствен (когда существует двусторонне): правый обратный равен левому.
-/
theorem right_inv_eq_left_inv [Monoid M] {a b c : M}
    (h1 : a * b = 1) (h2 : c * a = 1) : b = c := by
      have := mul_assoc c a b; aesop

/-
`invertibles` — подмоноид `M`.
-/
def invertibleSubmonoid [Monoid M] : Submonoid M where
  carrier := invertibles
  mul_mem' := by
    -- If $a$ and $b$ are invertible, then there exist $a^{-1}$ and $b^{-1}$ such that $a * a^{-1} = 1$ and $b * b^{-1} = 1$.
    intro a b ha hb
    obtain ⟨a_inv, ha_inv⟩ := ha
    obtain ⟨b_inv, hb_inv⟩ := hb;
    -- By definition of invertibles, we need to show that there exists some element $c$ such that $(a * b) * c = 1$ and $c * (a * b) = 1$.
    use b_inv * a_inv;
    grind +qlia
  one_mem' := by
    exact one_is_invertible

/-! ### §3. Обратимость в специальных классах моноидов -/

/-
В `LeftCancelMonoid` правая обратимость влечёт двустороннюю.
-/
theorem leftCancel_hasRightInverse_is_invertible [LeftCancelMonoid M] {a : M}
    (h : HasRightInverse a) : IsInvertible a := by
      obtain ⟨ b, hb ⟩ := h;
      use b;
      exact ⟨ hb, by simpa [ mul_assoc, hb ] using mul_left_cancel ( show a * ( b * a ) = a * 1 by simp +decide [ ← mul_assoc, hb ] ) ⟩

/-
В `RightCancelMonoid` левая обратимость влечёт двустороннюю.
-/
theorem rightCancel_hasLeftInverse_is_invertible [RightCancelMonoid M] {a : M}
    (h : HasLeftInverse a) : IsInvertible a := by
      obtain ⟨ b, hb ⟩ := h;
      refine' ⟨ b, _, _ ⟩ <;> have := mul_assoc a b a <;> simp_all +decide

/-
В группе каждый элемент обратим.
-/
theorem Group.all_invertible [Group M] (a : M) : IsInvertible a := by
  exact ⟨ a⁻¹, mul_inv_cancel a, inv_mul_cancel a ⟩

/-! ### §4. Связь с UAM-концепциями -/

/-
Правая обратимость `a` совпадает с достижимостью `1` из `a`.
-/
theorem hasRightInverse_iff_algLe_one [Monoid M] {a : M} :
    HasRightInverse a ↔ algLe a 1 := by
      exact ⟨ fun ⟨ b, hb ⟩ => ⟨ b, hb ⟩, fun ⟨ b, hb ⟩ => ⟨ b, hb ⟩ ⟩

/-
Единственный идемпотент-единица = 1.
-/
theorem invertible_idempotent_eq_one [Monoid M] {a : M}
    (hi : IsInvertible a) (he : IsIdempotent a) : a = 1 := by
      obtain ⟨ b, hb₁, hb₂ ⟩ := hi;
      have := mul_assoc b a a; simp_all +decide [ IsIdempotent ]

/-
У единицы тривиальный правый стабилизатор.
-/
theorem invertible_rightStabilizer_eq_one [Monoid M] {a : M}
    (h : IsInvertible a) : rightStabilizer a = {1} := by
      ext c;
      obtain ⟨ b, hb ⟩ := h;
      constructor <;> intro h <;> have := mul_assoc b a c <;> simp_all +decide [ rightStabilizer ]

/-
У единицы тривиальный левый стабилизатор.
-/
theorem invertible_leftStabilizer_eq_one [Monoid M] {a : M}
    (h : IsInvertible a) : leftStabilizer a = {1} := by
      -- By definition of invertibles, we need to show that if $c \in leftStabilizer(a)$, then $c = 1$.
      ext c
      simp only [leftStabilizer, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor <;> intro h' <;> rcases h with ⟨ b, hb₁, hb₂ ⟩ <;> have := mul_assoc c a b <;> simp_all +decide

/-! ### §5. Единицы в конкретных моноидах -/

/-
В `(ℕ, *)` обратим только `1`.
-/
theorem Nat.invertible_iff_eq_one {a : ℕ} : IsInvertible a ↔ a = 1 := by
  constructor;
  · rintro ⟨ b, hb₁, hb₂ ⟩;
    nlinarith [ show b > 0 by nlinarith ];
  · exact fun h => h.symm ▸ one_is_invertible

/-
В свободном моноиде обратимо только пустое слово.
-/
theorem FreeMonoid.invertible_iff_eq_one {α : Type*} {w : FreeMonoid α} :
    IsInvertible w ↔ w = 1 := by
      constructor;
      · rintro ⟨ b, hb ⟩;
        replace hb := congr_arg FreeMonoid.toList hb.1 ; aesop;
      · rintro rfl; exact one_is_invertible;

/-! ### §6. Конечные моноиды: правая обратимость достаточна -/

/-
В конечном моноиде правая обратимость влечёт двустороннюю.
-/
theorem fintype_hasRightInverse_is_invertible [Monoid M] [Fintype M] {a : M}
    (h : HasRightInverse a) : IsInvertible a := by
      obtain ⟨ b, hb ⟩ := h;
      use b;
      exact ⟨ hb, by have := Finite.injective_iff_surjective.2 ( show Function.Surjective ( fun x => a * x ) from fun x => ⟨ b * x, by simp +decide [ ← mul_assoc, hb ] ⟩ ) ; exact this ( by simp +decide [ ← mul_assoc, hb ] ) ⟩

/-! ### §7. Самодвойственность -/

/-
Обратимость самодвойственна относительно `Mᵐᵒᵖ`.
-/
theorem isInvertible_iff_op [Monoid M] {a : M} :
    IsInvertible a ↔ IsInvertible (MulOpposite.op a) := by
      constructor <;> intro h <;> cases' h with b hb;
      · exact ⟨ MulOpposite.op b, by simpa [ mul_assoc ] using congr_arg MulOpposite.op hb.2, by simpa [ mul_assoc ] using congr_arg MulOpposite.op hb.1 ⟩;
      · exact ⟨ MulOpposite.unop b, by simpa using congr_arg MulOpposite.unop hb.2, by simpa using congr_arg MulOpposite.unop hb.1 ⟩

/-
Образ множества единиц под `op` — множество единиц в `Mᵐᵒᵖ`.
-/
theorem invertibles_op_image [Monoid M] :
    MulOpposite.op '' (invertibles : Set M) = (invertibles : Set Mᵐᵒᵖ) := by
      convert Set.ext _;
      simp +decide [ invertibles, IsInvertible ];
      simp +decide [ ← MulOpposite.unop_inj ];
      exact fun a => ⟨ fun ⟨ b, hb₁, hb₂ ⟩ => ⟨ b, hb₂, hb₁ ⟩, fun ⟨ b, hb₁, hb₂ ⟩ => ⟨ b, hb₂, hb₁ ⟩ ⟩

end UAMUnits