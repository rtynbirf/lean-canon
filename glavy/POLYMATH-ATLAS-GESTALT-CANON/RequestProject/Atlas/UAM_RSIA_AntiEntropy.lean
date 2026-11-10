import Mathlib.Tactic
import Mathlib.Data.List.Basic
import RequestProject.Atlas.UAM_Free

set_option autoImplicit false

/-!
# RSIA — антиэнтропийный цикл (Задача G)
-/

namespace UAM_RSIA

universe u

/-- Сжатие: выход не длиннее входа и отличается от него. -/
def IsCompression {α : Type u}
    (input output : UAM_Free.FreeMonoid α) : Prop :=
  output.length ≤ input.length ∧ output ≠ input

/-- Антиэнтропийный цикл: период и функция сжатия. Пустое слово уже
минимально и потому является неподвижной точкой; каждое непустое слово
сжимается строго. -/
structure AntiEntropyCycle (α : Type u) where
  /-- Период цикла. -/
  period : ℕ
  /-- Функция сжатия состояния. -/
  compress : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α
  /-- Функция действительно сжимает каждое непустое слово. -/
  compresses_nonempty : ∀ w, w ≠ [] → IsCompression w (compress w)
  /-- Пустое слово отображается в себя. -/
  compress_empty : compress [] = []

/-- После любого числа применений сжатия длина не растёт. -/
theorem compress_monotone {α : Type u} (C : AntiEntropyCycle α)
    (w : UAM_Free.FreeMonoid α) (n : ℕ) :
    (C.compress^[n] w).length ≤ w.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hEmpty : C.compress^[n] w = []
    · rw [hEmpty, C.compress_empty]
      exact Nat.zero_le _
    · exact Nat.le_trans (C.compresses_nonempty _ hEmpty).1 ih

/-- Dropping the head is a concrete anti-entropy cycle on every alphabet. -/
def dropHeadAntiEntropy (α : Type u) : AntiEntropyCycle α where
  period := 1
  compress
    | [] => []
    | _ :: rest => rest
  compresses_nonempty := by
    intro w hw
    cases w with
    | nil => exact (hw rfl).elim
    | cons head rest =>
      constructor
      · simp
      · intro hEq
        have hLength := congrArg List.length hEq
        simp at hLength
  compress_empty := rfl

/-- In particular, the corrected anti-entropy interface is inhabited. -/
theorem antiEntropyCycle_nonempty (α : Type u) :
    Nonempty (AntiEntropyCycle α) :=
  ⟨dropHeadAntiEntropy α⟩

end UAM_RSIA
