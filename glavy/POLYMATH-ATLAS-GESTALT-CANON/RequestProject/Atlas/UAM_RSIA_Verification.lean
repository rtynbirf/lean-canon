import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_MyhillNerode

set_option autoImplicit false

/-!
# RSIA — верификация действий (Задача F)

`ActionAligned` — **бинарный** предикат (да/нет), дискретный аналог `cos θ = 1`
для детерминированных агентов: действие `σ` из состояния `w` согласовано с
языком `L`, если `w` и `w ++ σ` Нероуд-эквивалентны (по всем продолжениям
решение о принадлежности `L` совпадает).
-/

namespace UAM_RSIA

universe u

variable {α : Type u}

/-- Бинарная проверка согласованности действия `σ` с языком `L` из состояния `w`:
    `w` и `w ++ σ` неразличимы по правым продолжениям. -/
def ActionAligned (L : Set (UAM_Free.FreeMonoid α))
    (w σ : UAM_Free.FreeMonoid α) : Prop :=
  UAM_RegularLanguages.nerodeRel L w (w ++ σ)

/-- Пустое действие всегда согласовано. -/
theorem ActionAligned_empty (L : Set (UAM_Free.FreeMonoid α))
    (w : UAM_Free.FreeMonoid α) :
    ActionAligned L w [] := by
  unfold ActionAligned
  intro v
  simp only [List.append_nil]

/-- Согласованность рефлексивна относительно пустого расширения: то же, что
    `ActionAligned_empty`, но выраженное как `nerodeRel`-рефлексивность. -/
theorem ActionAligned_self (L : Set (UAM_Free.FreeMonoid α))
    (w : UAM_Free.FreeMonoid α) :
    UAM_RegularLanguages.nerodeRel L w w :=
  UAM_RegularLanguages.nerodeRel_refl L w

/-- **Композиция согласованности.** Если действие `σ` согласовано из `w`, а
    последующее действие `x` согласовано из `w ++ σ`, то составное действие
    `σ ++ x` согласовано из `w`.  Дискретный аналог «цепочки выровненных шагов».

    Замечание: без согласованности промежуточного шага (`h2`) простое
    «удлинение» `σ ↦ σ ++ x` в общем случае НЕ сохраняет согласованность —
    поэтому здесь требуется именно композиция. -/
theorem ActionAligned_trans (L : Set (UAM_Free.FreeMonoid α))
    (w σ x : UAM_Free.FreeMonoid α)
    (h1 : ActionAligned L w σ) (h2 : ActionAligned L (w ++ σ) x) :
    ActionAligned L w (σ ++ x) := by
  unfold ActionAligned at h1 h2 ⊢
  rw [← List.append_assoc]
  exact UAM_RegularLanguages.nerodeRel_trans L w (w ++ σ) ((w ++ σ) ++ x) h1 h2

end UAM_RSIA
