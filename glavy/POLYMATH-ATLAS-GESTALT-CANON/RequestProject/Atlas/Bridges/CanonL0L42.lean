import RequestProject.Atlas.Canon.Core
import RequestProject.Atlas.Canon.L0L42
import RequestProject.Atlas.Bridges.CanonUAM

/-!
# Шов: канон L0–L42 ↔ Канон Горизонтов

Шкала `L0–L42` и слои Канона Горизонтов записаны по-разному, но обе суть
упорядоченные семейства именованных позиций. Здесь шкала и её витки
представлены как слои `Layer`, после чего правило сдвига канона применимо
к ним, а «Закон выхода» («после L42 возможна новая шкала») получает точное
прочтение: новая шкала — это сдвиг, структурно тождественный прежней и
отличающийся только номером.

Формально доказано:

* `scaleLayer` — сорок три уровня как `Layer 43`, `arcLayer` — девять витков
  как `Layer 9`;
* `scaleLayer_strictlyOrdered`, `arcLayer_strictlyOrdered` — обе шкалы строго
  упорядочены;
* `scaleLayer_names_injective` — имена уровней различны (закон уникальности
  имени в форме слоя);
* `scaleLayer_lacks_canonical_arity`, `arcLayer_lacks_canonical_arity` — ни
  шкала, ни витки не имеют канонической арности пять;
* `exit_is_shift` — «новая шкала после L42» как сдвиг: имена сохраняются,
  номер растёт;
* `scale_shift_action` — сдвиг шкалы есть действие свободного моноида UAM.
-/

namespace Bridges.CanonL0L42

open Canon.L0L42

/-- Уровень с номером `i` шкалы `L0–L42`. -/
def levelAt (i : Fin 43) : Level :=
  levels[i.val]'(by rw [levels_length]; exact i.isLt)

/-- Виток с номером `i`. -/
def arcAt (i : Fin 9) : Arc :=
  arcs[i.val]'(by rw [arcs_length]; exact i.isLt)

/-- Шкала `L0–L42` как слой канона: имя позиции — имя уровня, уровень
самовмещения — его номер. -/
def scaleLayer : Layer 43 where
  idx := 0
  canons := fun i =>
    { name := (levelAt i).name
      layer := 0
      selfReferenceLevel := i.val }

/-- Девять витков как слой канона. -/
def arcLayer : Layer 9 where
  idx := 0
  canons := fun i =>
    { name := (arcAt i).title
      layer := 0
      selfReferenceLevel := i.val }

theorem scaleLayer_strictlyOrdered : scaleLayer.StrictlyOrdered := by
  intro i j hij
  exact hij

theorem arcLayer_strictlyOrdered : arcLayer.StrictlyOrdered := by
  intro i j hij
  exact hij

/-- Позиция слоя воспроизводит номер уровня канона. -/
theorem scaleLayer_selfReferenceLevel (i : Fin 43) :
    (scaleLayer.canons i).selfReferenceLevel = (levelAt i).idx := by
  fin_cases i <;> rfl

/-- Закон уникальности имени в форме слоя: разные позиции — разные имена. -/
theorem scaleLayer_names_injective :
    Function.Injective (fun i : Fin 43 => (scaleLayer.canons i).name) := by
  decide

/-- Витки тоже носят различные названия. -/
theorem arcLayer_names_injective :
    Function.Injective (fun i : Fin 9 => (arcLayer.canons i).name) := by
  decide

/-- Шкала из сорока трёх уровней не имеет канонической арности пять. -/
theorem scaleLayer_lacks_canonical_arity : ¬ scaleLayer.HasCanonicalArity :=
  nonfive_lacks_canonical_arity (by decide) scaleLayer

/-- Девять витков не образуют канонической пятёрки. -/
theorem arcLayer_lacks_canonical_arity : ¬ arcLayer.HasCanonicalArity :=
  nonfive_lacks_canonical_arity (by decide) arcLayer

/-- **Закон выхода как сдвиг.** «Новая шкала после L42» структурно тождественна
прежней и отличается только номером: имена уровней сохраняются, номер шкалы
и уровни самовмещения растут на единицу. -/
theorem exit_is_shift :
    shift scaleLayer ≈ scaleLayer ∧
    (shift scaleLayer).idx = scaleLayer.idx + 1 ∧
    ∀ i : Fin 43, ((shift scaleLayer).canons i).selfReferenceLevel =
      (scaleLayer.canons i).selfReferenceLevel + 1 :=
  ⟨shift_structurally_equivalent scaleLayer, rfl,
    shift_increases_selfReferenceLevel scaleLayer⟩

/-- Повторный выход: `k` новых шкал сохраняют имена и увеличивают номер на `k`. -/
theorem iterated_exit (k : Nat) :
    ((shift^[k]) scaleLayer).idx = k ∧ (shift^[k]) scaleLayer ≈ scaleLayer := by
  refine ⟨?_, shift_iterate_structurally_equivalent scaleLayer k⟩
  have h := (shift_iterate_fields scaleLayer k).1
  simpa [scaleLayer] using h

/-- Сдвиг шкалы `L0–L42` — частный случай действия свободного моноида UAM
на слоях канона. -/
theorem scale_shift_action (w : UAM_Free.FreeMonoid Unit) :
    (CanonUAM.shiftAction 43).act w scaleLayer = (shift^[w.length]) scaleLayer :=
  rfl

/-- Ни один выход не возвращает шкалу буквально: спираль шкал не замыкается. -/
theorem exit_never_returns (w : UAM_Free.FreeMonoid Unit) (hw : w ≠ []) :
    (CanonUAM.shiftAction 43).act w scaleLayer ≠ scaleLayer :=
  (CanonUAM.spiral_structural_not_literal scaleLayer).2 w hw

end Bridges.CanonL0L42
