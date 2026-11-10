import RequestProject.Atlas.Canon.Core
import RequestProject.Atlas.ApostlePipeline

/-!
# Шов: Канон Горизонтов ↔ ApostlePipeline

Оба проекта описывают упорядоченную последовательность именованных позиций.
Канон — слой из пяти канонов с уровнем самовмещения; конвейер — тринадцать фаз
с линейным порядком. Здесь конвейер представлен как слой канона `Layer 13`,
после чего разница между проектами становится доказанным утверждением, а не
комментарием: конвейер строго упорядочен и допускает сдвиг, но не имеет
канонической арности, то есть не является слоем канонического текста.

Формально доказано:

* `apostleLayer` — тринадцать фаз как слой `Layer 13` с уровнями `0…12`;
* `apostleLayer_selfReferenceLevel` — уровень позиции равен номеру фазы минус один;
* `apostleLayer_strictlyOrdered` — строгий порядок уровней;
* `apostleLayer_not_uniform` — слой не равномерен (в отличие от `Layer1` канона);
* `apostleLayer_lacks_canonical_arity` — арность 13 ≠ 5: шов между проектами;
* `apostleLayer_shift_ordered`, `apostleLayer_shift_structurallyEquivalent` —
  сдвиг применим и к конвейеру: имена сохраняются, уровни растут;
* `canon_arity_ne_pipeline_length` — числовой источник шва.
-/

namespace Bridges.CanonApostle

open ApostlePipeline

/-- Русские имена тринадцати фаз конвейера. -/
def Phase.title : Phase → String
  | .peter => "Пётр"
  | .andrew => "Андрей"
  | .jamesZebedee => "Иаков Зеведеев"
  | .john => "Иоанн"
  | .philip => "Филипп"
  | .bartholomew => "Варфоломей"
  | .thomas => "Фома"
  | .matthew => "Матфей"
  | .jamesAlphaeus => "Иаков Алфеев"
  | .thaddaeus => "Фаддей"
  | .simonZelotes => "Симон Зилот"
  | .judas => "Иуда"
  | .paul => "Павел"

/-- Разные фазы носят разные имена. -/
theorem Phase.title_injective : Function.Injective Phase.title := by
  intro a b h
  cases a <;> cases b <;> simp_all [Phase.title]

/-- Фаза, стоящая на позиции `i` полного прогона. -/
def phaseAt (i : Fin 13) : Phase :=
  flow.get ⟨i.val, by rw [flow_length]; exact i.isLt⟩

@[simp] theorem phaseAt_index (i : Fin 13) : (phaseAt i).index = i.val + 1 := by
  fin_cases i <;> rfl

/-- Разные позиции заняты разными фазами. -/
theorem phaseAt_injective : Function.Injective phaseAt := by
  intro i j h
  have hi : (phaseAt i).index = (phaseAt j).index := by rw [h]
  rw [phaseAt_index, phaseAt_index] at hi
  exact Fin.ext (by omega)

/-- Конвейер апостолов как слой канона: тринадцать именованных позиций,
уровень самовмещения равен номеру позиции. -/
def apostleLayer : Layer 13 where
  idx := 1
  canons := fun i =>
    { name := Phase.title (phaseAt i)
      layer := 1
      selfReferenceLevel := i.val }

@[simp] theorem apostleLayer_selfReferenceLevel (i : Fin 13) :
    (apostleLayer.canons i).selfReferenceLevel + 1 = (phaseAt i).index := by
  rw [phaseAt_index]
  rfl

/-- Уровни самовмещения строго возрастают: конвейер линейно упорядочен. -/
theorem apostleLayer_strictlyOrdered : apostleLayer.StrictlyOrdered := by
  intro i j hij
  exact hij

/-- В отличие от слоёв канона, слой конвейера не равномерен. -/
theorem apostleLayer_not_uniform : ¬ apostleLayer.uniform := by
  intro h
  have h01 := h ⟨0, by omega⟩ ⟨1, by omega⟩
  simp [apostleLayer] at h01

/-- Имена позиций конвейера попарно различны. -/
theorem apostleLayer_names_injective :
    Function.Injective (fun i : Fin 13 => (apostleLayer.canons i).name) := by
  intro i j h
  exact phaseAt_injective (Phase.title_injective h)

/-- Числовой источник шва: канонических позиций пять, фаз конвейера тринадцать. -/
theorem canon_arity_ne_pipeline_length : canonicalArity ≠ flow.length := by
  rw [flow_length]
  decide

/-- **Шов.** Слой конвейера не имеет канонической арности: конвейер не является
слоем канонического текста, хотя и является слоем в смысле `Layer`. -/
theorem apostleLayer_lacks_canonical_arity : ¬ apostleLayer.HasCanonicalArity :=
  nonfive_lacks_canonical_arity (by decide) apostleLayer

/-- Сдвиг применим и к конвейеру: строгий порядок фаз сохраняется. -/
theorem apostleLayer_shift_ordered : (shift apostleLayer).StrictlyOrdered :=
  shift_preserves_order apostleLayer apostleLayer_strictlyOrdered

/-- Сдвинутый конвейер структурно тот же: имена фаз не меняются, меняется
только номер витка. Это в точности «спираль» канона, применённая к конвейеру. -/
theorem apostleLayer_shift_structurallyEquivalent :
    shift apostleLayer ≈ apostleLayer :=
  shift_structurally_equivalent apostleLayer

/-- Новый виток конвейера отличается от предыдущего номером слоя. -/
theorem apostleLayer_shift_idx (k : Nat) :
    ((shift^[k]) apostleLayer).idx = 1 + k :=
  (shift_iterate_fields apostleLayer k).1

end Bridges.CanonApostle
