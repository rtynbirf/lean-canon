import RequestProject.Curriculum
import RequestProject.ProofGraph
import RequestProject.Atlas.Canon.Core

/-!
# Мост: слои Канона как граф знаний

Модуль связывает ядро модели знаний (`Polymath`) с формализацией
«Канона Горизонтов» из архивного слоя (`RequestProject.Atlas.Canon.Core`).

Четыре канонических слоя `Layer1`–`Layer4` рассматриваются как Knowledge
Objects типа «механизм», а правило сдвига — как структурная связь
«следующий слой строится на предыдущем». Доказано, что получающийся граф
знаний:

* корректен по построению (ссылочная целостность) и нормализован —
  имена слоёв различны, поэтому каждый слой представлен ровно одним
  объектом;
* ациклический, причём ранг объекта совпадает с уровнем самовмещения
  канонов слоя (`canonicalLayer_selfReferenceLevel`), то есть спираль
  Канона не замыкается в цикл (ср. `spiral_not_cycle`);
* даёт явную траекторию изучения `[1, 2, 3, 4]`;
* полностью обоснован как граф доказательств, если первый слой принять
  за аксиоматическое основание.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath
namespace AtlasBridge

/-- Knowledge Object, соответствующий `N`-му каноническому слою.
Идентификатор — номер слоя, метка — имя первого канона слоя. -/
def canonObj (N : Fin 4) : KnowledgeObject :=
  { id := N.val + 1
    kind := ObjectKind.mechanism
    label := ((canonicalLayer N).canons 0).name
    maturity := Maturity.canonical
    confidence := 1 }

@[simp] theorem canonObj_id (N : Fin 4) : (canonObj N).id = N.val + 1 := rfl

/-- Уровень самовмещения слоя определяется идентификатором объекта. -/
theorem canonObj_selfReferenceLevel (N : Fin 4) (i : Fin 5) :
    ((canonicalLayer N).canons i).selfReferenceLevel + 1 = (canonObj N).id := by
  rw [canonicalLayer_selfReferenceLevel, canonObj_id]

/-- Связь «слой `k+2` строится на слое `k+1`». -/
def canonRel (k : Fin 3) : KnowledgeRelation :=
  { source := k.val + 2, target := k.val + 1, kind := RelationKind.buildsOn, confidence := 1 }

/-- Граф знаний четырёх канонических слоёв. -/
def canonGraph : KnowledgeGraph where
  objects := {canonObj 0, canonObj 1, canonObj 2, canonObj 3}
  relations := {canonRel 0, canonRel 1, canonRel 2}
  unique_id := by decide
  src_closed := by decide
  tgt_closed := by decide

theorem canonGraph_ids : canonGraph.ids = {1, 2, 3, 4} := by decide

/-- Все объекты графа корректны: уверенность в `[0,1]`. -/
theorem canonGraph_wellFormed : ∀ o ∈ canonGraph.objects, o.WellFormed := by
  intro o ho
  fin_cases ho <;>
    refine ⟨by norm_num [canonObj], by norm_num [canonObj], fun _ => by norm_num [canonObj]⟩

/-- Имена канонических слоёв различны, поэтому граф нормализован:
каждый слой существует ровно один раз. -/
theorem canonGraph_normalized : canonGraph.Normalized := by
  unfold KnowledgeGraph.Normalized
  decide

/-- Граф зависимостей слоёв ациклический: спираль Канона не замыкается. -/
theorem canonGraph_acyclic : canonGraph.Acyclic := by
  refine canonGraph.acyclic_of_rank id ?_
  rintro a b ⟨r, hr, -, rfl, rfl⟩
  fin_cases hr <;> decide

/-- Первый слой — фундамент: он ни на что не опирается. -/
theorem canonGraph_foundation : ∀ b, ¬ canonGraph.Dep (canonObj 0).id b := by
  rintro b ⟨r, hr, -, hs, -⟩
  fin_cases hr <;> simp_all [canonObj, canonRel]

/-- Явная траектория изучения Канона: слои изучаются по порядку. -/
theorem canonGraph_curriculum : canonGraph.Curriculum [1, 2, 3, 4] := by
  refine ⟨?_, by decide, ?_⟩
  · intro i
    rw [canonGraph_ids]
    simp
  · rintro a b ⟨r, hr, -, rfl, rfl⟩
    fin_cases hr <;> decide

/-- Общая теорема о существовании траектории применима к графу Канона. -/
theorem canonGraph_exists_curriculum : ∃ l, canonGraph.Curriculum l :=
  canonGraph.exists_curriculum canonGraph_acyclic

/-! ## Канон как граф доказательств -/

/-- Аксиоматическое основание: первый слой. -/
def canonAx : Finset ℕ := {1}

/-- Выводимые слои: второй, третий и четвёртый. -/
def canonPr : Finset ℕ := {2, 3, 4}

theorem canonAx_sub : canonAx ⊆ canonGraph.ids := by decide

theorem canonPr_sub : canonPr ⊆ canonGraph.ids := by decide

theorem canonAx_leaf : ∀ c ∈ canonAx, canonGraph.premises c = ∅ := by decide

/-- Все слои Канона обоснованы: каждый следующий слой трассируется
к первому слою как к основанию. -/
theorem canonGraph_all_grounded :
    ∀ o ∈ canonGraph.objects,
      (canonGraph.toProofGraph canonAx canonPr canonAx_sub canonPr_sub
        canonAx_leaf).Grounded o.id :=
  canonGraph.all_grounded canonAx canonPr canonAx_sub canonPr_sub canonAx_leaf
    canonGraph_acyclic (by decide)

end AtlasBridge
end Polymath
