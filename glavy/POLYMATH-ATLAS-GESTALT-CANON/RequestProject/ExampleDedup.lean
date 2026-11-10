import RequestProject.Dedup
import RequestProject.Example

/-!
# Пример: устранение дублирования концепта

Демонстрация непустоты слоя `RequestProject.Dedup` на конкретных данных.

Берётся граф, в котором концепт «Information» заведён дважды — под
идентификаторами `1` и `5` (типичная находка аудита). Такой граф
**не нормализован**. После дедупликации с каноническим представителем `1`
граф становится нормализованным, число объектов уменьшается, а зависимость
`2 → 5` превращается в зависимость `2 → 1`: знание не теряется, теряется
только дубликат.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath
namespace Demo

/-- Дубликат концепта «информация» под другим идентификатором. -/
def cInfoDup : KnowledgeObject := ⟨5, ObjectKind.concept, "Information", Maturity.prototype, 1⟩

/-- Связь инварианта с оригинальным концептом. -/
def rIU1 : KnowledgeRelation := ⟨2, 1, RelationKind.uses, 1⟩

/-- Связь инварианта с дубликатом концепта. -/
def rIU5 : KnowledgeRelation := ⟨2, 5, RelationKind.uses, 1⟩

/-- Граф с дублирующимся концептом. -/
def atlasDup : KnowledgeGraph where
  objects := {cInfo, cInfoDup, iUnc}
  relations := {rIU1, rIU5}
  unique_id := by decide
  src_closed := by decide
  tgt_closed := by decide

/-- Дублирование действительно нарушает нормализованность. -/
theorem atlasDup_not_normalized : ¬ atlasDup.Normalized := by
  intro h
  have := h cInfo (by decide) cInfoDup (by decide) rfl rfl
  exact absurd this (by decide)

/-- Канонический представитель: дубликат `5` заменяется оригиналом `1`. -/
def canonInfo : KnowledgeGraph.CanonChoice atlasDup where
  f := fun o => if o.id = 5 then cInfo else o
  fid := fun i => if i = 5 then 1 else i
  mem := by decide
  id_eq := by decide
  kind_eq := by decide
  label_eq := by decide
  merge := by decide

/-- Дедуплицированный граф. -/
def atlasDedup : KnowledgeGraph := atlasDup.dedup canonInfo

/-- После дедупликации концепт существует ровно один раз. -/
theorem atlasDedup_normalized : atlasDedup.Normalized :=
  atlasDup.dedup_normalized canonInfo

/-- Дубликат исчез: в дедуплицированном графе остались оригинальный концепт
и инвариант. -/
theorem atlasDedup_objects : atlasDedup.objects = {cInfo, iUnc} := by decide

/-- Объём графа строго уменьшился. -/
theorem atlasDedup_card_lt : atlasDedup.objects.card < atlasDup.objects.card := by decide

/-- Знание не потеряно: зависимость от дубликата стала зависимостью
от канонического концепта. -/
theorem atlasDedup_dep : atlasDedup.Dep 2 1 := by
  have h : atlasDup.Dep 2 5 := ⟨rIU5, by decide, by decide, rfl, rfl⟩
  have := atlasDup.dedup_dep_of_dep canonInfo h
  simpa [canonInfo] using this

end Demo
end Polymath
