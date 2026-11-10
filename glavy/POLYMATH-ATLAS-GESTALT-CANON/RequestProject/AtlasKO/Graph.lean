/-
# Корпус Атласа как экземпляр графа знаний

Реестр документов (`Registry.lean`) здесь превращается в настоящий
`Polymath.KnowledgeGraph`: узлы — документы корпуса, рёбра — слой
зависимостей `defined_in` / `builds_on`.  Тем самым первичный материал
проекта становится экземпляром формализованного ядра модели знаний, а не
отдельной сущностью рядом с ним.

Доказаны: корректность всех узлов (`WellFormed`), нормализованность
(пара «тип + имя» определяет узел однозначно), разрешимость всех ссылок,
подсчёт узлов и рёбер и устойчивость свойств при удалении узла.
-/
import RequestProject.AtlasKO.Registry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Polymath.AtlasKO

open Polymath

/-! ## Нумерация документов -/

/-- Числовой идентификатор документа в графе знаний. -/
def oid : AtlasId → ℕ
  | .STEP_001 => 1
  | .STEP_005 => 5
  | .STEP_006 => 6
  | .CONCEPT_001 => 101
  | .CONCEPT_002 => 102
  | .CONCEPT_003 => 103
  | .CONCEPT_010 => 110
  | .CONCEPT_011 => 111
  | .CONCEPT_012 => 112
  | .CONCEPT_013 => 113
  | .INVARIANT_001 => 201
  | .INVARIANT_005 => 205
  | .INVARIANT_006 => 206
  | .MECHANISM_001 => 301
  | .MECHANISM_002 => 302
  | .MECHANISM_005 => 305
  | .MECHANISM_006 => 306

theorem oid_injective : Function.Injective oid := by decide

/-! ## Узлы -/

/-- Зрелость документа: все документы корпуса имеют `status: draft`,
что соответствует состоянию `prototype`. -/
def maturityOf (_ : AtlasMeta) : Maturity := Maturity.prototype

/-- Уверенность узла: доля достигнутого уровня формализации (`level / 4`). -/
def confidenceOf (m : AtlasMeta) : ℚ := (m.level : ℚ) / 4

/-- Документ как узел графа знаний. -/
def toObject (m : AtlasMeta) : KnowledgeObject :=
  ⟨oid m.id, m.kind, m.name, maturityOf m, confidenceOf m⟩

/-- Список узлов. -/
def objList : List KnowledgeObject := registry.map toObject

/-! ## Рёбра -/

/-- Все пары документов. -/
def allIds : List AtlasId :=
  [.STEP_001, .STEP_005, .STEP_006, .CONCEPT_001, .CONCEPT_002, .CONCEPT_003,
   .CONCEPT_010, .CONCEPT_011, .CONCEPT_012, .CONCEPT_013,
   .INVARIANT_001, .INVARIANT_005, .INVARIANT_006,
   .MECHANISM_001, .MECHANISM_002, .MECHANISM_005, .MECHANISM_006]

theorem allIds_complete : ∀ a : AtlasId, a ∈ allIds := by decide

/-- Тип связи: между шагами — `builds_on`, от документа к его шагу — `uses`. -/
def relKindOf (a b : AtlasId) : RelationKind :=
  if (docMeta a).kind = ObjectKind.step && (docMeta b).kind = ObjectKind.step then
    RelationKind.buildsOn
  else
    RelationKind.uses

/-- Список рёбер слоя зависимостей. -/
def relList : List KnowledgeRelation :=
  (allIds.flatMap fun a =>
    allIds.filterMap fun b =>
      if dependsOn a b then some (⟨oid a, oid b, relKindOf a b, 1⟩ : KnowledgeRelation)
      else none)

/-! ## Граф -/

/-- Разные документы дают разные узлы: `id` документа определяет его целиком. -/
theorem registry_id_inj :
    ∀ m ∈ registry, ∀ n ∈ registry, m.id = n.id → m = n := by decide

/-- Пара «тип + имя» также определяет документ однозначно. -/
theorem registry_name_inj :
    ∀ m ∈ registry, ∀ n ∈ registry, m.kind = n.kind → m.name = n.name → m = n := by decide

theorem mem_objList {o : KnowledgeObject} :
    o ∈ objList ↔ ∃ m ∈ registry, toObject m = o := by
  simp [objList]

/-- Корпус Атласа как граф знаний. -/
def graph : KnowledgeGraph where
  objects := objList.toFinset
  relations := relList.toFinset
  unique_id := by
    intro a ha b hb hab
    rw [List.mem_toFinset, mem_objList] at ha hb
    obtain ⟨m, hm, rfl⟩ := ha
    obtain ⟨n, hn, rfl⟩ := hb
    have : m = n := registry_id_inj m hm n hn (oid_injective hab)
    rw [this]
  src_closed := by decide
  tgt_closed := by decide

/-! ## Свойства -/

/-- Семнадцать узлов. -/
theorem graph_objects_card : graph.objects.card = 17 := by decide

/-- Шестнадцать рёбер: по одному от каждого из четырнадцати несамостоятельных
документов к своему шагу и два ребра `builds_on` между шагами. -/
theorem graph_relations_card : graph.relations.card = 16 := by decide

/-- Все узлы корректны: уверенность лежит в `[0,1]`, а зрелость `prototype`
не требует единичной уверенности. -/
theorem graph_objects_wellFormed : ∀ o ∈ graph.objects, o.WellFormed := by
  intro o ho
  rw [show graph.objects = objList.toFinset from rfl, List.mem_toFinset, mem_objList] at ho
  obtain ⟨m, hm, rfl⟩ := ho
  obtain ⟨h1, h4⟩ := level_range m hm
  have hle : ((m.level : ℚ)) ≤ 4 := by exact_mod_cast h4
  refine ⟨by simp only [toObject, confidenceOf]; positivity, ?_, ?_⟩
  · simpa [toObject, confidenceOf] using (div_le_one (by norm_num : (0:ℚ) < 4)).2 hle
  · intro h
    exact absurd h (by simp [toObject, maturityOf])

/-- Граф нормализован: пара «тип + имя» определяет узел однозначно. -/
theorem graph_normalized : graph.Normalized := by
  intro a ha b hb hk hl
  rw [show graph.objects = objList.toFinset from rfl, List.mem_toFinset, mem_objList] at ha hb
  obtain ⟨m, hm, rfl⟩ := ha
  obtain ⟨n, hn, rfl⟩ := hb
  have : m = n := registry_name_inj m hm n hn hk hl
  rw [this]

/-- Каждое ребро разрешается в существующие узлы (следствие ядра). -/
theorem graph_relations_resolve :
    ∀ r ∈ graph.relations, (∃ o ∈ graph.objects, o.id = r.source) ∧
      ∃ o ∈ graph.objects, o.id = r.target :=
  fun r hr => ⟨graph.src_closed r hr, graph.tgt_closed r hr⟩

/-- Структурный слой: все рёбра корпуса структурные, причинных рёбер нет. -/
theorem graph_all_structural :
    ∀ r ∈ graph.relations, r.kind.isStructural = true ∧ r.kind.isCausal = false := by decide

/-- В графе нет петель. -/
theorem graph_no_selfloops : ∀ r ∈ graph.relations, r.source ≠ r.target := by decide

/-- Удаление узла снова даёт корректный нормализованный граф — свойство ядра,
применённое к корпусу. -/
theorem graph_erase_normalized (o : KnowledgeObject) : (graph.eraseObj o).Normalized :=
  graph.eraseObj_normalized o graph_normalized

end Polymath.AtlasKO
