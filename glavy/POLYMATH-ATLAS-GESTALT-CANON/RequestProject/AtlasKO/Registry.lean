/-
# ATLAS Knowledge Objects — реестр первичных документов

Исходные документы Атласа (`docs/atlas/ATLAS-*.md`) — это семнадцать
объектов знания четырёх типов: STEP, CONCEPT, INVARIANT, MECHANISM.
Каждый документ несёт метаданные (`type`, `epistemic_status`,
`formalization_level`, `defined_in`, `used_in`, `related_*`).

Здесь эти метаданные превращены в машинно проверяемый реестр: доказаны
полнота реестра, целостность внутренних ссылок, тот факт, что поле
`defined_in` всегда указывает на STEP, ацикличность слоя зависимостей и —
честно — **неполнота исходного корпуса**: документы ссылаются на
`ATLAS-CONCEPT-004…009`, `ATLAS-STEP-002…004` и `ATLAS-MECHANISM-003`,
которых в корпусе нет.
-/
import Mathlib
import RequestProject.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8000

namespace Polymath.AtlasKO

open Polymath

/-! ## Идентификаторы документов -/

/-- Идентификатор объекта знания Атласа (по одному на документ корпуса). -/
inductive AtlasId where
  /-- STEP-001: системы растут. -/
  | STEP_001
  /-- STEP-005: информация уменьшает неопределённость. -/
  | STEP_005
  /-- STEP-006: редукция неопределённости порождает уровни сложности. -/
  | STEP_006
  /-- CONCEPT-001: система. -/
  | CONCEPT_001
  /-- CONCEPT-002: метрика. -/
  | CONCEPT_002
  /-- CONCEPT-003: ресурс. -/
  | CONCEPT_003
  /-- CONCEPT-010: неопределённость конфигурации. -/
  | CONCEPT_010
  /-- CONCEPT-011: релевантность данных. -/
  | CONCEPT_011
  /-- CONCEPT-012: уровень системной сложности. -/
  | CONCEPT_012
  /-- CONCEPT-013: высвобожденный ресурс. -/
  | CONCEPT_013
  /-- INVARIANT-001: инвариант роста. -/
  | INVARIANT_001
  /-- INVARIANT-005: информационное снижение неопределённости. -/
  | INVARIANT_005
  /-- INVARIANT-006: порождение сложности через редукцию неопределённости. -/
  | INVARIANT_006
  /-- MECHANISM-001: накопление. -/
  | MECHANISM_001
  /-- MECHANISM-002: воспроизводство и кооперация. -/
  | MECHANISM_002
  /-- MECHANISM-005: редукция неопределённости через информационные потоки. -/
  | MECHANISM_005
  /-- MECHANISM-006: формирование уровней сложности. -/
  | MECHANISM_006
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Эпистемический статус документа: определение или модель. -/
inductive EpistemicStatus where
  /-- `epistemic_status: definition` — вводит понятие. -/
  | definition
  /-- `epistemic_status: model` — содержательное утверждение о мире. -/
  | model
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Метаданные одного документа корпуса. -/
structure AtlasMeta where
  /-- Идентификатор документа. -/
  id : AtlasId
  /-- Тип объекта в терминах ядра (`ObjectKind`). -/
  kind : ObjectKind
  /-- Имя из поля `name`. -/
  name : String
  /-- Значение поля `epistemic_status`. -/
  epistemic : EpistemicStatus
  /-- Значение поля `formalization_level` (1…4). -/
  level : ℕ
  /-- Документ (STEP), в котором объект определён. -/
  definedIn : AtlasId
  /-- Шаги, в которых объект используется. -/
  usedIn : List AtlasId
  /-- Ссылки на документы, отсутствующие в корпусе (как строки). -/
  danglingRefs : List String
  deriving DecidableEq, Repr, Inhabited

/-- Реестр корпуса: семнадцать документов с их метаданными. -/
def registry : List AtlasMeta :=
  [ ⟨.STEP_001, .step, "Системы растут", .model, 2, .STEP_001,
      [.STEP_001], []⟩,
    ⟨.STEP_005, .step, "Информация уменьшает неопределённость", .model, 4, .STEP_005,
      [.STEP_005], ["ATLAS-CONCEPT-004", "ATLAS-CONCEPT-005", "ATLAS-CONCEPT-006",
        "ATLAS-CONCEPT-007", "ATLAS-CONCEPT-008", "ATLAS-CONCEPT-009",
        "ATLAS-STEP-002", "ATLAS-STEP-003", "ATLAS-STEP-004"]⟩,
    ⟨.STEP_006, .step, "Редукция неопределённости порождает уровни сложности", .model, 4,
      .STEP_006, [.STEP_006], []⟩,
    ⟨.CONCEPT_001, .concept, "System", .definition, 1, .STEP_001,
      [.STEP_001, .STEP_005], []⟩,
    ⟨.CONCEPT_002, .concept, "Metric", .definition, 2, .STEP_001,
      [.STEP_001, .STEP_005], []⟩,
    ⟨.CONCEPT_003, .concept, "Resource", .definition, 1, .STEP_001,
      [.STEP_001, .STEP_005], []⟩,
    ⟨.CONCEPT_010, .concept, "Неопределенность конфигурации", .definition, 4, .STEP_005,
      [.STEP_005], ["ATLAS-CONCEPT-007", "ATLAS-CONCEPT-008"]⟩,
    ⟨.CONCEPT_011, .concept, "Релевантность данных", .definition, 3, .STEP_005,
      [.STEP_005], ["ATLAS-CONCEPT-008", "ATLAS-CONCEPT-009"]⟩,
    ⟨.CONCEPT_012, .concept, "Уровень системной сложности", .definition, 4, .STEP_006,
      [.STEP_006], ["ATLAS-CONCEPT-007"]⟩,
    ⟨.CONCEPT_013, .concept, "Высвобожденный ресурс", .definition, 3, .STEP_006,
      [.STEP_006], ["ATLAS-CONCEPT-006", "ATLAS-CONCEPT-008"]⟩,
    ⟨.INVARIANT_001, .invariant, "Growth invariant", .model, 2, .STEP_001,
      [.STEP_001], []⟩,
    ⟨.INVARIANT_005, .invariant, "Инвариант информационного снижения неопределенности",
      .model, 4, .STEP_005, [.STEP_005], []⟩,
    ⟨.INVARIANT_006, .invariant,
      "Инвариант порождения сложности через редукцию неопределённости",
      .model, 4, .STEP_006, [.STEP_006], []⟩,
    ⟨.MECHANISM_001, .mechanism, "Accumulation (physical and biological)", .model, 2,
      .STEP_001, [.STEP_001], []⟩,
    ⟨.MECHANISM_002, .mechanism, "Reproduction and cooperation", .model, 1, .STEP_001,
      [.STEP_001], []⟩,
    ⟨.MECHANISM_005, .mechanism, "Редукция неопределенности через информационные потоки",
      .model, 4, .STEP_005, [.STEP_005], ["ATLAS-MECHANISM-003"]⟩,
    ⟨.MECHANISM_006, .mechanism,
      "Формирование уровней сложности после редукции неопределённости",
      .model, 4, .STEP_006, [.STEP_006], ["ATLAS-MECHANISM-003"]⟩ ]

/-! ## Целостность реестра -/

/-- В корпусе семнадцать документов. -/
theorem registry_card : registry.length = 17 := by decide

/-- Идентификаторы документов не повторяются. -/
theorem registry_nodup : (registry.map AtlasMeta.id).Nodup := by decide

/-- Реестр покрывает все идентификаторы. -/
theorem registry_total : ∀ a : AtlasId, ∃ m ∈ registry, m.id = a := by decide

/-- Метаданные по идентификатору (тотальная функция благодаря `registry_total`). -/
def docMeta (a : AtlasId) : AtlasMeta :=
  (registry.find? (fun m => m.id == a)).getD default

theorem docMeta_id : ∀ a : AtlasId, (docMeta a).id = a := by decide

/-- Уровень формализации каждого документа лежит в диапазоне 1…4. -/
theorem level_range : ∀ m ∈ registry, 1 ≤ m.level ∧ m.level ≤ 4 := by decide

/-- Поле `defined_in` всегда указывает на документ типа STEP. -/
theorem definedIn_is_step : ∀ m ∈ registry, (docMeta m.definedIn).kind = ObjectKind.step := by
  decide

/-- Шаг определён сам в себе. -/
theorem step_definedIn_self :
    ∀ m ∈ registry, m.kind = ObjectKind.step → m.definedIn = m.id := by decide

/-- Каждый документ используется хотя бы одним шагом, и все элементы `used_in`
действительно являются шагами. -/
theorem usedIn_are_steps :
    ∀ m ∈ registry, m.usedIn ≠ [] ∧ ∀ s ∈ m.usedIn, (docMeta s).kind = ObjectKind.step := by
  decide

/-- Документ определён в одном из шагов, которые его используют. -/
theorem definedIn_mem_usedIn : ∀ m ∈ registry, m.definedIn ∈ m.usedIn := by decide

/-- На четвёртом уровне формализации присутствуют и модели, и определения. -/
theorem level4_mixed_status :
    (∃ m ∈ registry, m.level = 4 ∧ m.epistemic = EpistemicStatus.model) ∧
    (∃ m ∈ registry, m.level = 4 ∧ m.epistemic = EpistemicStatus.definition) := by decide

/-! ## Распределение по типам -/

/-- Число документов каждого типа: 3 шага, 7 концептов, 3 инварианта, 4 механизма. -/
theorem kind_counts :
    (registry.filter (fun m => m.kind == ObjectKind.step)).length = 3 ∧
    (registry.filter (fun m => m.kind == ObjectKind.concept)).length = 7 ∧
    (registry.filter (fun m => m.kind == ObjectKind.invariant)).length = 3 ∧
    (registry.filter (fun m => m.kind == ObjectKind.mechanism)).length = 4 := by decide

/-- Каждый шаг снабжён хотя бы одним инвариантом и хотя бы одним механизмом:
структурное требование Атласа выполнено всеми тремя шагами. -/
theorem every_step_has_invariant_and_mechanism :
    ∀ m ∈ registry, m.kind = ObjectKind.step →
      (∃ i ∈ registry, i.kind = ObjectKind.invariant ∧ i.definedIn = m.id) ∧
      (∃ k ∈ registry, k.kind = ObjectKind.mechanism ∧ k.definedIn = m.id) := by decide

/-! ## Слой зависимостей и его ацикличность -/

/-- Ранг документа: номер шага в цепочке STEP-001 → STEP-005 → STEP-006,
удвоенный, плюс единица для несамостоятельных документов. -/
def rank : AtlasId → ℕ
  | .STEP_001 => 0
  | .CONCEPT_001 => 1
  | .CONCEPT_002 => 1
  | .CONCEPT_003 => 1
  | .INVARIANT_001 => 1
  | .MECHANISM_001 => 1
  | .MECHANISM_002 => 1
  | .STEP_005 => 2
  | .CONCEPT_010 => 3
  | .CONCEPT_011 => 3
  | .INVARIANT_005 => 3
  | .MECHANISM_005 => 3
  | .STEP_006 => 4
  | .CONCEPT_012 => 5
  | .CONCEPT_013 => 5
  | .INVARIANT_006 => 5
  | .MECHANISM_006 => 5

/-- Рёбра слоя зависимостей: «объект опирается на шаг, в котором определён»
и «шаг опирается на предыдущий шаг» (`builds_on`). -/
def dependsOn (a b : AtlasId) : Bool :=
  (a == AtlasId.STEP_005 && b == AtlasId.STEP_001) ||
  (a == AtlasId.STEP_006 && b == AtlasId.STEP_005) ||
  (!(a == b) && (docMeta a).definedIn == b)

/-- Ребро зависимости строго понижает ранг. -/
theorem dependsOn_decreases :
    ∀ a b : AtlasId, dependsOn a b = true → rank b < rank a := by decide

/-- Отношение зависимости иррефлексивно. -/
theorem dependsOn_irrefl : ∀ a : AtlasId, dependsOn a a = false := by decide

/-- **Ацикличность слоя зависимостей.** Никакая цепочка зависимостей не
возвращается в исходную точку. -/
theorem dependsOn_acyclic (a : AtlasId) :
    ¬ Relation.TransGen (fun x y => dependsOn x y = true) a a := by
  have key : ∀ x y : AtlasId, Relation.TransGen (fun x y => dependsOn x y = true) x y →
      rank y < rank x := by
    intro x y hxy
    induction hxy with
    | single h => exact dependsOn_decreases _ _ h
    | tail _ h ih => exact lt_trans (dependsOn_decreases _ _ h) ih
  intro h
  exact absurd (key a a h) (lt_irrefl _)

/-! ## Честный учёт: корпус не полон -/

/-- Все висячие ссылки корпуса. -/
def danglingAll : List String :=
  (registry.flatMap AtlasMeta.danglingRefs).eraseDups

/-- Недостающие документы перечислены явно. -/
theorem danglingAll_eq :
    danglingAll =
      ["ATLAS-CONCEPT-004", "ATLAS-CONCEPT-005", "ATLAS-CONCEPT-006", "ATLAS-CONCEPT-007",
       "ATLAS-CONCEPT-008", "ATLAS-CONCEPT-009", "ATLAS-STEP-002", "ATLAS-STEP-003",
       "ATLAS-STEP-004", "ATLAS-MECHANISM-003"] := by decide

/-- **Корпус ссылается на отсутствующие документы**: десять внешних ссылок не
разрешаются ни в один документ корпуса. -/
theorem corpus_incomplete : danglingAll.length = 10 ∧ "ATLAS-CONCEPT-004" ∈ danglingAll := by
  refine ⟨by decide, by decide⟩

/-- Внутренние ссылки (`used_in`, `defined_in`) при этом целостны: они
разрешаются в документы самого корпуса. -/
theorem internal_refs_resolve :
    ∀ m ∈ registry, (∃ d ∈ registry, d.id = m.definedIn) ∧
      ∀ s ∈ m.usedIn, ∃ d ∈ registry, d.id = s :=
  fun m _ => ⟨registry_total m.definedIn, fun s _ => registry_total s⟩

end Polymath.AtlasKO
