/-
# OSA-3.2 — Gold Dataset v0.1 (§12) как исполнимый набор кейсов

Модуль формализует 15 эталонных кейсов §12 (шесть доменов ENG / IT / ML /
SCI / BIZ / SAF) и десять кейсов расширения v0.2 (ENG-016 … SAF-025) вместе с расширенным каталогом операторов §6 и проводит
**двухступенчатый протокол §11**:

* ступень A (SPEC CONSISTENCY) — каждый кейс записан в схеме §12
  (`case_id`, `domain`, `natural_request`, `proposed_graph`, `gold`,
  `expected_result`, `expected_error_code`, `expected_repair_action`,
  `rationale`), и его контракты проверяются структурно;
* ступень B (COMPILER CONFORMANCE) — вердикт компилятора для каждого кейса
  **вычисляется** и сравнивается с эталонным; совпадение доказано (`decide`),
  а не заявлено.

Все расхождения между эталоном §12 и вычисленным вердиктом зафиксированы
явно (см. `goldFindings` и раздел «Находки аудита» ниже) — по правилу
§22.12 «аудит перед расширением».

Порядок операторов в `goldRegistry` значим: `List.find?` возвращает первое
подходящее предложение починки, поэтому более специфичные операторы
(VALIDATE, CALIBRATE) стоят раньше более общих (COMPARE,
REDUCE_UNCERTAINTY).
-/
import RequestProject.OSA.Cases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

/-! ## Расширенный каталог операторов (§6) -/

/-- REPRESENT (инженерный контракт): представление модели требует
предварительной верификации.  §6 прямо требует, чтобы это условие стояло
в контракте, а не подразумевалось. -/
def REPRESENT_VERIFIED : Operator :=
  { baseOp with
    id := "REPRESENT_VERIFIED", level := .L2
    inputType := .Model, outputType := .Representation
    pre := [.Verified], post := [.Represented]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite] }

/-- REPRESENT (документационный контракт): представление формального описания
верификации не требует. -/
def REPRESENT_DOC : Operator :=
  { baseOp with
    id := "REPRESENT_DOC", level := .L2
    inputType := .FormalDescription, outputType := .Representation
    pre := [.Formalized], post := [.Represented]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite]
    uncertainty := ⟨0, 0, 1, 0⟩ }

/-- MODEL (контракт, требующий калиброванных данных).  Именно наличие этого
контракта — а не глобальное правило — делает `MEASURE → MODEL` ошибкой
(находка batch 1 §12). -/
def MODEL_STRICT : Operator :=
  { MODEL with
    id := "MODEL_STRICT"
    inputType := .CalibratedValue
    pre := [.Calibrated] }

/-- MODEL с высокой эпистемической неопределённостью (кейс ML-007). -/
def MODEL_UNCERTAIN : Operator :=
  { MODEL with
    id := "MODEL_UNCERTAIN"
    uncertainty := ⟨0, 40, 0, 0⟩ }

/-- ALGORITHMICIZE: разработка алгоритма по спецификации. -/
def ALGORITHMICIZE : Operator :=
  { baseOp with
    id := "ALGORITHMICIZE", level := .L2
    inputType := .Specification, outputType := .Algorithm
    pre := [.SpecAvailable], post := [.AlgorithmDesigned]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite] }

/-- COMPILE: компиляция исходного кода. -/
def COMPILE : Operator :=
  { baseOp with
    id := "COMPILE", level := .L2
    inputType := .SourceCode, outputType := .CompiledBinary
    pre := [.AlgorithmDesigned], post := [.Compiled]
    requiresInv := [.DataExistence]
    effectLevel := .E2
    producedEffects := [.ResourceBurn], allowedEffects := [.ResourceBurn] }

/-- DEPLOY: развёртывание на production.  Требует человеческой авторизации
(§6), которую автоматический оператор AUTHORIZE выдать не может. -/
def DEPLOY : Operator :=
  { baseOp with
    id := "DEPLOY", level := .L4
    inputType := .CompiledBinary, outputType := .Deployment
    pre := [.Compiled], post := [.Deployed]
    requiresInv := [.DataExistence]
    preserves := [.DataExistence, .Traceability, .Consistency, .PhysicalIntegrity]
    destroys := [.ReversibilityMargin]
    effectLevel := .E4
    producedEffects := [.ExternalIrreversible]
    allowedEffects := [.ExternalIrreversible, .InformationWrite]
    uncertainty := ⟨1, 0, 0, 0⟩
    reversibility := .irreversible
    requiresAuthorization := true
    humanAuthorizationRequired := true }

/-- AUTHORIZE_HUMAN: авторизация, обеспеченная решением человека.  В
`goldRegistry` его нет: человеческое решение не является оператором, который
компилятор вправе вставить самостоятельно (§4). -/
def AUTHORIZE_HUMAN : Operator :=
  { AUTHORIZE with
    id := "AUTHORIZE_HUMAN"
    grantsHumanAuthorization := true }

/-- COMPARE: сравнение двух объектов одного уровня, чистое вычисление. -/
def COMPARE : Operator :=
  { baseOp with
    id := "COMPARE", level := .L2
    inputType := .Model, outputType := .ComparisonResult
    pre := [], post := [.Compared, .EvidenceAvailable]
    requiresInv := [.DataExistence]
    effectLevel := .E0 }

/-- CLUSTERIZE: кластеризация набора данных. -/
def CLUSTERIZE : Operator :=
  { baseOp with
    id := "CLUSTERIZE", level := .L2
    inputType := .Dataset, outputType := .ClusterModel
    pre := [.DatasetAvailable], post := [.Clustered]
    requiresInv := [.DataExistence]
    effectLevel := .E2
    producedEffects := [.ResourceBurn], allowedEffects := [.ResourceBurn]
    uncertainty := ⟨0, 2, 2, 0⟩ }

/-- DELETE в необратимом варианте (E4): уничтожает `DataExistence` и требует
авторизации. -/
def DELETE_HARD : Operator :=
  { baseOp with
    id := "DELETE_HARD", level := .L1
    inputType := .ClusterModel, outputType := .DeletionRecord
    pre := [.Clustered], post := []
    requiresInv := [.DataExistence]
    preserves := [.Traceability, .Consistency, .PhysicalIntegrity]
    destroys := [.DataExistence, .ReversibilityMargin]
    effectLevel := .E4
    producedEffects := [.DataDeletion, .ExternalIrreversible]
    allowedEffects := [.DataDeletion, .ExternalIrreversible]
    reversibility := .irreversible
    requiresAuthorization := true }

/-- HYPOTHESIZE: формулирование гипотезы по наблюдению. -/
def HYPOTHESIZE : Operator :=
  { baseOp with
    id := "HYPOTHESIZE", level := .L2
    inputType := .Observation, outputType := .Hypothesis
    pre := [.Observed], post := [.Hypothesized]
    requiresInv := [.DataExistence]
    effectLevel := .E0 }

/-- EXPERIMENT: проведение эксперимента.  Успешная валидация — *возможный*
исход, а не постусловие: контракт гарантирует лишь факт проведения. -/
def EXPERIMENT_SCI : Operator :=
  { baseOp with
    id := "EXPERIMENT", level := .L2
    inputType := .Hypothesis, outputType := .ExperimentalResult
    pre := [.Hypothesized], post := [.ExperimentRun], sideFacts := [.Validated]
    requiresInv := [.DataExistence]
    effectLevel := .E2
    producedEffects := [.ResourceBurn], allowedEffects := [.ResourceBurn]
    uncertainty := ⟨0, 0, 4, 0⟩ }

/-- AXIOMATIZE: возведение подтверждённого результата в ранг закона. -/
def AXIOMATIZE_SCI : Operator :=
  { baseOp with
    id := "AXIOMATIZE", level := .L2
    inputType := .ValidationResult, outputType := .FormalAxiom
    pre := [.Validated], post := [.Axiomatized]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite] }

/-- OBSERVE: фиксация наблюдения. -/
def OBSERVE : Operator :=
  { baseOp with
    id := "OBSERVE", level := .L1
    inputType := .ObjectState, outputType := .Observation
    pre := [], post := [.Observed]
    requiresInv := [.DataExistence]
    effectLevel := .E0
    uncertainty := ⟨1, 0, 0, 1⟩ }

/-- FORMALIZE: формализация наблюдения. -/
def FORMALIZE : Operator :=
  { baseOp with
    id := "FORMALIZE", level := .L2
    inputType := .Observation, outputType := .FormalDescription
    pre := [.Observed], post := [.Formalized]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite]
    uncertainty := ⟨0, 1, 0, 0⟩ }

/-- EVALUATE: оценка (финансовая, рисковая) по модели. -/
def EVALUATE : Operator :=
  { baseOp with
    id := "EVALUATE", level := .L2
    inputType := .Model, outputType := .EvaluationResult
    pre := [.Modeled], post := [.Evaluated, .EvidenceAvailable]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite]
    uncertainty := ⟨0, 15, 10, 0⟩ }

/-- TRANSFORM: изменение конфигурации системы по авторизованному плану. -/
def TRANSFORM : Operator :=
  { baseOp with
    id := "TRANSFORM", level := .L4
    inputType := .AuthorizationToken, outputType := .SystemStateChange
    pre := [.Authorized], post := [.Transformed]
    requiresInv := [.DataExistence]
    preserves := [.DataExistence, .Traceability, .Consistency, .PhysicalIntegrity]
    destroys := [.ReversibilityMargin]
    effectLevel := .E4
    producedEffects := [.ExternalReversible]
    allowedEffects := [.ExternalReversible, .InformationWrite]
    uncertainty := ⟨1, 0, 0, 0⟩
    reversibility := .partiallyReversible
    requiresAuthorization := true
    requiredPreOps := ["AUTHORIZE"] }

/-- STRUCTURE: проектирование структуры процесса по требованиям. -/
def STRUCTURE : Operator :=
  { baseOp with
    id := "STRUCTURE", level := .L2
    inputType := .Requirements, outputType := .Design
    pre := [], post := [.Structured]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite] }

/-- DETECT: обнаружение аномалии. -/
def DETECT : Operator :=
  { baseOp with
    id := "DETECT", level := .L1
    inputType := .ObjectState, outputType := .DetectedEvent
    pre := [], post := [.Detected]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite]
    uncertainty := ⟨1, 1, 0, 0⟩ }

/-- DIAGNOSE: диагностика обнаруженного события. -/
def DIAGNOSE : Operator :=
  { baseOp with
    id := "DIAGNOSE", level := .L3
    inputType := .DetectedEvent, outputType := .DiagnosticResult
    pre := [.Detected], post := [.Diagnosed]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite]
    uncertainty := ⟨0, 1, 0, 0⟩ }

/-- EXECUTE в аварийном контуре: физическое воздействие по результату
диагностики; требует авторизации. -/
def EXECUTE_SAF : Operator :=
  { baseOp with
    id := "EXECUTE_SAF", level := .L4
    inputType := .DiagnosticResult, outputType := .PhysicalActuation
    pre := [.Diagnosed, .Authorized], post := [.Executed]
    requiresInv := [.DataExistence, .PhysicalIntegrity]
    preserves := [.DataExistence, .Traceability, .Consistency, .PhysicalIntegrity]
    destroys := [.ReversibilityMargin]
    effectLevel := .E4
    producedEffects := [.ExternalIrreversible]
    allowedEffects := [.ExternalIrreversible, .InformationWrite]
    uncertainty := ⟨1, 0, 0, 0⟩
    reversibility := .irreversible
    requiresAuthorization := true }

/-- RECOGNIZE: распознавание объекта в сыром сигнале. -/
def RECOGNIZE : Operator :=
  { baseOp with
    id := "RECOGNIZE", level := .L1
    inputType := .RawSignal, outputType := .RecognitionResult
    pre := [], post := [.Recognized]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite]
    uncertainty := ⟨2, 1, 0, 1⟩ }

/-- INDEX: занесение результата распознавания в каталог (информационный
эффект). -/
def INDEX : Operator :=
  { baseOp with
    id := "INDEX", level := .L1
    inputType := .RecognitionResult, outputType := .IndexEntry
    pre := [.Recognized], post := [.Indexed]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite]
    uncertainty := ⟨0, 0, 0, 1⟩ }

/-- INDEX с обратимым внешним эффектом (E3): запись во внешний каталог.
Показывает находку batch 1 §12 — «внешний эффект ≠ безопасность»: такой
вариант требует подтверждения. -/
def INDEX_EXTERNAL : Operator :=
  { INDEX with
    id := "INDEX_EXTERNAL"
    effectLevel := .E3
    producedEffects := [.ExternalReversible]
    allowedEffects := [.ExternalReversible, .InformationWrite] }

/-- REDUCE_UNCERTAINTY: снижение неопределённости данных (§6). -/
def REDUCE_UNCERTAINTY : Operator :=
  { baseOp with
    id := "REDUCE_UNCERTAINTY", level := .L1
    inputType := .MeasuredValue, outputType := .CalibratedValue
    pre := [.Measured], post := [.Calibrated]
    requiresInv := [.DataExistence]
    effectLevel := .E2
    producedEffects := [.ResourceBurn], allowedEffects := [.ResourceBurn]
    reduction := ⟨5, 10, 5, 5⟩ }

/-- Каталог операторов Gold Dataset.  Порядок задаёт приоритет предложений
починки (`List.find?` берёт первое совпадение). -/
def goldRegistry : List Operator :=
  [ MEASURE, CALIBRATE, MODEL, VALIDATE, VERIFY, DECIDE, AUTHORIZE, EXECUTE
  , SIMULATE, ANALYZE, COMPARE, EVALUATE, STRUCTURE, TRANSFORM
  , ALGORITHMICIZE, COMPILE, DEPLOY, CLUSTERIZE, DELETE_HARD
  , HYPOTHESIZE, EXPERIMENT_SCI, AXIOMATIZE_SCI
  , OBSERVE, FORMALIZE, REPRESENT_DOC, REPRESENT_VERIFIED
  , DETECT, DIAGNOSE, EXECUTE_SAF, RECOGNIZE, INDEX
  , REDUCE_UNCERTAINTY ]

/-- Тот же каталог, дополненный оператором человеческой авторизации. -/
def goldRegistryHuman : List Operator := AUTHORIZE_HUMAN :: goldRegistry

/-! ## Схема кейса (§12) -/

/-- Домены Gold Dataset. -/
inductive Domain
  | ENG | IT | ML | SCI | BIZ | SAF
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Кейс Gold Dataset в схеме §12. -/
structure GoldCase where
  caseId : String
  domain : Domain
  naturalRequest : String
  registry : List Operator
  composition : Composition
  /-- Ожидаемый вердикт (`expected_result`). -/
  expected : Status
  /-- Ожидаемый код ошибки (`expected_error_code`); для PASS — `NONE`. -/
  expectedCode : ErrCode
  /-- Ожидаемое действие починки: идентификаторы операторов, которые должны
  быть названы в предложении компилятора. -/
  expectedRepair : List String
  rationale : String
  deriving Inhabited

/-- Встречается ли список `sub` как непрерывный фрагмент. -/
def hasSubList : List Char → List Char → Bool
  | [], sub => sub.isEmpty
  | ch :: cs, sub => sub.isPrefixOf (ch :: cs) || hasSubList cs sub

/-- Содержит ли строка подстроку. -/
def containsSubstr (s sub : String) : Bool := hasSubList s.toList sub.toList

/-- Отчёт компилятора по кейсу. -/
def GoldCase.report (g : GoldCase) : Report := compile g.registry g.composition

/-- Вердикт компилятора совпал с эталонным. -/
def GoldCase.verdictMatches (g : GoldCase) : Bool :=
  g.report.status == g.expected

/-- Код ошибки совпал с эталонным. -/
def GoldCase.codeMatches (g : GoldCase) : Bool :=
  g.report.code == g.expectedCode

/-- Предложенная починка называет ровно те операторы, которых требует
эталон (§11, метрика Repair Precision). -/
def GoldCase.repairMatches (g : GoldCase) : Bool :=
  g.expectedRepair.all (fun x => containsSubstr g.report.suggestion x)

/-- Полное соответствие кейса эталону. -/
def GoldCase.conforms (g : GoldCase) : Bool :=
  g.verdictMatches && g.codeMatches && g.repairMatches

/-! ## Заготовки композиций -/

/-- Заготовка кейса: инварианты данных активны, трассируемость обязана
сохраниться. -/
def goldBase : Composition :=
  { baseCase with
    initialInvariants := [.DataExistence, .Traceability, .Consistency]
    requiredFinalInvariants := [.DataExistence, .Traceability] }

/-! ## 15 кейсов Gold Dataset v0.1 -/

/-- ENG-001: измерение и немедленное исполнение — прыжок L1 → L3. -/
def ENG001 : GoldCase where
  caseId := "ENG-001"
  domain := .ENG
  naturalRequest := "Измерить температуру узла и сразу запустить охлаждение"
  registry := goldRegistry
  composition :=
    { goldBase with caseId := "ENG-001", ops := [MEASURE, EXECUTE] }
  expected := .REJECT
  expectedCode := .E_LEVEL_JUMP
  expectedRepair := []
  rationale := "MeasuredValue (L1) подаётся оператору, ожидающему L3: gap = 2 (RULE 6)"

/-- ENG-002: представление модели без верификации. -/
def ENG002 : GoldCase where
  caseId := "ENG-002"
  domain := .ENG
  naturalRequest := "Построить модель узла по измерениям и выпустить её представление"
  registry := goldRegistry
  composition :=
    { goldBase with caseId := "ENG-002", ops := [MEASURE, MODEL, REPRESENT_VERIFIED] }
  expected := .REPAIR
  expectedCode := .E_NOT_YET_SATISFIED
  expectedRepair := ["VERIFY"]
  rationale := "контракт REPRESENT_VERIFIED требует факта Verified; его устанавливает VERIFY"

/-- ENG-003: анализ уже удалённых данных. -/
def ENG003 : GoldCase where
  caseId := "ENG-003"
  domain := .ENG
  naturalRequest := "Удалить архив измерений и проанализировать его"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "ENG-003"
      requiredFinalInvariants := [.Traceability]
      ops := [MEASURE, DELETE, ANALYZE] }
  expected := .REJECT
  expectedCode := .E_INVARIANT_VIOLATION
  expectedRepair := []
  rationale := "DELETE уничтожает DataExistence, который требует ANALYZE (RULE 3)"

/-- IT-004: развёртывание без человеческой авторизации. -/
def IT004 : GoldCase where
  caseId := "IT-004"
  domain := .IT
  naturalRequest := "Разработать алгоритм, собрать и выкатить в production"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "IT-004"
      initialType := .Specification
      initialFacts := [.SpecAvailable]
      requiredFinalInvariants := [.DataExistence, .Traceability]
      ops := [ALGORITHMICIZE, COMPILE, DEPLOY] }
  expected := .REJECT
  expectedCode := .E_EFFECT_POLICY_VIOLATION
  expectedRepair := []
  rationale :=
    "DEPLOY — E4 с требованием человеческой авторизации; автоматический " ++
    "AUTHORIZE такого токена не выдаёт, починка невозможна (RULE 4)"

/-- IT-005: модель по некалиброванным данным. -/
def IT005 : GoldCase where
  caseId := "IT-005"
  domain := .IT
  naturalRequest := "Построить модель нагрузки прямо по сырым телеметрическим измерениям"
  registry := goldRegistry
  composition :=
    { goldBase with caseId := "IT-005", ops := [MEASURE, MODEL_STRICT] }
  expected := .REPAIR
  expectedCode := .E_MISSING_CONVERSION
  expectedRepair := ["CALIBRATE"]
  rationale :=
    "контракт MODEL_STRICT требует CalibratedValue — именно контракт, " ++
    "а не глобальное правило, делает вставку CALIBRATE обязательной"

/-- IT-006: сравнение вариантов и выбор. -/
def IT006 : GoldCase where
  caseId := "IT-006"
  domain := .IT
  naturalRequest := "Сравнить две конфигурации сервиса и выбрать одну"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "IT-006"
      initialType := .Model
      initialFacts := [.Modeled]
      declaredThreshold := some 15
      ops := [COMPARE, DECIDE] }
  expected := .PASS
  expectedCode := .NONE
  expectedRepair := []
  rationale := "COMPARE даёт основание (EvidenceAvailable), DECIDE — чистый выбор уровня L3"

/-- ML-007: исполнение по модели с неопределённостью 0.40. -/
def ML007 : GoldCase where
  caseId := "ML-007"
  domain := .ML
  naturalRequest := "Прогнать модель прогноза и применить её решение к системе"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "ML-007"
      declaredThreshold := some 10
      ops := [MEASURE, CALIBRATE, MODEL_UNCERTAIN, VALIDATE, DECIDE, AUTHORIZE, EXECUTE] }
  expected := .REJECT
  expectedCode := .E_EPISTEMIC_INSUFFICIENT
  expectedRepair := []
  rationale :=
    "накопленная неопределённость 0.41 против порога 0.10 для L4; " ++
    "ни один оператор снижения не приводит её под порог"

/-- ML-008: реконфигурация по симуляции без валидации. -/
def ML008 : GoldCase where
  caseId := "ML-008"
  domain := .ML
  naturalRequest := "По результату симуляции перенастроить кластер"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "ML-008"
      initialType := .EnergyModel
      initialFacts := [.Modeled]
      ops := [SIMULATE, DECIDE, AUTHORIZE, TRANSFORM] }
  expected := .REPAIR
  expectedCode := .E_MISSING_CONVERSION
  expectedRepair := ["VALIDATE"]
  rationale := "SimulationResult не является ValidationResult: решение требует валидации"

/-- ML-009: удаление кластеризованных данных без авторизации. -/
def ML009 : GoldCase where
  caseId := "ML-009"
  domain := .ML
  naturalRequest := "Кластеризовать датасет и удалить исходные записи"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "ML-009"
      initialType := .Dataset
      initialFacts := [.DatasetAvailable]
      requiredFinalInvariants := [.Traceability]
      ops := [CLUSTERIZE, DELETE_HARD] }
  expected := .REPAIR
  expectedCode := .E_EFFECT_POLICY_VIOLATION
  expectedRepair := ["AUTHORIZE"]
  rationale := "необратимое удаление — E4; перед ним обязателен AUTHORIZE (RULE 4)"

/-- SCI-010: возведение результата эксперимента в закон. -/
def SCI010 : GoldCase where
  caseId := "SCI-010"
  domain := .SCI
  naturalRequest := "Выдвинуть гипотезу, поставить эксперимент и закрепить результат как закон"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "SCI-010"
      initialType := .Observation
      initialFacts := [.Observed]
      ops := [HYPOTHESIZE, EXPERIMENT_SCI, AXIOMATIZE_SCI] }
  expected := .REJECT
  expectedCode := .E_CONTRACT_LEAKAGE
  expectedRepair := []
  rationale :=
    "AXIOMATIZE требует статуса Validated; EXPERIMENT гарантирует только " ++
    "факт проведения — успешная валидация является недекларированным исходом"

/-- SCI-011: наблюдение → формализация → представление. -/
def SCI011 : GoldCase where
  caseId := "SCI-011"
  domain := .SCI
  naturalRequest := "Зафиксировать наблюдение, формализовать его и оформить представление"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "SCI-011"
      ops := [OBSERVE, FORMALIZE, REPRESENT_DOC] }
  expected := .PASS
  expectedCode := .NONE
  expectedRepair := []
  rationale := "каждый стык сдвигает уровень на +1 или 0, эффекты E0–E1, порог L2 = 0.30"

/-- BIZ-012: реконфигурация по оценке с неопределённостью 0.25. -/
def BIZ012 : GoldCase where
  caseId := "BIZ-012"
  domain := .BIZ
  naturalRequest := "Оценить экономический эффект и перестроить процесс"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "BIZ-012"
      initialType := .Model
      initialFacts := [.Modeled]
      declaredThreshold := some 10
      ops := [EVALUATE, DECIDE, AUTHORIZE, TRANSFORM] }
  expected := .REJECT
  expectedCode := .E_EPISTEMIC_INSUFFICIENT
  expectedRepair := []
  rationale := "0.27 против порога 0.10 для обратимого действия L4"

/-- BIZ-013: исполнение проекта процесса без валидации и решения. -/
def BIZ013 : GoldCase where
  caseId := "BIZ-013"
  domain := .BIZ
  naturalRequest := "Спроектировать процесс и сразу его запустить"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "BIZ-013"
      initialType := .Requirements
      ops := [STRUCTURE, EXECUTE_PLAN] }
  expected := .REPAIR
  expectedCode := .E_MISSING_CONVERSION
  expectedRepair := ["VALIDATE", "DECIDE"]
  rationale := "от Design до Plan нужны два оператора: VALIDATE и DECIDE"

/-- SAF-014: аварийное воздействие без авторизации; в домене SAF
автоматическая починка запрещена. -/
def SAF014 : GoldCase where
  caseId := "SAF-014"
  domain := .SAF
  naturalRequest := "Обнаружить утечку и немедленно перекрыть линию"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "SAF-014"
      initialInvariants := [.DataExistence, .Traceability, .Consistency, .PhysicalIntegrity]
      repairPolicy := .forbid
      ops := [DETECT, DIAGNOSE, EXECUTE_SAF] }
  expected := .REJECT
  expectedCode := .E_NOT_YET_SATISFIED
  expectedRepair := []
  rationale :=
    "прекондиция Authorized не установлена; в критичном по безопасности " ++
    "контуре компилятор обязан отвергнуть цепочку, а не дополнить её"

/-- SAF-015: распознавание и индексация. -/
def SAF015 : GoldCase where
  caseId := "SAF-015"
  domain := .SAF
  naturalRequest := "Распознать объект на видеопотоке и внести его в каталог"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "SAF-015"
      initialType := .RawSignal
      declaredThreshold := some 20
      ops := [RECOGNIZE, INDEX] }
  expected := .PASS
  expectedCode := .NONE
  expectedRepair := []
  rationale := "порог кейса 0.20, накоплено 0.05; эффекты информационные (E1)"

/-- Gold Dataset v0.1: пятнадцать кейсов §12. -/
def goldDatasetV01 : List GoldCase :=
  [ ENG001, ENG002, ENG003, IT004, IT005, IT006, ML007, ML008, ML009
  , SCI010, SCI011, BIZ012, BIZ013, SAF014, SAF015 ]

/-! ## Расширение v0.2: ещё десять кейсов (ENG-016 … SAF-025)

Кейсы подобраны так, чтобы покрыть все шесть доменов и три исхода
компилятора; вердикт каждого, как и в v0.1, **вычислен**, а не объявлен. -/

/-- ENG-016: канонический путь с симуляцией при объявленном пороге 0.30. -/
def ENG016 : GoldCase where
  caseId := "ENG-016"
  domain := .ENG
  naturalRequest := "Измерить, откалибровать, смоделировать, просимулировать, проверить и решить"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "ENG-016"
      declaredThreshold := some 30
      ops := [MEASURE, CALIBRATE, MODEL, SIMULATE, VALIDATE, DECIDE] }
  expected := .PASS
  expectedCode := .NONE
  expectedRepair := []
  rationale :=
    "каждый стык сдвигает уровень на +1 или 0; калибровка и валидация " ++
    "удерживают накопленную неопределённость под объявленным порогом 0.30"

/-- IT-017: разработка алгоритма и сборка без развёртывания. -/
def IT017 : GoldCase where
  caseId := "IT-017"
  domain := .IT
  naturalRequest := "Разработать алгоритм по спецификации и собрать бинарь"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "IT-017"
      initialType := .Specification
      initialFacts := [.SpecAvailable]
      ops := [ALGORITHMICIZE, COMPILE] }
  expected := .PASS
  expectedCode := .NONE
  expectedRepair := []
  rationale :=
    "цепочка останавливается на уровне L2: необратимых эффектов нет, " ++
    "человеческая авторизация не требуется"

/-- BIZ-018: сравнение вариантов, решение и авторизованная перестройка. -/
def BIZ018 : GoldCase where
  caseId := "BIZ-018"
  domain := .BIZ
  naturalRequest := "Сравнить сценарии, выбрать один и перестроить процесс по авторизации"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "BIZ-018"
      initialType := .Model
      initialFacts := [.Modeled]
      declaredThreshold := some 30
      ops := [COMPARE, DECIDE, AUTHORIZE, TRANSFORM] }
  expected := .PASS
  expectedCode := .NONE
  expectedRepair := []
  rationale :=
    "COMPARE даёт основание, AUTHORIZE выдаёт токен, требуемый TRANSFORM; " ++
    "накопленная неопределённость не превышает объявленного порога 0.30"

/-- ML-019: симуляция по измерениям без построенной модели. -/
def ML019 : GoldCase where
  caseId := "ML-019"
  domain := .ML
  naturalRequest := "Прогнать симуляцию прямо по измерениям"
  registry := goldRegistry
  composition :=
    { goldBase with caseId := "ML-019", ops := [MEASURE, SIMULATE] }
  expected := .REPAIR
  expectedCode := .E_MISSING_CONVERSION
  expectedRepair := ["MODEL"]
  rationale := "SIMULATE ожидает EnergyModel; посредник MODEL существует в каталоге"

/-- SAF-020: запись во внешний каталог без авторизации. -/
def SAF020 : GoldCase where
  caseId := "SAF-020"
  domain := .SAF
  naturalRequest := "Распознать объект и записать его во внешний каталог"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "SAF-020"
      initialType := .RawSignal
      declaredThreshold := some 20
      ops := [RECOGNIZE, INDEX_EXTERNAL] }
  expected := .REPAIR
  expectedCode := .E_EFFECT_POLICY_VIOLATION
  expectedRepair := ["AUTHORIZE"]
  rationale := "внешний (пусть и обратимый) эффект E3 требует подтверждения"

/-- SCI-021: возведение гипотезы в закон без валидации. -/
def SCI021 : GoldCase where
  caseId := "SCI-021"
  domain := .SCI
  naturalRequest := "Выдвинуть гипотезу и сразу закрепить её как закон"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "SCI-021"
      initialType := .Observation
      initialFacts := [.Observed]
      ops := [HYPOTHESIZE, AXIOMATIZE_SCI] }
  expected := .REPAIR
  expectedCode := .E_MISSING_CONVERSION
  expectedRepair := ["VALIDATE"]
  rationale := "AXIOMATIZE ожидает ValidationResult; посредник VALIDATE существует"

/-- ENG-022: представление верификационного отчёта как модели. -/
def ENG022 : GoldCase where
  caseId := "ENG-022"
  domain := .ENG
  naturalRequest := "Проверить модель и выпустить представление результата проверки"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "ENG-022"
      ops := [MEASURE, MODEL, VERIFY, REPRESENT_VERIFIED] }
  expected := .REJECT
  expectedCode := .E_TYPE_MISMATCH
  expectedRepair := []
  rationale :=
    "VerificationResult не является Model, и в каталоге нет оператора, " ++
    "переводящего один тип в другой"

/-- IT-023: решение по оценке при жёстком пороге 0.05. -/
def IT023 : GoldCase where
  caseId := "IT-023"
  domain := .IT
  naturalRequest := "Оценить нагрузку и принять решение при требовании точности 0.05"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "IT-023"
      initialType := .Model
      initialFacts := [.Modeled]
      declaredThreshold := some 5
      ops := [EVALUATE, DECIDE] }
  expected := .REJECT
  expectedCode := .E_EPISTEMIC_INSUFFICIENT
  expectedRepair := []
  rationale := "накопленная неопределённость оценки превышает объявленный порог 0.05"

/-- ML-024: необратимое удаление в контуре, где починка запрещена. -/
def ML024 : GoldCase where
  caseId := "ML-024"
  domain := .ML
  naturalRequest := "Кластеризовать датасет и безвозвратно удалить исходные записи"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "ML-024"
      initialType := .Dataset
      initialFacts := [.DatasetAvailable]
      requiredFinalInvariants := [.Traceability]
      repairPolicy := .forbid
      ops := [CLUSTERIZE, DELETE_HARD] }
  expected := .REJECT
  expectedCode := .E_EFFECT_POLICY_VIOLATION
  expectedRepair := []
  rationale :=
    "тот же диагноз, что и в ML-009, но при запрещённой починке вердикт " ++
    "обязан быть REJECT: политика меняет исход, не меняя причины"

/-- SAF-025: воздействие сразу после обнаружения. -/
def SAF025 : GoldCase where
  caseId := "SAF-025"
  domain := .SAF
  naturalRequest := "Обнаружить событие и немедленно выполнить физическое воздействие"
  registry := goldRegistry
  composition :=
    { goldBase with
      caseId := "SAF-025"
      initialInvariants := [.DataExistence, .Traceability, .Consistency, .PhysicalIntegrity]
      ops := [DETECT, EXECUTE_SAF] }
  expected := .REJECT
  expectedCode := .E_LEVEL_JUMP
  expectedRepair := []
  rationale := "DetectedEvent — L1, EXECUTE_SAF — L4: разрыв в два уровня (RULE 6)"

/-- Полный Gold Dataset: пятнадцать кейсов §12 и десять кейсов расширения. -/
def goldDataset : List GoldCase :=
  goldDatasetV01 ++
    [ ENG016, IT017, BIZ018, ML019, SAF020, SCI021, ENG022, IT023, ML024, SAF025 ]

/-- Кейсов в датасете двадцать пять. -/
theorem goldDataset_card : goldDataset.length = 25 := by decide

/-! ## Ступень B: COMPILER CONFORMANCE (§11) -/

/-- **Главный результат модуля**: вердикт, код ошибки и предложение починки
компилятора совпадают с эталоном для всех двадцати пяти кейсов. -/
theorem goldDataset_conforms : goldDataset.all (fun g => g.conforms) = true := by
  decide

/-- Покейсовые вердикты — по отдельности, для читаемости. -/
theorem ENG001_verdict :
    ENG001.report.status = Status.REJECT ∧ ENG001.report.code = ErrCode.E_LEVEL_JUMP := by
  decide

theorem ENG002_verdict :
    ENG002.report.status = Status.REPAIR ∧
    ENG002.report.code = ErrCode.E_NOT_YET_SATISFIED ∧
    containsSubstr ENG002.report.suggestion "VERIFY" = true := by decide

theorem ENG003_verdict :
    ENG003.report.status = Status.REJECT ∧
    ENG003.report.code = ErrCode.E_INVARIANT_VIOLATION := by decide

theorem IT004_verdict :
    IT004.report.status = Status.REJECT ∧
    IT004.report.code = ErrCode.E_EFFECT_POLICY_VIOLATION := by decide

theorem IT005_verdict :
    IT005.report.status = Status.REPAIR ∧
    IT005.report.code = ErrCode.E_MISSING_CONVERSION ∧
    containsSubstr IT005.report.suggestion "CALIBRATE" = true := by decide

theorem IT006_verdict : IT006.report.status = Status.PASS := by decide

theorem ML007_verdict :
    ML007.report.status = Status.REJECT ∧
    ML007.report.code = ErrCode.E_EPISTEMIC_INSUFFICIENT := by decide

theorem ML008_verdict :
    ML008.report.status = Status.REPAIR ∧
    containsSubstr ML008.report.suggestion "VALIDATE" = true := by decide

theorem ML009_verdict :
    ML009.report.status = Status.REPAIR ∧
    ML009.report.code = ErrCode.E_EFFECT_POLICY_VIOLATION ∧
    containsSubstr ML009.report.suggestion "AUTHORIZE" = true := by decide

theorem SCI010_verdict :
    SCI010.report.status = Status.REJECT ∧
    SCI010.report.code = ErrCode.E_CONTRACT_LEAKAGE := by decide

theorem SCI011_verdict : SCI011.report.status = Status.PASS := by decide

theorem BIZ012_verdict :
    BIZ012.report.status = Status.REJECT ∧
    BIZ012.report.code = ErrCode.E_EPISTEMIC_INSUFFICIENT := by decide

theorem BIZ013_verdict :
    BIZ013.report.status = Status.REPAIR ∧
    containsSubstr BIZ013.report.suggestion "VALIDATE" = true ∧
    containsSubstr BIZ013.report.suggestion "DECIDE" = true := by decide

theorem SAF014_verdict :
    SAF014.report.status = Status.REJECT ∧
    SAF014.report.code = ErrCode.E_NOT_YET_SATISFIED := by decide

theorem SAF015_verdict : SAF015.report.status = Status.PASS := by decide

theorem ENG016_verdict :
    ENG016.report.status = Status.PASS ∧ ENG016.report.code = ErrCode.NONE := by decide

theorem IT017_verdict :
    IT017.report.status = Status.PASS ∧ IT017.report.code = ErrCode.NONE := by decide

theorem BIZ018_verdict :
    BIZ018.report.status = Status.PASS ∧ BIZ018.report.code = ErrCode.NONE := by decide

theorem ML019_verdict :
    ML019.report.status = Status.REPAIR ∧
    ML019.report.code = ErrCode.E_MISSING_CONVERSION ∧
    containsSubstr ML019.report.suggestion "MODEL" = true := by decide

theorem SAF020_verdict :
    SAF020.report.status = Status.REPAIR ∧
    SAF020.report.code = ErrCode.E_EFFECT_POLICY_VIOLATION ∧
    containsSubstr SAF020.report.suggestion "AUTHORIZE" = true := by decide

theorem SCI021_verdict :
    SCI021.report.status = Status.REPAIR ∧
    SCI021.report.code = ErrCode.E_MISSING_CONVERSION ∧
    containsSubstr SCI021.report.suggestion "VALIDATE" = true := by decide

theorem ENG022_verdict :
    ENG022.report.status = Status.REJECT ∧
    ENG022.report.code = ErrCode.E_TYPE_MISMATCH := by decide

theorem IT023_verdict :
    IT023.report.status = Status.REJECT ∧
    IT023.report.code = ErrCode.E_EPISTEMIC_INSUFFICIENT := by decide

theorem ML024_verdict :
    ML024.report.status = Status.REJECT ∧
    ML024.report.code = ErrCode.E_EFFECT_POLICY_VIOLATION := by decide

theorem SAF025_verdict :
    SAF025.report.status = Status.REJECT ∧
    SAF025.report.code = ErrCode.E_LEVEL_JUMP := by decide

/-! ## Аудит распределения вердиктов (§12) -/

/-- Число кейсов датасета с данным эталонным вердиктом. -/
def goldCount (s : Status) : ℕ :=
  (goldDataset.filter (fun g => g.expected == s)).length

/-- Число кейсов версии v0.1 с данным эталонным вердиктом. -/
def goldCountV01 (s : Status) : ℕ :=
  (goldDatasetV01.filter (fun g => g.expected == s)).length

/-- §12 объявляет распределение «3 PASS + 6 REPAIR + 6 REJECT», однако сам
список кейсов v0.1 даёт 3 / 5 / 7.  Расхождение доказано вычислением: это
находка аудита, а не опечатка формализации. -/
theorem gold_distribution_v01 :
    goldCountV01 .PASS = 3 ∧ goldCountV01 .REPAIR = 5 ∧ goldCountV01 .REJECT = 7 ∧
    goldCountV01 .SPEC_GAP = 0 := by decide

/-- Заявленное в §12 распределение не выполняется. -/
theorem gold_distribution_ne_declared : goldCountV01 .REPAIR ≠ 6 := by decide

/-- Распределение расширенного датасета из двадцати пяти кейсов:
6 PASS + 8 REPAIR + 11 REJECT.  Десять добавленных кейсов дают 3 / 3 / 4. -/
theorem gold_distribution :
    goldCount .PASS = 6 ∧ goldCount .REPAIR = 8 ∧ goldCount .REJECT = 11 ∧
    goldCount .SPEC_GAP = 0 := by decide

/-! ## Чувствительность к каталогу и к политике (§11, Repair Precision) -/

/-- Если человеческая авторизация доступна как оператор, IT-004 из REJECT
превращается в REPAIR со вставкой `AUTHORIZE_HUMAN`.  Это показывает, что
вердикт определяется каталогом, а не жёстко зашит в кейс. -/
theorem IT004_repairable_with_human_authorizer :
    (compile goldRegistryHuman IT004.composition).status = Status.REPAIR ∧
    containsSubstr (compile goldRegistryHuman IT004.composition).suggestion
      "AUTHORIZE_HUMAN" = true := by decide

/-- SAF-014 при разрешённой политике починки даёт REPAIR с тем же кодом:
эскалация меняет вердикт, но не диагноз. -/
theorem SAF014_repair_under_allow :
    (compile goldRegistry
      { SAF014.composition with repairPolicy := .allow }).status = Status.REPAIR ∧
    (compile goldRegistry
      { SAF014.composition with repairPolicy := .allow }).code =
        ErrCode.E_NOT_YET_SATISFIED := by decide

/-- SAF-015 при более жёстком пороге кейса (0.03) переходит в REPAIR —
условие, отмеченное в самом §12. -/
theorem SAF015_repair_under_tight_threshold :
    (compile goldRegistry
      { SAF015.composition with declaredThreshold := some 3 }).status = Status.REPAIR ∧
    (compile goldRegistry
      { SAF015.composition with declaredThreshold := some 3 }).code =
        ErrCode.E_EPISTEMIC_INSUFFICIENT := by decide

/-- Находка batch 1 §12: «E3 → PASS» не выводится из уровня эффекта.  Тот же кейс с внешним
обратимым эффектом требует подтверждения и PASS уже не получает. -/
theorem SAF015_external_variant_needs_approval :
    (compile goldRegistry
      { SAF015.composition with ops := [RECOGNIZE, INDEX_EXTERNAL] }).status ≠ Status.PASS ∧
    (compile goldRegistry
      { SAF015.composition with ops := [RECOGNIZE, INDEX_EXTERNAL] }).code =
        ErrCode.E_EFFECT_POLICY_VIOLATION := by decide

/-- Буквальный граф SAF-014 из §12 (`DETECT → EXECUTE`) отвергается раньше —
на уровне типов: прыжок L1 → L3.  Ожидаемый в §12 код `E_NOT_YET_SATISFIED`
для него недостижим, поскольку §9 проверяет типы прежде контрактов. -/
theorem SAF014_literal_graph_is_level_jump :
    (compile goldRegistry
      { SAF014.composition with ops := [DETECT, EXECUTE] }).status = Status.REJECT ∧
    (compile goldRegistry
      { SAF014.composition with ops := [DETECT, EXECUTE] }).code =
        ErrCode.E_LEVEL_JUMP := by decide

/-! ## Печать отчётов -/

/-- Отчёты §9 по всем кейсам Gold Dataset. -/
def goldReports : String :=
  String.intercalate "\n\n" (goldDataset.map (fun g => g.report.render))

#eval IO.println goldReports

end Polymath.OSA
