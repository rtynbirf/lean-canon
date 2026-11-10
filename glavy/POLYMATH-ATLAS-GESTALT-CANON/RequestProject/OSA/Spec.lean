/-
# OSA-3.2 — формальная спецификация компилятора композиций операторов

Этот модуль формализует спецификацию **OSA-3.2 Conformance** (Operator
Schema Architecture): схему оператора (§2), иерархию типов (§3), уровни
эффектов (§4), векторную модель неопределённости (§5), разграничение
операторов решения (§6), правила компиляции (§7), реестр кодов ошибок (§8)
и формат вывода вердикта (§9).

Все проверки реализованы как *вычислимые* булевы функции, поэтому вердикт
для конкретной композиции получается вычислением (`decide` / `#eval`), а
общие свойства компилятора доказываются в `RequestProject.OSA.Theorems`.

Осознанные решения при формализации (места, где текст спецификации
допускает две интерпретации; §11.A требует минимизировать одновременно
false accept и false reject):

* §7 RULE 4A объявляет статус REPAIR для E4 без токена авторизации, тогда как
  реестр §8 указывает REJECT.  Реализовано согласование: REPAIR, если в
  реестре операторов существует оператор авторизации, который можно вставить,
  иначе REJECT (починка невозможна).
* §3 разрешает конверсию внутри уровня «явно»; поэтому совместимость типов
  требует *объявленной* конверсии (`convTable`), а не автоматического
  совпадения уровней.
* §5/§11.C: универсальной формулы агрегации нет.  Правило агрегации — поле
  композиции; если оно не задано, компилятор выдаёт
  `UNCERTAINTY_RULE_NOT_DEFINED` (SPEC_GAP), а не подставляет формулу.
* Пороги §5 определены только для выходов уровней L2–L4; выход L0/L1 даёт
  `SPEC_GAP_UNDEFINED_THRESHOLD` (§10.8), а не «по аналогии».

Величины неопределённости представлены натуральными числами в сотых долях
(0.30 = `30`), что делает все сравнения разрешимыми.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

/-! ## §3. Иерархия типов -/

/-- Пять уровней иерархии типов OSA: реальность, данные, представление,
решение, действие. -/
inductive TypeLevel
  | L0 | L1 | L2 | L3 | L4
  deriving DecidableEq, Repr, Inhabited

/-- Числовой индекс уровня (для правила `RULE 6: LEVEL_JUMP`). -/
def TypeLevel.idx : TypeLevel → ℕ
  | .L0 => 0 | .L1 => 1 | .L2 => 2 | .L3 => 3 | .L4 => 4

/-- Типы OSA-3.2, сгруппированные по уровням §3. -/
inductive OSAType
  -- L0 REALITY
  | ObjectState | PhysicalMeasurement | EnvironmentState | RawSignal
  -- L1 DATA
  | MeasuredValue | RegisteredEvent | CalibratedValue | SensorReading
  | Observation | DetectedEvent | RecognitionResult | IndexEntry | Dataset
  | DeletionRecord
  -- L2 REPRESENTATION
  | Model | Specification | FormalDescription | EnergyModel | SimulationResult
  | ValidationResult | VerificationResult
  | SourceCode | CompiledBinary | Algorithm | Hypothesis | ExperimentalResult
  | ClusterModel | AnalysisResult | ComparisonResult | EvaluationResult
  | Requirements | Design | Representation | FormalAxiom
  -- L3 DECISION
  | Plan | Decision | PolicyChoice | AuthorizationToken | DiagnosticResult
  -- L4 ACTION
  | SystemStateChange | Deployment | PhysicalActuation | IrreversibleChange
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Уровень типа согласно §3. -/
def OSAType.level : OSAType → TypeLevel
  | .ObjectState | .PhysicalMeasurement | .EnvironmentState | .RawSignal => .L0
  | .MeasuredValue | .RegisteredEvent | .CalibratedValue | .SensorReading
  | .Observation | .DetectedEvent | .RecognitionResult | .IndexEntry
  | .Dataset | .DeletionRecord => .L1
  | .Model | .Specification | .FormalDescription | .EnergyModel
  | .SimulationResult | .ValidationResult | .VerificationResult
  | .SourceCode | .CompiledBinary | .Algorithm | .Hypothesis
  | .ExperimentalResult | .ClusterModel | .AnalysisResult | .ComparisonResult
  | .EvaluationResult | .Requirements | .Design | .Representation
  | .FormalAxiom => .L2
  | .Plan | .Decision | .PolicyChoice | .AuthorizationToken
  | .DiagnosticResult => .L3
  | .SystemStateChange | .Deployment | .PhysicalActuation
  | .IrreversibleChange => .L4

/-- Имя типа (для справочной системы и визуализации). -/
def OSAType.name : OSAType → String
  | .ObjectState => "ObjectState"
  | .PhysicalMeasurement => "PhysicalMeasurement"
  | .EnvironmentState => "EnvironmentState"
  | .RawSignal => "RawSignal"
  | .MeasuredValue => "MeasuredValue"
  | .RegisteredEvent => "RegisteredEvent"
  | .CalibratedValue => "CalibratedValue"
  | .SensorReading => "SensorReading"
  | .Observation => "Observation"
  | .DetectedEvent => "DetectedEvent"
  | .RecognitionResult => "RecognitionResult"
  | .IndexEntry => "IndexEntry"
  | .Dataset => "Dataset"
  | .DeletionRecord => "DeletionRecord"
  | .Model => "Model"
  | .Specification => "Specification"
  | .FormalDescription => "FormalDescription"
  | .EnergyModel => "EnergyModel"
  | .SimulationResult => "SimulationResult"
  | .ValidationResult => "ValidationResult"
  | .VerificationResult => "VerificationResult"
  | .SourceCode => "SourceCode"
  | .CompiledBinary => "CompiledBinary"
  | .Algorithm => "Algorithm"
  | .Hypothesis => "Hypothesis"
  | .ExperimentalResult => "ExperimentalResult"
  | .ClusterModel => "ClusterModel"
  | .AnalysisResult => "AnalysisResult"
  | .ComparisonResult => "ComparisonResult"
  | .EvaluationResult => "EvaluationResult"
  | .Requirements => "Requirements"
  | .Design => "Design"
  | .Representation => "Representation"
  | .FormalAxiom => "FormalAxiom"
  | .Plan => "Plan"
  | .Decision => "Decision"
  | .PolicyChoice => "PolicyChoice"
  | .AuthorizationToken => "AuthorizationToken"
  | .DiagnosticResult => "DiagnosticResult"
  | .SystemStateChange => "SystemStateChange"
  | .Deployment => "Deployment"
  | .PhysicalActuation => "PhysicalActuation"
  | .IrreversibleChange => "IrreversibleChange"

/-- Имя уровня иерархии. -/
def TypeLevel.name : TypeLevel → String
  | .L0 => "L0" | .L1 => "L1" | .L2 => "L2" | .L3 => "L3" | .L4 => "L4"

/-- Полное имя типа вместе с уровнем, как в §3 (например,
`L1_MeasuredValue`). -/
def typeStr (t : OSAType) : String := t.level.name ++ "_" ++ t.name

/-- Расстояние между уровнями двух типов (|x − y| из `RULE 6`). -/
def levelGap (a b : OSAType) : ℕ :=
  Nat.dist a.level.idx b.level.idx

/-- Объявленные отношения подтипирования (все — внутри одного уровня). -/
def subtypePairs : List (OSAType × OSAType) :=
  [ (.CalibratedValue, .MeasuredValue)
  , (.SensorReading, .MeasuredValue)
  , (.EnergyModel, .Model)
  , (.SimulationResult, .Model)
  , (.FormalDescription, .Specification)
  , (.Design, .Model)
  , (.ClusterModel, .Model)
  , (.AnalysisResult, .Model)
  , (.Hypothesis, .Model) ]

/-- `a` — подтип `b`. -/
def isSubtype (a b : OSAType) : Bool := subtypePairs.contains (a, b)

/-- Объявленные явные конверсии внутри уровня (§3, «явная конверсия между
типами одного уровня допускается без промежуточного оператора»). -/
def convTable : List (OSAType × OSAType) :=
  [ (.RawSignal, .PhysicalMeasurement)
  , (.MeasuredValue, .SensorReading)
  , (.SensorReading, .MeasuredValue)
  , (.EnergyModel, .Specification)
  , (.Plan, .PolicyChoice)
  , (.PolicyChoice, .Plan)
  , (.Algorithm, .SourceCode)
  , (.ComparisonResult, .ValidationResult)
  , (.EvaluationResult, .ValidationResult)
  , (.ExperimentalResult, .ValidationResult)
  , (.MeasuredValue, .Dataset)
  , (.CalibratedValue, .Dataset) ]

/-- `RULE 1`: типы совместимы, если они равны, либо первый — подтип второго,
либо объявлена явная конверсия. -/
def typeCompatible (a b : OSAType) : Bool :=
  a == b || isSubtype a b || convTable.contains (a, b)

/-! ## §4. Уровни эффектов -/

/-- Уровни побочного эффекта E0–E4. -/
inductive EffectLevel
  | E0 | E1 | E2 | E3 | E4
  deriving DecidableEq, Repr, Inhabited

/-- Атомарные побочные эффекты, используемые в контрактах операторов. -/
inductive Effect
  | InformationWrite | ResourceBurn | ExternalReversible
  | ExternalIrreversible | DataDeletion
  deriving DecidableEq, Repr, Inhabited

/-- Обратимость оператора. -/
inductive Reversibility
  | reversible | partiallyReversible | irreversible
  deriving DecidableEq, Repr, Inhabited

/-! ## Контрактные атомы -/

/-- Атомарные факты, используемые в pre/postconditions операторов. -/
inductive Fact
  | RawDataAvailable | Measured | Calibrated | Modeled | Simulated
  | Validated | Verified | RiskAssessed | Approved | PlanSelected
  | Authorized | Executed | ExperimentRun
  | Observed | Hypothesized | Formalized | Represented | Axiomatized
  | SpecAvailable | AlgorithmDesigned | Compiled | Deployed
  | DatasetAvailable | Clustered | Detected | Diagnosed | Evaluated
  | Compared | EvidenceAvailable | Structured | Recognized | Indexed
  | Transformed
  deriving DecidableEq, Repr, Inhabited

/-- Инварианты системы, которые операторы сохраняют или уничтожают. -/
inductive Invariant
  | DataExistence | Traceability | Consistency | PhysicalIntegrity
  | ReversibilityMargin
  deriving DecidableEq, Repr, Inhabited

/-! ## §5. Модель неопределённости -/

/-- Вектор неопределённости: четыре независимые компоненты (§5).
Значения — в сотых долях единицы (0.30 ↦ 30). -/
structure Uncert where
  aleatoric : ℕ
  epistemic : ℕ
  model : ℕ
  provenance : ℕ
  deriving DecidableEq, Repr, Inhabited

namespace Uncert

/-- Нулевой вектор неопределённости. -/
def zero : Uncert := ⟨0, 0, 0, 0⟩

/-- Покомпонентная сумма. -/
def add (u v : Uncert) : Uncert :=
  ⟨u.aleatoric + v.aleatoric, u.epistemic + v.epistemic,
   u.model + v.model, u.provenance + v.provenance⟩

/-- Покомпонентный максимум. -/
def max (u v : Uncert) : Uncert :=
  ⟨Nat.max u.aleatoric v.aleatoric, Nat.max u.epistemic v.epistemic,
   Nat.max u.model v.model, Nat.max u.provenance v.provenance⟩

/-- Покомпонентное усечённое вычитание (действие оператора снижения
неопределённости). -/
def sub (u v : Uncert) : Uncert :=
  ⟨u.aleatoric - v.aleatoric, u.epistemic - v.epistemic,
   u.model - v.model, u.provenance - v.provenance⟩

/-- Наибольшая компонента вектора. -/
def peak (u : Uncert) : ℕ :=
  Nat.max (Nat.max u.aleatoric u.epistemic) (Nat.max u.model u.provenance)

/-- Общая (суммарная) оценка — сумма компонент. -/
def total (u : Uncert) : ℕ :=
  u.aleatoric + u.epistemic + u.model + u.provenance

/-- Покомпонентный порядок. -/
def le (u v : Uncert) : Prop :=
  u.aleatoric ≤ v.aleatoric ∧ u.epistemic ≤ v.epistemic ∧
  u.model ≤ v.model ∧ u.provenance ≤ v.provenance

end Uncert

/-- Правило агрегации неопределённости по цепочке.  Согласно §11.C
универсальной формулы не существует, поэтому правило задаётся для каждой
композиции отдельно. -/
inductive AggRule
  | additive        -- покомпонентное сложение
  | maximum         -- покомпонентный максимум
  deriving DecidableEq, Repr, Inhabited

/-- Пороги §5 для выходного типа.  Для выходов уровней L0/L1 порог не
определён спецификацией. -/
def thresholdFor (t : OSAType) (r : Reversibility) : Option ℕ :=
  match t.level with
  | .L2 => some 30
  | .L3 => some 15
  | .L4 => match r with
      | .irreversible => some 5
      | _ => some 10
  | _ => none

/-! ## §2. Схема оператора -/

/-- Схема оператора OSA-3.2 (§2). -/
structure Operator where
  id : String
  level : TypeLevel
  inputType : OSAType
  outputType : OSAType
  /-- Прекондиции: факты, которые должны быть истинны до запуска. -/
  pre : List Fact
  /-- Постусловия: факты, гарантированно истинные после успеха. -/
  post : List Fact
  /-- Негарантированные побочные исходы (используются правилом 2B). -/
  sideFacts : List Fact
  /-- Инварианты, необходимые оператору для работы (`Requires`). -/
  requiresInv : List Invariant
  preserves : List Invariant
  destroys : List Invariant
  effectLevel : EffectLevel
  producedEffects : List Effect
  allowedEffects : List Effect
  forbiddenEffects : List Effect
  /-- Неопределённость, добавляемая оператором. -/
  uncertainty : Uncert
  /-- Неопределённость, снимаемая оператором (VALIDATE, CALIBRATE, ADD_DATA). -/
  reduction : Uncert
  reversibility : Reversibility
  requiresAuthorization : Bool
  /-- §4/§6: действие требует токена, обеспеченного человеком (DEPLOY), а не
  токена, выданного автоматическим оператором авторизации. -/
  humanAuthorizationRequired : Bool
  /-- Оператор выдаёт токен, обеспеченный человеческим решением. -/
  grantsHumanAuthorization : Bool
  requiredPreOps : List String
  forbiddenPreOps : List String
  deriving Repr, Inhabited

/-- Оператор снижает неопределённость (кандидат на починку по §5, правило
тренда). -/
def Operator.reduces (o : Operator) : Bool := o.reduction != Uncert.zero

/-- Оператор выдаёт токен авторизации (кандидат на вставку по `RULE 4A`). -/
def Operator.isAuthorizer (o : Operator) : Bool :=
  o.outputType == OSAType.AuthorizationToken

/-- Оператор порождает подтверждение (`approval`, `RULE 4B`). -/
def Operator.isApprover (o : Operator) : Bool := o.post.contains Fact.Approved

/-- Оператор `x` может выдать токен, пригодный для оператора `o`: он является
оператором авторизации и, если `o` требует человеческой авторизации, выдаёт
именно такой токен (§4, §6 DEPLOY). -/
def Operator.authorizes (o x : Operator) : Bool :=
  x.isAuthorizer && (!o.humanAuthorizationRequired || x.grantsHumanAuthorization)

/-- Политика починки композиции.  Для критичных по безопасности композиций
(домен SAF) автоматическая починка запрещена: компилятор обязан отвергнуть
цепочку, а не молча дополнить её (§11, «paranoia trap» работает в обе
стороны). -/
inductive RepairPolicy
  | allow | forbid
  deriving DecidableEq, Repr, Inhabited

/-! ## Композиция -/

/-- Предложенный граф операторов — линейная композиция с начальным
контекстом.  Правило агрегации неопределённости задаётся здесь (§11.C). -/
structure Composition where
  caseId : String
  initialType : OSAType
  initialFacts : List Fact
  initialInvariants : List Invariant
  /-- Инварианты, которые должны сохраниться к концу всей композиции
  (глобальная проверка §11.D). -/
  requiredFinalInvariants : List Invariant
  ops : List Operator
  agg : Option AggRule
  /-- §12: порог неопределённости, объявленный самим кейсом.  Если он задан,
  он имеет приоритет над табличным порогом уровня (§5). -/
  declaredThreshold : Option ℕ
  /-- Разрешена ли автоматическая починка (§11). -/
  repairPolicy : RepairPolicy
  deriving Repr, Inhabited

/-! ## §8. Реестр кодов ошибок -/

/-- Коды ошибок §8 плюс два кода пробелов спецификации (§10.8, §11.C). -/
inductive ErrCode
  | NONE
  | E_TYPE_MISMATCH
  | E_INVARIANT_VIOLATION
  | E_EFFECT_POLICY_VIOLATION
  | E_EPISTEMIC_INSUFFICIENT
  | E_CONTRACT_LEAKAGE
  | E_LEVEL_JUMP
  | E_EFFECT_LEAKAGE
  | E_MISSING_CONVERSION
  | E_NOT_YET_SATISFIED
  | E_UNSATISFIABLE_CONTRACT
  | E_INVARIANT_LOSS
  | UNCERTAINTY_RULE_NOT_DEFINED
  | SPEC_GAP_UNDEFINED_THRESHOLD
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Итоговый статус компиляции (§9). -/
inductive Status
  | PASS | REPAIR | REJECT | SPEC_GAP
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Тяжесть обнаруженного нарушения.  Обратите внимание: `PASS` не входит в
образ `Severity.toStatus`, поэтому статус `PASS` возможен только при полном
отсутствии нарушений. -/
inductive Severity
  | REPAIR | REJECT | SPEC_GAP
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Отображение тяжести в статус §9. -/
def Severity.toStatus : Severity → Status
  | .REPAIR => .REPAIR
  | .REJECT => .REJECT
  | .SPEC_GAP => .SPEC_GAP

/-- Эскалация статуса под действием политики починки: если автоматическая
починка запрещена, вердикт REPAIR становится REJECT (код ошибки при этом
сохраняется). -/
def Status.escalate : RepairPolicy → Status → Status
  | .allow, s => s
  | .forbid, .REPAIR => .REJECT
  | .forbid, s => s

/-- Обнаруженное нарушение: тяжесть, код §8, обоснование и предложение
починки. -/
structure Failure where
  sev : Severity
  code : ErrCode
  detail : String
  suggestion : String
  deriving Repr, Inhabited

/-! ## §7. Правила компиляции -/

/-- Списковое включение с разрешимым равенством. -/
def subsetOf {α : Type} [BEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => ys.contains x)

/-- Поиск двухшаговой вставки: пары операторов, соединяющей тип `t` с типом
`goal` (§11.6, Repair Precision: починка может требовать двух операторов,
например VALIDATE и DECIDE). -/
def findPath2 (reg : List Operator) (t goal : OSAType) :
    Option (Operator × Operator) :=
  (reg.flatMap (fun c1 =>
      if typeCompatible t c1.inputType then
        reg.filterMap (fun c2 =>
          if typeCompatible c1.outputType c2.inputType &&
             typeCompatible c2.outputType goal then some (c1, c2) else none)
      else [])).head?

/-- `RULE 1` + `RULE 6`: проверка типовой корректности цепочки.
`reg` — реестр известных операторов, используемый для поиска
оператора-посредника при `E_MISSING_CONVERSION`. -/
def typeDiag (reg : List Operator) : OSAType → List Operator → Option Failure
  | _, [] => none
  | t, o :: rest =>
    if typeCompatible t o.inputType then typeDiag reg o.outputType rest
    else if 2 ≤ levelGap t o.inputType then
      some { sev := .REJECT, code := .E_LEVEL_JUMP
           , detail := "level jump into " ++ o.id
           , suggestion := "" }
    else
      match reg.find? (fun c => typeCompatible t c.inputType &&
                                typeCompatible c.outputType o.inputType) with
      | some c =>
          some { sev := .REPAIR, code := .E_MISSING_CONVERSION
               , detail := "output type is not accepted by " ++ o.id
               , suggestion := "insert " ++ c.id ++ " before " ++ o.id }
      | none =>
        match findPath2 reg t o.inputType with
        | some (c1, c2) =>
            some { sev := .REPAIR, code := .E_MISSING_CONVERSION
                 , detail := "output type is not accepted by " ++ o.id
                 , suggestion := "insert " ++ c1.id ++ " and " ++ c2.id ++
                     " before " ++ o.id }
        | none =>
            some { sev := .REJECT, code := .E_TYPE_MISMATCH
                 , detail := "output type is not accepted by " ++ o.id
                 , suggestion := "" }

/-- `RULE 2` + `RULE 2B`: контрактная корректность.
`g` — накопленные *гарантированные* факты, `s` — накопленные негарантированные
побочные исходы, `prev` — идентификаторы уже выполненных операторов. -/
def contractDiag (reg : List Operator) :
    List Fact → List Fact → List String → List Operator → Option Failure
  | _, _, _, [] => none
  | g, s, prev, o :: rest =>
    if subsetOf o.pre g then
      if !subsetOf o.requiredPreOps prev then
        some { sev := .REPAIR, code := .E_NOT_YET_SATISFIED
             , detail := o.id ++ " misses a required predecessor"
             , suggestion := "insert the required pre-operators of " ++ o.id }
      else if o.forbiddenPreOps.any (fun p => prev.contains p) then
        some { sev := .REJECT, code := .E_UNSATISFIABLE_CONTRACT
             , detail := o.id ++ " has a forbidden predecessor"
             , suggestion := "" }
      else contractDiag reg (g ++ o.post) (s ++ o.sideFacts) (prev ++ [o.id]) rest
    else if subsetOf o.pre (g ++ s) then
      some { sev := .REJECT, code := .E_CONTRACT_LEAKAGE
           , detail := "precondition of " ++ o.id ++
               " is met only by a non-guaranteed side effect"
           , suggestion := "" }
    else
      match reg.find? (fun c =>
          (o.pre.filter (fun f => !g.contains f)).all (fun f => c.post.contains f)) with
      | some c =>
          some { sev := .REPAIR, code := .E_NOT_YET_SATISFIED
               , detail := "preconditions of " ++ o.id ++ " are not established"
               , suggestion := "insert " ++ c.id ++ " before " ++ o.id }
      | none =>
          some { sev := .REJECT, code := .E_UNSATISFIABLE_CONTRACT
               , detail := "preconditions of " ++ o.id ++ " cannot be established"
               , suggestion := "" }

/-- `RULE 3` + `RULE 4`: инвариантная безопасность и политика эффектов.
`inv` — множество инвариантов, действующих в данный момент, `tok` —
получен ли токен авторизации, `apr` — получено ли подтверждение. -/
def effectDiag (reg : List Operator) :
    List Invariant → Bool → Bool → Bool → List Operator → Option Failure
  | _, _, _, _, [] => none
  | inv, tok, htok, apr, o :: rest =>
    if !subsetOf o.producedEffects o.allowedEffects then
      some { sev := .REJECT, code := .E_EFFECT_LEAKAGE
           , detail := o.id ++ " produces an effect outside allowed_effects"
           , suggestion := "" }
    else if o.producedEffects.any (fun e => o.forbiddenEffects.contains e) then
      some { sev := .REJECT, code := .E_EFFECT_LEAKAGE
           , detail := o.id ++ " produces a forbidden effect"
           , suggestion := "" }
    else if !subsetOf o.requiresInv inv then
      some { sev := .REJECT, code := .E_INVARIANT_VIOLATION
           , detail := o.id ++ " requires an invariant destroyed earlier"
           , suggestion := "" }
    else if o.effectLevel == EffectLevel.E4 && o.requiresAuthorization &&
        !(tok && (!o.humanAuthorizationRequired || htok)) then
      match reg.find? (fun c => o.authorizes c) with
      | some c =>
          some { sev := .REPAIR, code := .E_EFFECT_POLICY_VIOLATION
               , detail := o.id ++ " is E4 and requires authorization"
               , suggestion := "insert " ++ c.id ++ " before " ++ o.id }
      | none =>
          some { sev := .REJECT, code := .E_EFFECT_POLICY_VIOLATION
               , detail := o.id ++ " is E4 and requires authorization"
               , suggestion := "" }
    else if o.effectLevel == EffectLevel.E3 && !apr then
      match reg.find? (fun c => c.isApprover) with
      | some c =>
          some { sev := .REPAIR, code := .E_EFFECT_POLICY_VIOLATION
               , detail := o.id ++ " is E3 and requires approval"
               , suggestion := "insert " ++ c.id ++ " before " ++ o.id }
      | none =>
          some { sev := .REJECT, code := .E_EFFECT_POLICY_VIOLATION
               , detail := o.id ++ " is E3 and requires approval"
               , suggestion := "" }
    else if inv.any (fun i => !o.preserves.contains i && !o.destroys.contains i) then
      some { sev := .REPAIR, code := .E_INVARIANT_LOSS
           , detail := o.id ++ " neither preserves nor destroys an active invariant"
           , suggestion := "declare the invariant in preserves of " ++ o.id }
    else
      effectDiag reg (inv.filter (fun i => !o.destroys.contains i))
        (tok || o.isAuthorizer) (htok || o.grantsHumanAuthorization)
        (apr || o.isApprover) rest

/-- Инварианты, действующие после выполнения цепочки. -/
def finalInvariants : List Invariant → List Operator → List Invariant
  | inv, [] => inv
  | inv, o :: rest =>
      finalInvariants (inv.filter (fun i => !o.destroys.contains i)) rest

/-- §11.D: глобальная проверка — требуемые инварианты композиции должны
сохраниться к концу цепочки. -/
def globalInvariantDiag (c : Composition) : Option Failure :=
  if subsetOf c.requiredFinalInvariants (finalInvariants c.initialInvariants c.ops) then
    none
  else
    some { sev := .REJECT, code := .E_INVARIANT_VIOLATION
         , detail := "the composition as a whole destroys a required invariant"
         , suggestion := "" }

/-- Агрегация неопределённости по цепочке согласно выбранному правилу. -/
def aggregate (r : AggRule) : Uncert → List Operator → Uncert
  | u, [] => u
  | u, o :: rest =>
    let step :=
      match r with
      | .additive => u.add o.uncertainty
      | .maximum => u.max o.uncertainty
    aggregate r (step.sub o.reduction) rest

/-- `RULE 5`: эпистемическая обоснованность. -/
def uncertaintyDiag (reg : List Operator) (c : Composition) : Option Failure :=
  match c.ops.getLast? with
  | none => none
  | some last =>
    match c.agg with
    | none =>
        some { sev := .SPEC_GAP, code := .UNCERTAINTY_RULE_NOT_DEFINED
             , detail := "no aggregation rule is defined for this composition"
             , suggestion := "declare the aggregation rule of the composition" }
    | some r =>
      match c.declaredThreshold.orElse
          (fun _ => thresholdFor last.outputType last.reversibility) with
      | none =>
          some { sev := .SPEC_GAP, code := .SPEC_GAP_UNDEFINED_THRESHOLD
               , detail := "OSA-3.2 defines no decision threshold for this output level"
               , suggestion := "" }
      | some thr =>
        let u := aggregate r Uncert.zero c.ops
        if u.peak ≤ thr && u.total ≤ thr then none
        else
          match reg.find? (fun x => x.reduces &&
              (u.sub x.reduction).peak ≤ thr && (u.sub x.reduction).total ≤ thr) with
          | some x =>
              some { sev := .REPAIR, code := .E_EPISTEMIC_INSUFFICIENT
                   , detail := "accumulated uncertainty exceeds the target threshold"
                   , suggestion := "insert " ++ x.id ++ " to reduce uncertainty" }
          | none =>
              some { sev := .REJECT, code := .E_EPISTEMIC_INSUFFICIENT
                   , detail := "accumulated uncertainty exceeds the target threshold"
                   , suggestion := "" }

/-! ## §9. Компиляция и вердикт -/

/-- Уровень L1 спецификации: типовая корректность. -/
def diagL1 (reg : List Operator) (c : Composition) : Option Failure :=
  typeDiag reg c.initialType c.ops

/-- Уровень L2: контрактная корректность. -/
def diagL2 (reg : List Operator) (c : Composition) : Option Failure :=
  contractDiag reg c.initialFacts [] [] c.ops

/-- Уровень L3: безопасность эффектов и инвариантов (локальная и
глобальная части). -/
def diagL3 (reg : List Operator) (c : Composition) : Option Failure :=
  (effectDiag reg c.initialInvariants false false false c.ops).orElse
    (fun _ => globalInvariantDiag c)

/-- Уровень L4: эпистемическая обоснованность. -/
def diagL4 (reg : List Operator) (c : Composition) : Option Failure :=
  uncertaintyDiag reg c

/-- Отчёт компилятора (§9). -/
structure Report where
  caseId : String
  proposed : List String
  l1 : Bool
  l2 : Bool
  l3 : Bool
  l4 : Bool
  status : Status
  code : ErrCode
  detail : String
  suggestion : String
  deriving Repr, Inhabited

/-- Первое нарушение в порядке L1 → L2 → L3 → L4. -/
def firstFailure (reg : List Operator) (c : Composition) : Option Failure :=
  ((diagL1 reg c).orElse (fun _ => diagL2 reg c)).orElse
    (fun _ => (diagL3 reg c).orElse (fun _ => diagL4 reg c))

/-- Компилятор OSA-3.2: по реестру операторов и предложенной композиции
возвращает отчёт §9. -/
def compile (reg : List Operator) (c : Composition) : Report :=
  { caseId := c.caseId
  , proposed := c.ops.map (·.id)
  , l1 := (diagL1 reg c).isNone
  , l2 := (diagL2 reg c).isNone
  , l3 := (diagL3 reg c).isNone
  , l4 := (diagL4 reg c).isNone
  , status := match firstFailure reg c with
      | none => .PASS
      | some f => Status.escalate c.repairPolicy f.sev.toStatus
  , code := match firstFailure reg c with
      | none => .NONE
      | some f => f.code
  , detail := match firstFailure reg c with
      | none => "all four levels pass"
      | some f => f.detail
  , suggestion := match firstFailure reg c with
      | none => ""
      | some f => f.suggestion }

/-! ## Отрисовка отчёта в формате §9 -/

private def flag (b : Bool) : String := if b then "PASS" else "FAIL"

/-- Имя вердикта §9. -/
def Status.toStatusString : Status → String
  | .PASS => "PASS" | .REPAIR => "REPAIR" | .REJECT => "REJECT"
  | .SPEC_GAP => "SPEC_GAP"

/-- Имя кода ошибки §8. -/
def ErrCode.toCodeString : ErrCode → String
  | .NONE => "NONE"
  | .E_TYPE_MISMATCH => "E_TYPE_MISMATCH"
  | .E_INVARIANT_VIOLATION => "E_INVARIANT_VIOLATION"
  | .E_EFFECT_POLICY_VIOLATION => "E_EFFECT_POLICY_VIOLATION"
  | .E_EPISTEMIC_INSUFFICIENT => "E_EPISTEMIC_INSUFFICIENT"
  | .E_CONTRACT_LEAKAGE => "E_CONTRACT_LEAKAGE"
  | .E_LEVEL_JUMP => "E_LEVEL_JUMP"
  | .E_EFFECT_LEAKAGE => "E_EFFECT_LEAKAGE"
  | .E_MISSING_CONVERSION => "E_MISSING_CONVERSION"
  | .E_NOT_YET_SATISFIED => "E_NOT_YET_SATISFIED"
  | .E_UNSATISFIABLE_CONTRACT => "E_UNSATISFIABLE_CONTRACT"
  | .E_INVARIANT_LOSS => "E_INVARIANT_LOSS"
  | .UNCERTAINTY_RULE_NOT_DEFINED => "UNCERTAINTY_RULE_NOT_DEFINED"
  | .SPEC_GAP_UNDEFINED_THRESHOLD => "SPEC_GAP_UNDEFINED_THRESHOLD"

/-- Текстовый вывод отчёта в формате §9. -/
def Report.render (r : Report) : String :=
  "┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐\n" ++
  "│ CASE: " ++ r.caseId ++ "\n" ++
  "│ PROPOSED: " ++ String.intercalate " → " r.proposed ++ "\n" ++
  "├─────────────────────────────────────────────────┤\n" ++
  "│ L1 TYPE-CORRECT:        " ++ flag r.l1 ++ "\n" ++
  "│ L2 CONTRACT-CORRECT:    " ++ flag r.l2 ++ "\n" ++
  "│ L3 EFFECT-SAFE:         " ++ flag r.l3 ++ "\n" ++
  "│ L4 EPISTEMIC-JUSTIFIED: " ++ flag r.l4 ++ "\n" ++
  "├─────────────────────────────────────────────────┤\n" ++
  "│ VERDICT: " ++ r.status.toStatusString ++ "\n" ++
  "│ ERROR_CODE: " ++ r.code.toCodeString ++ "\n" ++
  "├─────────────────────────────────────────────────┤\n" ++
  "│ DETAILED ANALYSIS: " ++ r.detail ++ "\n" ++
  (if r.suggestion == "" then "" else "│ REPAIR SUGGESTION: " ++ r.suggestion ++ "\n") ++
  "└─────────────────────────────────────────────────┘"

end Polymath.OSA
