/-
# OSA-3.2 — реестр операторов и разобранные кейсы

Модуль содержит:

* каталог операторов (`stdRegistry`) в схеме §2: MEASURE, CALIBRATE, MODEL,
  SIMULATE, VALIDATE, VERIFY, DECIDE, AUTHORIZE, EXECUTE, ANALYZE и др.;
* набор предложенных композиций (кейсов), включая примеры, явно названные
  в спецификации: канонический путь §3, `DECIDE → EXECUTE` без AUTHORIZE (§6),
  `DELETE → ANALYZE` (§7 RULE 3), `EXPERIMENT → AXIOMATIZE` (§7 RULE 2B),
  прыжок через уровни (§7 RULE 6);
* вердикты компилятора для каждого кейса — **доказанные** вычислением
  (`by decide`), а не заявленные.

Все `#eval` печатают отчёт в формате §9.
-/
import RequestProject.OSA.Theorems

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

/-! ## Каталог операторов -/

/-- Полный список инвариантов (используется как значение `preserves` для
операторов, которые ничего не разрушают). -/
def allInvariants : List Invariant :=
  [.DataExistence, .Traceability, .Consistency, .PhysicalIntegrity, .ReversibilityMargin]

/-- Нейтральная заготовка оператора; конкретные операторы задаются как
`{ baseOp with … }`. -/
def baseOp : Operator where
  id := ""
  level := .L2
  inputType := .Model
  outputType := .Model
  pre := []
  post := []
  sideFacts := []
  requiresInv := []
  preserves := allInvariants
  destroys := []
  effectLevel := .E0
  producedEffects := []
  allowedEffects := []
  forbiddenEffects := []
  uncertainty := Uncert.zero
  reduction := Uncert.zero
  reversibility := .reversible
  requiresAuthorization := false
  humanAuthorizationRequired := false
  grantsHumanAuthorization := false
  requiredPreOps := []
  forbiddenPreOps := []

/-- MEASURE: L0 → L1, регистрация физического состояния. -/
def MEASURE : Operator :=
  { baseOp with
    id := "MEASURE", level := .L1
    inputType := .ObjectState, outputType := .MeasuredValue
    pre := [.RawDataAvailable], post := [.Measured]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite]
    uncertainty := ⟨3, 0, 0, 1⟩ }

/-- CALIBRATE: снижает алеаторную и провенансную неопределённость. -/
def CALIBRATE : Operator :=
  { baseOp with
    id := "CALIBRATE", level := .L1
    inputType := .MeasuredValue, outputType := .CalibratedValue
    pre := [.Measured], post := [.Calibrated]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite]
    reduction := ⟨1, 0, 0, 1⟩ }

/-- MODEL: L1 → L2, построение энергетической модели. -/
def MODEL : Operator :=
  { baseOp with
    id := "MODEL", level := .L2
    inputType := .MeasuredValue, outputType := .EnergyModel
    pre := [.Measured], post := [.Modeled]
    requiresInv := [.DataExistence]
    effectLevel := .E2
    producedEffects := [.ResourceBurn, .InformationWrite]
    allowedEffects := [.ResourceBurn, .InformationWrite]
    uncertainty := ⟨0, 4, 3, 0⟩ }

/-- SIMULATE: увеличивает model-компоненту неопределённости (§5). -/
def SIMULATE : Operator :=
  { baseOp with
    id := "SIMULATE", level := .L2
    inputType := .EnergyModel, outputType := .SimulationResult
    pre := [.Modeled], post := [.Simulated]
    requiresInv := [.DataExistence]
    effectLevel := .E2
    producedEffects := [.ResourceBurn], allowedEffects := [.ResourceBurn]
    uncertainty := ⟨0, 0, 12, 0⟩ }

/-- VALIDATE: выдаёт `ValidationResult` (тип L2, НЕ решение, §6). -/
def VALIDATE : Operator :=
  { baseOp with
    id := "VALIDATE", level := .L2
    inputType := .Model, outputType := .ValidationResult
    pre := [.Modeled], post := [.Validated, .EvidenceAvailable]
    requiresInv := [.DataExistence]
    effectLevel := .E2
    producedEffects := [.ResourceBurn], allowedEffects := [.ResourceBurn]
    reduction := ⟨0, 3, 2, 0⟩ }

/-- VERIFY: формальная проверка, выдаёт `VerificationResult` (§6). -/
def VERIFY : Operator :=
  { baseOp with
    id := "VERIFY", level := .L2
    inputType := .Model, outputType := .VerificationResult
    pre := [.Modeled], post := [.Verified]
    requiresInv := [.DataExistence]
    effectLevel := .E2
    producedEffects := [.ResourceBurn], allowedEffects := [.ResourceBurn]
    reduction := ⟨0, 1, 1, 0⟩ }

/-- DECIDE: выбор альтернативы; НЕ даёт полномочий на исполнение (§6). -/
def DECIDE : Operator :=
  { baseOp with
    id := "DECIDE", level := .L3
    inputType := .ValidationResult, outputType := .Plan
    pre := [.EvidenceAvailable], post := [.PlanSelected]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite]
    uncertainty := ⟨0, 1, 0, 0⟩ }

/-- AUTHORIZE: выдаёт `AuthorizationToken`; не исполняет действие (§6). -/
def AUTHORIZE : Operator :=
  { baseOp with
    id := "AUTHORIZE", level := .L3
    inputType := .Plan, outputType := .AuthorizationToken
    pre := [.PlanSelected], post := [.Authorized, .Approved]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite] }

/-- EXECUTE: внешнее исполнение по токену авторизации (§6). -/
def EXECUTE : Operator :=
  { baseOp with
    id := "EXECUTE", level := .L4
    inputType := .AuthorizationToken, outputType := .SystemStateChange
    pre := [.Authorized], post := [.Executed]
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

/-- EXECUTE_PLAN: ошибочный оператор, принимающий `Plan` напрямую —
исполнение без авторизации (иллюстрация §6). -/
def EXECUTE_PLAN : Operator :=
  { EXECUTE with
    id := "EXECUTE_PLAN"
    inputType := .Plan
    pre := [.PlanSelected]
    requiredPreOps := [] }

/-- EXECUTE_IRREVERSIBLE: необратимое внешнее воздействие (порог 0.05). -/
def EXECUTE_IRREVERSIBLE : Operator :=
  { EXECUTE with
    id := "EXECUTE_IRREVERSIBLE"
    outputType := .IrreversibleChange
    reversibility := .irreversible }

/-- DELETE: уничтожает инвариант `DataExistence`. -/
def DELETE : Operator :=
  { baseOp with
    id := "DELETE", level := .L1
    inputType := .MeasuredValue, outputType := .RegisteredEvent
    requiresInv := [.DataExistence]
    preserves := [.Traceability, .Consistency, .PhysicalIntegrity, .ReversibilityMargin]
    destroys := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.DataDeletion], allowedEffects := [.DataDeletion] }

/-- ANALYZE: требует инвариант `DataExistence`. -/
def ANALYZE : Operator :=
  { baseOp with
    id := "ANALYZE", level := .L2
    inputType := .RegisteredEvent, outputType := .Model
    pre := [.Measured], post := [.Modeled]
    requiresInv := [.DataExistence]
    effectLevel := .E2
    producedEffects := [.ResourceBurn], allowedEffects := [.ResourceBurn]
    uncertainty := ⟨0, 4, 3, 0⟩ }

/-- EXPERIMENT: успешная валидация — его *негарантированный* побочный исход
(`sideFacts`), а не постусловие (§7 RULE 2B). -/
def EXPERIMENT : Operator :=
  { baseOp with
    id := "EXPERIMENT", level := .L2
    inputType := .EnergyModel, outputType := .SimulationResult
    pre := [.Modeled], post := [.ExperimentRun], sideFacts := [.Validated]
    requiresInv := [.DataExistence]
    effectLevel := .E2
    producedEffects := [.ResourceBurn], allowedEffects := [.ResourceBurn]
    uncertainty := ⟨0, 0, 4, 0⟩ }

/-- AXIOMATIZE: требует подтверждённой валидации. -/
def AXIOMATIZE : Operator :=
  { baseOp with
    id := "AXIOMATIZE", level := .L2
    inputType := .Model, outputType := .FormalDescription
    pre := [.Validated], post := [.Verified]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite] }

/-- CERTIFY: требует формальной верификации. -/
def CERTIFY : Operator :=
  { baseOp with
    id := "CERTIFY", level := .L2
    inputType := .Model, outputType := .Specification
    pre := [.Verified], post := [.Validated]
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.InformationWrite], allowedEffects := [.InformationWrite] }

/-- SILENT_WRITE: порождает эффект, не разрешённый его контрактом
(§7 RULE 4C). -/
def SILENT_WRITE : Operator :=
  { baseOp with
    id := "SILENT_WRITE", level := .L1
    inputType := .MeasuredValue, outputType := .RegisteredEvent
    requiresInv := [.DataExistence]
    effectLevel := .E1
    producedEffects := [.ExternalIrreversible], allowedEffects := [.InformationWrite] }

/-- Каталог операторов, доступных компилятору для предложения починок. -/
def stdRegistry : List Operator :=
  [MEASURE, CALIBRATE, MODEL, SIMULATE, VALIDATE, VERIFY, DECIDE, AUTHORIZE,
   EXECUTE, ANALYZE]

/-- Каталог без оператора MODEL: показывает разницу между
`E_MISSING_CONVERSION` (посредник существует) и `E_TYPE_MISMATCH`
(посредника нет) — §10.9. -/
def registryNoModel : List Operator :=
  [MEASURE, CALIBRATE, SIMULATE, VALIDATE, DECIDE, AUTHORIZE, EXECUTE, ANALYZE]

/-- Каталог без оператора VERIFY: недостающую прекондицию нечем установить. -/
def registryNoVerify : List Operator :=
  [MEASURE, CALIBRATE, MODEL, SIMULATE, VALIDATE, DECIDE, AUTHORIZE, EXECUTE, ANALYZE]

/-! ## Кейсы -/

/-- Заготовка композиции: физический объект на входе, данные существуют,
трассируемость и целостность данных обязаны сохраниться. -/
def baseCase : Composition where
  caseId := ""
  initialType := .ObjectState
  initialFacts := [.RawDataAvailable]
  initialInvariants := [.DataExistence, .Traceability, .Consistency]
  requiredFinalInvariants := [.DataExistence, .Traceability]
  ops := []
  agg := some .additive
  declaredThreshold := none
  repairPolicy := .allow

/-- Канонический путь §3. -/
def caseGolden : Composition :=
  { baseCase with
    caseId := "GOLDEN: canonical path of §3"
    ops := [MEASURE, CALIBRATE, MODEL, VALIDATE, DECIDE, AUTHORIZE, EXECUTE] }

/-- DECIDE → EXECUTE без AUTHORIZE (§6). -/
def caseDecideExecute : Composition :=
  { baseCase with
    caseId := "DECIDE -> EXECUTE without AUTHORIZE"
    ops := [MEASURE, CALIBRATE, MODEL, VALIDATE, DECIDE, EXECUTE_PLAN] }

/-- DELETE → ANALYZE (§7 RULE 3). -/
def caseDeleteAnalyze : Composition :=
  { baseCase with
    caseId := "DELETE -> ANALYZE"
    ops := [MEASURE, DELETE, ANALYZE] }

/-- EXPERIMENT → AXIOMATIZE (§7 RULE 2B). -/
def caseContractLeakage : Composition :=
  { baseCase with
    caseId := "EXPERIMENT -> AXIOMATIZE"
    ops := [MEASURE, MODEL, EXPERIMENT, AXIOMATIZE] }

/-- L1_MeasuredValue → EXECUTE: прыжок через уровни (§7 RULE 6). -/
def caseLevelJump : Composition :=
  { baseCase with
    caseId := "MEASURE -> EXECUTE (level jump)"
    ops := [MEASURE, EXECUTE] }

/-- MEASURE → VALIDATE: нужен посредник MODEL. -/
def caseMissingConversion : Composition :=
  { baseCase with
    caseId := "MEASURE -> VALIDATE (missing conversion)"
    ops := [MEASURE, VALIDATE] }

/-- MODEL без предшествующего MEASURE: прекондиция пока не установлена. -/
def caseNotYetSatisfied : Composition :=
  { baseCase with
    caseId := "MODEL without MEASURE"
    initialType := .MeasuredValue
    initialFacts := []
    ops := [ MODEL ] }

/-- CERTIFY требует `Verified`; в каталоге без VERIFY это неустранимо. -/
def caseUnsatisfiable : Composition :=
  { baseCase with
    caseId := "CERTIFY with no verifier available"
    ops := [MEASURE, MODEL, CERTIFY] }

/-- Оператор порождает эффект вне своего контракта (§7 RULE 4C). -/
def caseEffectLeakage : Composition :=
  { baseCase with
    caseId := "SILENT_WRITE (effect leakage)"
    ops := [MEASURE, SILENT_WRITE] }

/-- Канонический путь без объявленного правила агрегации (§11.C). -/
def caseNoAggRule : Composition :=
  { caseGolden with
    caseId := "GOLDEN without an aggregation rule"
    agg := none }

/-- Необратимое исполнение: порог 0.05 не выдержан. -/
def caseIrreversible : Composition :=
  { baseCase with
    caseId := "irreversible execution"
    ops := [MEASURE, CALIBRATE, MODEL, VALIDATE, DECIDE, AUTHORIZE, EXECUTE_IRREVERSIBLE] }

/-- SIMULATE увеличивает model-компоненту; порог L3 = 0.15 превышен. -/
def caseEpistemic : Composition :=
  { baseCase with
    caseId := "SIMULATE -> ... -> DECIDE (epistemic budget)"
    ops := [MEASURE, MODEL, SIMULATE, VALIDATE, DECIDE] }

/-- Локально всё корректно, но композиция в целом разрушает требуемый
инвариант (§11.D). -/
def caseGlobalInvariant : Composition :=
  { baseCase with
    caseId := "MEASURE -> DELETE (global invariant)"
    requiredFinalInvariants := [.DataExistence]
    ops := [MEASURE, DELETE] }

/-- Выход уровня L1: порог принятия решения спецификацией не определён
(§10.8). -/
def caseSpecGapThreshold : Composition :=
  { baseCase with
    caseId := "MEASURE alone (no threshold for an L1 output)"
    ops := [MEASURE] }

/-! ## Вердикты (доказаны вычислением) -/

/-- Канонический путь §3 проходит все четыре уровня. -/
theorem caseGolden_pass :
    (compile stdRegistry caseGolden).status = Status.PASS ∧
    (compile stdRegistry caseGolden).code = ErrCode.NONE := by decide

/-- Все четыре уровня канонического пути отмечены как пройденные. -/
theorem caseGolden_levels :
    (compile stdRegistry caseGolden).l1 = true ∧
    (compile stdRegistry caseGolden).l2 = true ∧
    (compile stdRegistry caseGolden).l3 = true ∧
    (compile stdRegistry caseGolden).l4 = true := by decide

/-- `DECIDE → EXECUTE` без AUTHORIZE: нарушение политики эффектов; починка —
вставка AUTHORIZE (§6, §7 RULE 4A). -/
theorem caseDecideExecute_repair :
    (compile stdRegistry caseDecideExecute).status = Status.REPAIR ∧
    (compile stdRegistry caseDecideExecute).code = ErrCode.E_EFFECT_POLICY_VIOLATION ∧
    (compile stdRegistry caseDecideExecute).l1 = true ∧
    (compile stdRegistry caseDecideExecute).l3 = false := by decide

/-- Предложенная починка действительно работает: канонический путь с
AUTHORIZE получает `PASS` (точность починки, §12). -/
theorem repair_of_decideExecute_passes :
    (compile stdRegistry caseGolden).status = Status.PASS := by decide

/-- `DELETE → ANALYZE`: фатальное нарушение инварианта (§7 RULE 3). -/
theorem caseDeleteAnalyze_reject :
    (compile stdRegistry caseDeleteAnalyze).status = Status.REJECT ∧
    (compile stdRegistry caseDeleteAnalyze).code = ErrCode.E_INVARIANT_VIOLATION := by
  decide

/-- `EXPERIMENT → AXIOMATIZE`: прекондиция удовлетворена лишь негарантированным
побочным исходом (§7 RULE 2B). -/
theorem caseContractLeakage_reject :
    (compile stdRegistry caseContractLeakage).status = Status.REJECT ∧
    (compile stdRegistry caseContractLeakage).code = ErrCode.E_CONTRACT_LEAKAGE := by
  decide

/-- Прыжок L1 → L3 (§7 RULE 6). -/
theorem caseLevelJump_reject :
    (compile stdRegistry caseLevelJump).status = Status.REJECT ∧
    (compile stdRegistry caseLevelJump).code = ErrCode.E_LEVEL_JUMP := by decide

/-- Недостающая конверсия: посредник существует, статус REPAIR (§10.9). -/
theorem caseMissingConversion_repair :
    (compile stdRegistry caseMissingConversion).status = Status.REPAIR ∧
    (compile stdRegistry caseMissingConversion).code = ErrCode.E_MISSING_CONVERSION := by
  decide

/-- Та же композиция без подходящего оператора в каталоге — уже
`E_TYPE_MISMATCH` (REJECT).  Это и есть различение §10.9. -/
theorem caseMissingConversion_becomes_mismatch :
    (compile registryNoModel caseMissingConversion).status = Status.REJECT ∧
    (compile registryNoModel caseMissingConversion).code = ErrCode.E_TYPE_MISMATCH := by
  decide

/-- Прекондиция ещё не установлена, но её можно установить (§7 RULE 2). -/
theorem caseNotYetSatisfied_repair :
    (compile stdRegistry caseNotYetSatisfied).status = Status.REPAIR ∧
    (compile stdRegistry caseNotYetSatisfied).code = ErrCode.E_NOT_YET_SATISFIED := by
  decide

/-- Прекондицию нечем установить: контракт неудовлетворим. -/
theorem caseUnsatisfiable_reject :
    (compile registryNoVerify caseUnsatisfiable).status = Status.REJECT ∧
    (compile registryNoVerify caseUnsatisfiable).code = ErrCode.E_UNSATISFIABLE_CONTRACT := by
  decide

/-- Тот же кейс с доступным VERIFY — устранимая ошибка (REPAIR). -/
theorem caseUnsatisfiable_repairable_with_verify :
    (compile stdRegistry caseUnsatisfiable).status = Status.REPAIR ∧
    (compile stdRegistry caseUnsatisfiable).code = ErrCode.E_NOT_YET_SATISFIED := by
  decide

/-- Утечка эффекта (§7 RULE 4C). -/
theorem caseEffectLeakage_reject :
    (compile stdRegistry caseEffectLeakage).status = Status.REJECT ∧
    (compile stdRegistry caseEffectLeakage).code = ErrCode.E_EFFECT_LEAKAGE := by decide

/-- Без объявленного правила агрегации компилятор не подставляет формулу,
а фиксирует пробел спецификации (§11.C). -/
theorem caseNoAggRule_specGap :
    (compile stdRegistry caseNoAggRule).status = Status.SPEC_GAP ∧
    (compile stdRegistry caseNoAggRule).code = ErrCode.UNCERTAINTY_RULE_NOT_DEFINED := by
  decide

/-- Необратимое действие требует порога 0.05; накопленной точности не хватает
(§5, §7 RULE 5). -/
theorem caseIrreversible_repair :
    (compile stdRegistry caseIrreversible).status = Status.REPAIR ∧
    (compile stdRegistry caseIrreversible).code = ErrCode.E_EPISTEMIC_INSUFFICIENT ∧
    (compile stdRegistry caseIrreversible).l1 = true ∧
    (compile stdRegistry caseIrreversible).l2 = true ∧
    (compile stdRegistry caseIrreversible).l3 = true ∧
    (compile stdRegistry caseIrreversible).l4 = false := by decide

/-- Та же цепочка, но обратимое исполнение (порог 0.10) — `PASS`.
Это и есть чувствительность порога к уровню действия. -/
theorem threshold_depends_on_reversibility :
    (compile stdRegistry caseGolden).status = Status.PASS ∧
    (compile stdRegistry caseIrreversible).status = Status.REPAIR := by decide

/-- Правило тренда §5: SIMULATE наращивает model-компоненту, и к уровню
решения порог 0.15 оказывается превышен. -/
theorem caseEpistemic_repair :
    (compile stdRegistry caseEpistemic).status = Status.REPAIR ∧
    (compile stdRegistry caseEpistemic).code = ErrCode.E_EPISTEMIC_INSUFFICIENT := by
  decide

/-- Глобальная проверка §11.D: локально корректная цепочка отвергается,
потому что композиция в целом уничтожает требуемый инвариант. -/
theorem caseGlobalInvariant_reject :
    (compile stdRegistry caseGlobalInvariant).status = Status.REJECT ∧
    (compile stdRegistry caseGlobalInvariant).code = ErrCode.E_INVARIANT_VIOLATION := by
  decide

/-- Для выхода уровня L1 спецификация не задаёт порога — объявляется
SPEC_GAP, а не вывод «по аналогии» (§10.8). -/
theorem caseSpecGapThreshold_specGap :
    (compile stdRegistry caseSpecGapThreshold).status = Status.SPEC_GAP ∧
    (compile stdRegistry caseSpecGapThreshold).code =
      ErrCode.SPEC_GAP_UNDEFINED_THRESHOLD := by decide

/-! ## Нетривиальность компилятора (§11.A, «paranoia trap») -/

/-- Компилятор не является ни тривиально принимающим, ни тривиально
отвергающим: существуют композиции с вердиктами PASS, REPAIR и REJECT. -/
theorem compiler_not_trivial :
    (∃ x : Composition, (compile stdRegistry x).status = Status.PASS) ∧
    (∃ x : Composition, (compile stdRegistry x).status = Status.REPAIR) ∧
    (∃ x : Composition, (compile stdRegistry x).status = Status.REJECT) ∧
    (∃ x : Composition, (compile stdRegistry x).status = Status.SPEC_GAP) :=
  ⟨⟨caseGolden, by decide⟩, ⟨caseDecideExecute, by decide⟩,
   ⟨caseDeleteAnalyze, by decide⟩, ⟨caseNoAggRule, by decide⟩⟩

/-! ## Печать отчётов в формате §9 -/

/-- Все разобранные кейсы. -/
def allCases : List (List Operator × Composition) :=
  [ (stdRegistry, caseGolden)
  , (stdRegistry, caseDecideExecute)
  , (stdRegistry, caseDeleteAnalyze)
  , (stdRegistry, caseContractLeakage)
  , (stdRegistry, caseLevelJump)
  , (stdRegistry, caseMissingConversion)
  , (registryNoModel, caseMissingConversion)
  , (stdRegistry, caseNotYetSatisfied)
  , (registryNoVerify, caseUnsatisfiable)
  , (stdRegistry, caseEffectLeakage)
  , (stdRegistry, caseNoAggRule)
  , (stdRegistry, caseIrreversible)
  , (stdRegistry, caseEpistemic)
  , (stdRegistry, caseGlobalInvariant)
  , (stdRegistry, caseSpecGapThreshold) ]

/-- Отчёты §9 по всем кейсам. -/
def allReports : String :=
  String.intercalate "\n\n" (allCases.map (fun p => (compile p.1 p.2).render))

#eval IO.println allReports

end Polymath.OSA
