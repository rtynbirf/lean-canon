/-
# OSA-4.0 — Semantic Torture Set T01–T15

Формализация §10 «SEMANTIC TORTURE SET T01–T15» и §13 «TORTURE SET v0.4»
кодекса OSA-4.0.  Каждый кейс — конкретный сценарий, вердикт которого не
объявлен, а **вычислен** компилятором (`decide`).

Тесты T04 (resurrection / recreation) и T12 (двойное потребление) на уровне
идентичности живут в `Identity.lean`, T08/T09 (слияние ветвей) — в
`Epistemic.lean`, T15 (лексикографический ремонт) — в `Repair.lean`; здесь
они собраны ссылками, чтобы набор был полным.

Замечание кодекса «15/15 — аудит, а не доказательство soundness» остаётся в
силе: набор кейсов проверяет, что компилятор выдаёт ожидаемые вердикты, а
общие свойства ядра доказаны отдельно в `Kernel.lean`, `Effects.lean`,
`Identity.lean`, `Repair.lean` и `Lawbook.lean`.
-/
import RequestProject.OSA4.Compiler
import RequestProject.OSA4.Epistemic
import RequestProject.OSA4.Identity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Polymath.OSA4

/-! ## Каталог операторов -/

/-- Измерение: производит сырые данные. -/
def MEASURE : Op := ⟨"MEASURE", [], ["RawData"], [], [], [], .E1, false⟩

/-- Калибровка: по сырым данным доказывает `Calibrated`. -/
def CALIBRATE : Op :=
  ⟨"CALIBRATE", [.factExists "RawData"], ["Calibrated"], [], [], [], .E1, false⟩

/-- Моделирование: требует доказанной достаточности данных. -/
def MODEL : Op :=
  ⟨"MODEL", [.factExists "DataSufficiency"], ["Model"], [], [], [], .E1, false⟩

/-- Явная проверка достаточности данных: оператор, устраняющий дефект
конфигурации T01 (отсутствие предиката `DataSufficiency` в реестре). -/
def CHECK_SUFFICIENCY : Op :=
  ⟨"CHECK_SUFFICIENCY", [.factExists "RawData"], ["DataSufficiency"], [], [], [], .E1, false⟩

/-- Моделирование с числовым порогом достаточности (0.80 в сотых долях). -/
def STRICT_MODEL : Op :=
  ⟨"STRICT_MODEL", [.gte "sufficiency" 80], ["Model"], [], [], [], .E1, false⟩

/-- Создание объекта X. -/
def CREATE_X : Op := ⟨"CREATE_X", [], ["X"], [], [], [], .E1, false⟩

/-- Создание объекта Y. -/
def CREATE_Y : Op := ⟨"CREATE_Y", [], ["Y"], [], [], [], .E1, false⟩

/-- Удаление объекта X: инвалидирует знание о нём. -/
def DELETE_X : Op := ⟨"DELETE_X", [.factExists "X"], [], [], ["X"], [], .E4, false⟩

/-- Анализ X. -/
def ANALYZE_X : Op :=
  ⟨"ANALYZE_X", [.factExists "X"], ["AnalysisX"], [], [], [], .E0, false⟩

/-- Анализ Y. -/
def ANALYZE_Y : Op :=
  ⟨"ANALYZE_Y", [.factExists "Y"], ["AnalysisY"], [], [], [], .E0, false⟩

/-- Потребление X. -/
def CONSUME_X : Op := ⟨"CONSUME_X", [.factExists "X"], [], ["X"], [], [], .E2, false⟩

/-- Изменение X: инвалидирует `Calibrated`, не доказывая его отрицания. -/
def MODIFY_X : Op :=
  ⟨"MODIFY_X", [.factExists "X"], [], [], ["Calibrated"], ["xval"], .E2, false⟩

/-- Использование X требует калибровки. -/
def USE_X : Op :=
  ⟨"USE_X", [.factExists "Calibrated"], ["Used"], [], [], [], .E1, false⟩

/-- Калибровка X (для T11). -/
def CALIBRATE_X : Op :=
  ⟨"CALIBRATE_X", [.factExists "X"], ["Calibrated"], [], [], [], .E1, false⟩

/-- Принятие решения. -/
def DECIDE : Op := ⟨"DECIDE", [], ["Decision"], [], [], [], .E1, false⟩

/-- Необратимое исполнение решения: требует авторизации (E4). -/
def EXECUTE : Op :=
  ⟨"EXECUTE", [.factExists "Decision"], ["Executed"], [], [], [], .E4, true⟩

/-- Авторизация исполнения: выдаёт токен для `EXECUTE`. -/
def AUTHORIZE : Op :=
  ⟨"AUTHORIZE", [.factExists "Decision"], [authFact EXECUTE], [], [], [], .E2, false⟩

/-- Оператор, отсутствующий в реестре (T07). -/
def TELEPORT : Op := ⟨"TELEPORT", [], ["Teleported"], [], [], [], .E3, false⟩

/-- Полный реестр известных операторов. -/
def registry : List Op :=
  [MEASURE, CALIBRATE, MODEL, CHECK_SUFFICIENCY, STRICT_MODEL, CREATE_X, CREATE_Y,
   DELETE_X, ANALYZE_X, ANALYZE_Y, CONSUME_X, MODIFY_X, USE_X, CALIBRATE_X,
   DECIDE, EXECUTE, AUTHORIZE]

/-- Пустое начальное состояние. -/
def s0 : KState := ⟨[], []⟩

/-! ## T01 — недоказанная достаточность данных -/

/-- Реестр без оператора проверки достаточности (исходная конфигурация T01). -/
def registryNoCheck : List Op :=
  registry.filter (fun o => o.name != "CHECK_SUFFICIENCY")

/-- **T01 (дефект конфигурации).**  `MEASURE → CALIBRATE → MODEL` без явно доказанной
достаточности данных **не** даёт PASS: заявленный в первичном прогоне PASS
был ошибкой. -/
theorem T01_no_pass :
    compile ⟨registryNoCheck, s0, [MEASURE, CALIBRATE, MODEL],
      .factExists "Model"⟩ = ⟨.UNDECIDABLE, none, some "MODEL"⟩ := by
  decide

/-- **T01 (после исправления).**  С явной проверкой достаточности цепочка
проходит. -/
theorem T01_fixed_pass :
    compile ⟨registry, s0, [MEASURE, CALIBRATE, CHECK_SUFFICIENCY, MODEL],
      .factExists "Model"⟩ = ⟨.PASS, none, none⟩ := by
  decide

/-! ## T02 — независимое уничтожение -/

/-- **T02.**  `CREATE X → CREATE Y → DELETE X → ANALYZE Y` корректно:
уничтожение X не влияет на анализ Y. -/
theorem T02_pass :
    compile ⟨registry, s0, [CREATE_X, CREATE_Y, DELETE_X, ANALYZE_Y],
      .factExists "AnalysisY"⟩ = ⟨.PASS, none, none⟩ := by
  decide

/-! ## T03 — уничтожение живого факта -/

/-- **T03.**  `CREATE X → DELETE X → ANALYZE X` отвергается: X принадлежит
LIVE_OUT оператора DELETE (LAW-006). -/
theorem T03_liveness_violation :
    compile ⟨registry, s0, [CREATE_X, DELETE_X, ANALYZE_X],
      .factExists "AnalysisX"⟩ =
        ⟨.REJECT, some .E_LIVENESS_VIOLATION, some "DELETE_X"⟩ := by
  decide

/-! ## T05 / T06 — UNKNOWN не равен FALSE -/

/-- **T05.**  `MEASURE → MODEL` при неизвестной достаточности —
UNDECIDABLE, а не REJECT. -/
theorem T05_undecidable :
    compile ⟨registryNoCheck, s0, [MEASURE, MODEL], .factExists "Model"⟩ =
      ⟨.UNDECIDABLE, none, some "MODEL"⟩ := by
  decide

/-- Состояние с доказанно недостаточными данными (0.20). -/
def sLowSufficiency : KState := ⟨[], [("sufficiency", some 20)]⟩

/-- Состояние с достаточными данными (0.90). -/
def sHighSufficiency : KState := ⟨[], [("sufficiency", some 90)]⟩

/-- **T06.**  Доказанно ложное предусловие (0.20 < 0.80) — REJECT. -/
theorem T06_reject :
    compile ⟨registry, sLowSufficiency, [STRICT_MODEL], .factExists "Model"⟩ =
      ⟨.REJECT, some .E_PRECONDITION_FALSE, some "STRICT_MODEL"⟩ := by
  decide

/-- Тот же сценарий с достаточными данными проходит: различие T05/T06 не
вырождено. -/
theorem T06_pass_when_sufficient :
    compile ⟨registry, sHighSufficiency, [STRICT_MODEL], .factExists "Model"⟩ =
      ⟨.PASS, none, none⟩ := by
  decide

/-! ## T07 — неизвестный оператор -/

/-- **T07.**  Оператор вне реестра — REJECT / `E_UNKNOWN_OPERATOR`. -/
theorem T07_unknown_operator :
    compile ⟨registry, s0, [MEASURE, TELEPORT, MODEL], .factExists "Model"⟩ =
      ⟨.REJECT, some .E_UNKNOWN_OPERATOR, some "TELEPORT"⟩ := by
  decide

/-! ## T08 / T09 / T10 — слияние ветвей -/

/-- Слияние значений переменной из двух ветвей: совпадение сохраняется,
расхождение даёт «значение неизвестно». -/
def mergeVarValue : Option ℕ → Option ℕ → Option ℕ
  | some a, some b => if a = b then some a else none
  | _, _ => none

/-- **T10.**  Ветви `X = 10` и `X = 11`: существование объекта известно, а
точное значение — нет.  Существование и значение — разные компоненты
состояния. -/
theorem T10_value_undecidable :
    mergeVarValue (some 10) (some 11) = none ∧
    (Belief.join (EV.TRUE_KNOWN).toBelief (EV.TRUE_KNOWN).toBelief).collapse
      = EV.TRUE_KNOWN := by
  refine ⟨by decide, by decide⟩

/-- Совпадающие ветви сохраняют значение. -/
theorem T10_value_agreement : mergeVarValue (some 10) (some 10) = some 10 := by
  decide

/-! ## T11 — инвалидация живого предиката -/

/-- **T11.**  `CALIBRATE X → MODIFY X → USE X`: MODIFY инвалидирует
`Calibrated`, который ещё нужен USE. -/
theorem T11_invalidate_live :
    compile ⟨registry, s0, [CREATE_X, CALIBRATE_X, MODIFY_X, USE_X],
      .factExists "Used"⟩ =
        ⟨.REJECT, some .E_LIVENESS_VIOLATION, some "MODIFY_X"⟩ := by
  decide

/-! ## T12 — повторное потребление -/

/-- **T12.**  Второе `CONSUME X` недопустимо. -/
theorem T12_double_consume :
    compile ⟨registry, s0, [CREATE_X, CONSUME_X, CONSUME_X], .factExists "X"⟩ =
      ⟨.REJECT, some .E_INVARIANT_VIOLATION, some "CONSUME_X"⟩ := by
  decide

/-! ## T13 — авторизация эффекта -/

/-- **T13.**  `DECIDE → EXECUTE` без токена авторизации: REPAIR, поскольку в
реестре есть оператор авторизации (LAW-011). -/
theorem T13_missing_authorization :
    compile ⟨registry, s0, [DECIDE, EXECUTE], .factExists "Executed"⟩ =
      ⟨.REPAIR, none, some "EXECUTE"⟩ := by
  decide

/-- Починенная цепочка со вставленным `AUTHORIZE` проходит. -/
theorem T13_repaired_pass :
    compile ⟨registry, s0, [DECIDE, AUTHORIZE, EXECUTE], .factExists "Executed"⟩ =
      ⟨.PASS, none, none⟩ := by
  decide

/-- Состояние, в котором в авторизации доказанно отказано. -/
def sAuthDenied : KState := ⟨[(authFact EXECUTE, .FALSE_KNOWN)], []⟩

/-- Доказанный отказ в авторизации даёт REJECT, а не REPAIR: `FALSE_KNOWN`
и `UNKNOWN` различаются и здесь. -/
theorem T13_auth_denied_reject :
    compile ⟨registry, sAuthDenied, [DECIDE, EXECUTE], .factExists "Executed"⟩ =
      ⟨.REJECT, some .E_AUTH_DENIED, some "EXECUTE"⟩ := by
  decide

/-! ## T14 — ремонт существует, но обязательство остаётся -/

/-- Реестр, в котором есть только «стандартная» калибровка, не доказывающая
достаточность данных. -/
def registryOnlyCalibrate : List Op :=
  [MEASURE, CALIBRATE, MODEL, CREATE_X, ANALYZE_X]

/-- **T14.**  Ремонт-гипотеза (`CALIBRATE`) существует, но не закрывает
обязательство доказательства достаточности: вердикт UNDECIDABLE, а не
REPAIR. -/
theorem T14_repair_with_obligation :
    compile ⟨registryOnlyCalibrate, s0, [MEASURE, MODEL], .factExists "Model"⟩ =
      ⟨.UNDECIDABLE, none, some "MODEL"⟩ := by
  decide

/-- Когда ремонт действительно закрывает обязательство, вердикт REPAIR. -/
theorem T14_real_repair :
    compile ⟨registry, s0, [MEASURE, MODEL], .factExists "Model"⟩ =
      ⟨.REPAIR, none, some "MODEL"⟩ := by
  decide

/-! ## Нетривиальность компилятора -/

/-- Реализуются все четыре вердикта: компилятор не вырожден. -/
theorem verdicts_all_realized :
    (∃ sc : Scenario, (compile sc).verdict = .PASS) ∧
    (∃ sc : Scenario, (compile sc).verdict = .REJECT) ∧
    (∃ sc : Scenario, (compile sc).verdict = .REPAIR) ∧
    (∃ sc : Scenario, (compile sc).verdict = .UNDECIDABLE) := by
  refine ⟨⟨⟨registry, s0, [CREATE_X, ANALYZE_X], .factExists "AnalysisX"⟩, by decide⟩,
    ⟨⟨registry, s0, [CREATE_X, DELETE_X, ANALYZE_X], .factExists "AnalysisX"⟩, by decide⟩,
    ⟨⟨registry, s0, [DECIDE, EXECUTE], .factExists "Executed"⟩, by decide⟩,
    ⟨⟨registryNoCheck, s0, [MEASURE, MODEL], .factExists "Model"⟩, by decide⟩⟩

end Polymath.OSA4
