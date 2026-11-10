/-
# Конкретный сценарий: конвейер обработки данных (ETL)

Слой конкретных примеров.  Прежние сценарии OSA-4.1 были синтетическими
(`X`, `Y`, `MODEL`); здесь построен реалистичный конвейер обработки данных над
строковыми идентификаторами фактов и числовой переменной качества:

```
INGEST → VALIDATE → DEDUP → TRANSFORM → PUBLISH
```

На одном и том же реестре проверены шесть режимов работы компилятора:

* полный путь при достаточном качестве и выданной авторизации — `PASS`;
* отсутствие авторизации на необратимом шаге `PUBLISH` — `REPAIR`;
* доказанно низкое качество — `REJECT / E_PRECONDITION_FALSE`;
* неизмеренное качество — не `REJECT`, а `UNDECIDABLE` (UNKNOWN ≠ FALSE);
* оператор вне реестра — `REJECT / E_UNKNOWN_OPERATOR`;
* повторное потребление сырых данных — `REJECT / E_INVARIANT_VIOLATION`.

Дополнительно многошаговый поиск ремонта OSA-5 строит недостающий префикс
цепочки и доводит её до `PASS`.

Все утверждения **вычислены** ядром (`decide`), а не объявлены.
-/
import RequestProject.OSA5.Repair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Polymath.Examples.DataPipeline

open Polymath.OSA4
open Polymath.OSA5

/-! ## Операторы конвейера -/

/-- Приём данных из источника: производит сырой набор. -/
def INGEST : Op := ⟨"INGEST", [], ["Raw"], [], [], [], .E1, false⟩

/-- Валидация схемы: по сырым данным доказывает `Valid`. -/
def VALIDATE : Op :=
  ⟨"VALIDATE", [.factExists "Raw"], ["Valid"], [], [], [], .E1, false⟩

/-- Дедупликация: потребляет сырой набор и производит очищенный. -/
def DEDUP : Op :=
  ⟨"DEDUP", [.factExists "Valid"], ["Deduped"], ["Raw"], [], [], .E2, false⟩

/-- Трансформация: требует очищенных данных и качества не ниже 0.80
(в сотых долях). -/
def TRANSFORM : Op :=
  ⟨"TRANSFORM", [.factExists "Deduped", .gte "quality" 80], ["Transformed"], [], [], [],
    .E2, false⟩

/-- Публикация: необратимый шаг уровня E4, требует авторизации. -/
def PUBLISH : Op :=
  ⟨"PUBLISH", [.factExists "Transformed"], ["Published"], [], [], [], .E4, true⟩

/-- Выдача токена авторизации на публикацию. -/
def AUTHORIZE_PUBLISH : Op :=
  ⟨"AUTHORIZE_PUBLISH", [.factExists "Transformed"], [authFact PUBLISH], [], [], [], .E2, false⟩

/-- Оператор, которого нет в реестре конвейера. -/
def EXFILTRATE : Op := ⟨"EXFILTRATE", [], ["Leaked"], [], [], [], .E4, false⟩

/-- Реестр конвейера. -/
def pipelineRegistry : List Op :=
  [INGEST, VALIDATE, DEDUP, TRANSFORM, PUBLISH, AUTHORIZE_PUBLISH]

/-! ## Начальные состояния и цели -/

/-- Пустое состояние: качество данных ещё не измерено. -/
def sUnknown : KState := ⟨[], []⟩

/-- Состояние с измеренным высоким качеством (0.92). -/
def sGood : KState := ⟨[], [("quality", some 92)]⟩

/-- Состояние с измеренным низким качеством (0.50). -/
def sPoor : KState := ⟨[], [("quality", some 50)]⟩

/-- Цель конвейера: данные опубликованы. -/
def goalPublished : Pred := .factExists "Published"

/-- Промежуточная цель: данные преобразованы. -/
def goalTransformed : Pred := .factExists "Transformed"

/-- Полная цепочка с авторизацией. -/
def fullChain : List Op :=
  [INGEST, VALIDATE, DEDUP, TRANSFORM, AUTHORIZE_PUBLISH, PUBLISH]

/-- Та же цепочка без шага авторизации. -/
def unauthorizedChain : List Op := [INGEST, VALIDATE, DEDUP, TRANSFORM, PUBLISH]

/-! ## Сценарий 1 — полный путь -/

/-- **Счастливый путь.**  При измеренном качестве 0.92 и выданном токене
авторизации конвейер компилируется в `PASS`. -/
theorem pipeline_pass :
    compile ⟨pipelineRegistry, sGood, fullChain, goalPublished⟩ = ⟨.PASS, none, none⟩ := by
  decide

/-! ## Сценарий 2 — отсутствие авторизации -/

/-- **Необратимый шаг без авторизации.**  Вердикт — `REPAIR` с указанием
оператора `PUBLISH`: реестр содержит выдающий токен оператор, поэтому отказ не
окончательный. -/
theorem pipeline_repair_missing_auth :
    compile ⟨pipelineRegistry, sGood, unauthorizedChain, goalPublished⟩ =
      ⟨.REPAIR, none, some "PUBLISH"⟩ := by
  decide

/-! ## Сценарий 3 — доказанно недостаточное качество -/

/-- **Порог качества.**  При измеренном качестве 0.50 предусловие
`TRANSFORM` доказанно ложно: `REJECT / E_PRECONDITION_FALSE`. -/
theorem pipeline_reject_low_quality :
    compile ⟨pipelineRegistry, sPoor, fullChain, goalPublished⟩ =
      ⟨.REJECT, some .E_PRECONDITION_FALSE, some "TRANSFORM"⟩ := by
  decide

/-! ## Сценарий 4 — качество не измерено -/

/-- **UNKNOWN ≠ FALSE.**  Если качество не измерено, конвейер не отвергается. -/
theorem pipeline_not_reject_when_unknown :
    (compile ⟨pipelineRegistry, sUnknown, fullChain, goalPublished⟩).verdict ≠ .REJECT := by
  decide

/-- Точный вердикт при неизмеренном качестве — `UNDECIDABLE`. -/
theorem pipeline_undecidable_when_unknown :
    compile ⟨pipelineRegistry, sUnknown, fullChain, goalPublished⟩ =
      ⟨.UNDECIDABLE, none, some "TRANSFORM"⟩ := by
  decide

/-! ## Сценарий 5 — оператор вне реестра -/

/-- **Закрытый мир.**  Оператор, не объявленный в реестре, отвергается до
всякого эпистемического анализа. -/
theorem pipeline_reject_unknown_operator :
    compile ⟨pipelineRegistry, sGood, [INGEST, EXFILTRATE], goalPublished⟩ =
      ⟨.REJECT, some .E_UNKNOWN_OPERATOR, some "EXFILTRATE"⟩ := by
  decide

/-! ## Сценарий 6 — повторное потребление -/

/-- **Инвариант ресурса.**  Дважды дедуплицировать один и тот же сырой набор
нельзя: второй `DEDUP` потребляет уже потреблённый `Raw`. -/
theorem pipeline_reject_double_consume :
    compile ⟨pipelineRegistry, sGood, [INGEST, VALIDATE, DEDUP, DEDUP], goalTransformed⟩ =
      ⟨.REJECT, some .E_INVARIANT_VIOLATION, some "DEDUP"⟩ := by
  decide

/-! ## Многошаговый ремонт конвейера -/

/-- Цель поиска ремонта: сделать исполнимой цепочку `TRANSFORM`. -/
def transformGoal : Pred := chainPred [TRANSFORM] goalTransformed

/-- Ремонта длины ≤ 2 не существует. -/
theorem pipeline_no_short_repair :
    searchRepair pipelineRegistry transformGoal 2 sGood = none := by
  decide

/-- Трёхшаговый ремонт найден: приём → валидация → дедупликация. -/
theorem pipeline_three_step_repair :
    searchRepair pipelineRegistry transformGoal 3 sGood = some [INGEST, VALIDATE, DEDUP] := rfl

/-- Найденный ремонт минимален среди планов длины ≤ 4. -/
theorem pipeline_minimal_repair :
    minRepair pipelineRegistry transformGoal 4 sGood = some [INGEST, VALIDATE, DEDUP] := rfl

/-- **Полнота ремонта на конкретном конвейере.**  После вставки найденного
префикса цепочка компилируется в `PASS`. -/
theorem pipeline_repaired_pass :
    compile ⟨pipelineRegistry, sGood, [INGEST, VALIDATE, DEDUP] ++ [TRANSFORM],
      goalTransformed⟩ = ⟨.PASS, none, none⟩ := by
  decide

/-- **Сводка примера.**  Один реестр, шесть режимов вердикта и найденный
многошаговый ремонт — всё вычислено ядром. -/
theorem dataPipeline_report :
    compile ⟨pipelineRegistry, sGood, fullChain, goalPublished⟩ = ⟨.PASS, none, none⟩ ∧
    compile ⟨pipelineRegistry, sGood, unauthorizedChain, goalPublished⟩ =
      ⟨.REPAIR, none, some "PUBLISH"⟩ ∧
    compile ⟨pipelineRegistry, sPoor, fullChain, goalPublished⟩ =
      ⟨.REJECT, some .E_PRECONDITION_FALSE, some "TRANSFORM"⟩ ∧
    (compile ⟨pipelineRegistry, sUnknown, fullChain, goalPublished⟩).verdict ≠ .REJECT ∧
    compile ⟨pipelineRegistry, sGood, [INGEST, EXFILTRATE], goalPublished⟩ =
      ⟨.REJECT, some .E_UNKNOWN_OPERATOR, some "EXFILTRATE"⟩ ∧
    compile ⟨pipelineRegistry, sGood, [INGEST, VALIDATE, DEDUP, DEDUP], goalTransformed⟩ =
      ⟨.REJECT, some .E_INVARIANT_VIOLATION, some "DEDUP"⟩ ∧
    minRepair pipelineRegistry transformGoal 4 sGood = some [INGEST, VALIDATE, DEDUP] ∧
    compile ⟨pipelineRegistry, sGood, [INGEST, VALIDATE, DEDUP] ++ [TRANSFORM],
      goalTransformed⟩ = ⟨.PASS, none, none⟩ :=
  ⟨pipeline_pass, pipeline_repair_missing_auth, pipeline_reject_low_quality,
    pipeline_not_reject_when_unknown, pipeline_reject_unknown_operator,
    pipeline_reject_double_consume, pipeline_minimal_repair, pipeline_repaired_pass⟩

end Polymath.Examples.DataPipeline
