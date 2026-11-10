/-
# POLYMATH-ATLAS — исполнимые проверки верификации

Модуль собирает в одном месте **вычислимые** проверки, о которых говорит
протокол верификации проекта, и отделяет их от утверждений, которые
вычислением проверить нельзя.

Различие существенно и соблюдается буквально:

* если утверждение разрешимо на конечной области (вердикт компилятора для
  конкретного сценария, соответствие Gold Dataset, покрытие базиса §13), оно
  записано как булево значение и проверено `decide`; итог печатает `#eval`;
* если утверждение — предложение с кванторами по бесконечным областям
  (`∀ o : Op`, `∀ s : KState`, `∀ r : RegExp α`, свойства множеств), оно
  **не** вычисляется: `#eval` для него не имеет смысла.  Такое утверждение
  проверяется тем, что оно доказано, а его аксиоматический базис печатает
  `#print axioms`.

Итоговая теорема модуля — `allBoolChecks_pass`.
-/
import RequestProject.OSA4.Index
import RequestProject.OSA4.Audit
import RequestProject.OSA5.Index
import RequestProject.OSA.Gold
import RequestProject.UCC
import RequestProject.AdaptiveAgent
import RequestProject.Gestalt
import RequestProject.UAM_Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace PolymathAtlas.AuditChecks

open Polymath.OSA4

/-! ## 1. Torture Set T01–T15 (ядро): вердикты вычислены -/

/-- Проверки ядра из `OSA4/TortureSet.lean`: для каждого сценария вердикт
компилятора сравнивается с эталонным значением.  T15 сюда не входит: его
утверждение — сравнение в лексикографическом порядке `RVec.lt`, чей
экземпляр разрешимости строится через `Prod.Lex` и не рассчитан на
исполнение интерпретатором; T15 проверен доказательством (см. раздел 3). -/
def coreTortureChecks : List (String × Bool) :=
  [ ("T01 недоказанная достаточность данных → UNDECIDABLE",
      compile ⟨registryNoCheck, s0, [MEASURE, CALIBRATE, MODEL], .factExists "Model"⟩ ==
        ⟨.UNDECIDABLE, none, some "MODEL"⟩)
  , ("T01 после вставки CHECK_SUFFICIENCY → PASS",
      compile ⟨registry, s0, [MEASURE, CALIBRATE, CHECK_SUFFICIENCY, MODEL],
        .factExists "Model"⟩ == ⟨.PASS, none, none⟩)
  , ("T02 независимое уничтожение → PASS",
      compile ⟨registry, s0, [CREATE_X, CREATE_Y, DELETE_X, ANALYZE_Y],
        .factExists "AnalysisY"⟩ == ⟨.PASS, none, none⟩)
  , ("T03 уничтожение живого факта → REJECT/E_LIVENESS_VIOLATION",
      compile ⟨registry, s0, [CREATE_X, DELETE_X, ANALYZE_X], .factExists "AnalysisX"⟩ ==
        ⟨.REJECT, some .E_LIVENESS_VIOLATION, some "DELETE_X"⟩)
  , ("T04 Recreation допустима, Resurrection — нет",
      (Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2) == true) &&
        (Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.resurrect 1) == false))
  , ("T05 неизвестная достаточность → UNDECIDABLE (UNKNOWN ≠ FALSE)",
      compile ⟨registryNoCheck, s0, [MEASURE, MODEL], .factExists "Model"⟩ ==
        ⟨.UNDECIDABLE, none, some "MODEL"⟩)
  , ("T06 доказанно ложное предусловие → REJECT/E_PRECONDITION_FALSE",
      compile ⟨registry, sLowSufficiency, [STRICT_MODEL], .factExists "Model"⟩ ==
        ⟨.REJECT, some .E_PRECONDITION_FALSE, some "STRICT_MODEL"⟩)
  , ("T06 достаточные данные → PASS",
      compile ⟨registry, sHighSufficiency, [STRICT_MODEL], .factExists "Model"⟩ ==
        ⟨.PASS, none, none⟩)
  , ("T07 оператор вне реестра → REJECT/E_UNKNOWN_OPERATOR",
      compile ⟨registry, s0, [MEASURE, TELEPORT, MODEL], .factExists "Model"⟩ ==
        ⟨.REJECT, some .E_UNKNOWN_OPERATOR, some "TELEPORT"⟩)
  , ("T08 присутствие отделено от истинности",
      decide ((Belief.join (EV.TRUE_KNOWN).toBelief (EV.ABSENT).toBelief).collapse
        = EV.UNKNOWN))
  , ("T09 слияние TRUE и FALSE даёт CONFLICT",
      decide ((Belief.join (EV.TRUE_KNOWN).toBelief (EV.FALSE_KNOWN).toBelief).collapse
        = EV.CONFLICT))
  , ("T10 существование известно, значение — нет",
      (mergeVarValue (some 10) (some 11) == none) &&
        (mergeVarValue (some 10) (some 10) == some 10))
  , ("T11 инвалидация живого предиката → REJECT/E_LIVENESS_VIOLATION",
      compile ⟨registry, s0, [CREATE_X, CALIBRATE_X, MODIFY_X, USE_X], .factExists "Used"⟩ ==
        ⟨.REJECT, some .E_LIVENESS_VIOLATION, some "MODIFY_X"⟩)
  , ("T12 повторное потребление → REJECT/E_INVARIANT_VIOLATION",
      compile ⟨registry, s0, [CREATE_X, CONSUME_X, CONSUME_X], .factExists "X"⟩ ==
        ⟨.REJECT, some .E_INVARIANT_VIOLATION, some "CONSUME_X"⟩)
  , ("T13 отсутствует авторизация → REPAIR",
      compile ⟨registry, s0, [DECIDE, EXECUTE], .factExists "Executed"⟩ ==
        ⟨.REPAIR, none, some "EXECUTE"⟩)
  , ("T13 вставленный AUTHORIZE → PASS",
      compile ⟨registry, s0, [DECIDE, AUTHORIZE, EXECUTE], .factExists "Executed"⟩ ==
        ⟨.PASS, none, none⟩)
  , ("T13 доказанный отказ в авторизации → REJECT/E_AUTH_DENIED",
      compile ⟨registry, sAuthDenied, [DECIDE, EXECUTE], .factExists "Executed"⟩ ==
        ⟨.REJECT, some .E_AUTH_DENIED, some "EXECUTE"⟩)
  , ("T14 ремонт-гипотеза не закрывает обязательство → UNDECIDABLE",
      compile ⟨registryOnlyCalibrate, s0, [MEASURE, MODEL], .factExists "Model"⟩ ==
        ⟨.UNDECIDABLE, none, some "MODEL"⟩)
  , ("T14 настоящий ремонт → REPAIR",
      compile ⟨registry, s0, [MEASURE, MODEL], .factExists "Model"⟩ ==
        ⟨.REPAIR, none, some "MODEL"⟩)
  ]

/-! ## 2. Прочие вычислимые проверки -/

/-- Проверки, разрешимые на конечных областях: Gold Dataset, покрытие §13,
таблица Torture Set аудита, конечная часть Meta-Schema. -/
def otherBoolChecks : List (String × Bool) :=
  [ ("Gold Dataset: все кейсы соответствуют эталону",
      Polymath.OSA.goldDataset.all (fun g => g.conforms))
  , ("Gold Dataset: распределение вердиктов",
      (Polymath.OSA.goldCount .PASS == 6) && (Polymath.OSA.goldCount .REPAIR == 8) &&
        (Polymath.OSA.goldCount .REJECT == 11) && (Polymath.OSA.goldCount .SPEC_GAP == 0))
  , ("Базис §13: закрыты все 90 позиций",
      decide (∀ (l : LawId) (k : BasisKind), covered l k = true))
  , ("Базис §13: ровно 90 записей покрытия",
      coverage.length == requiredPositions)
  , ("LAWBOOK: законов ровно 18", Fintype.card LawId == 18)
  , ("Torture Set аудита: тестов ровно 20", Fintype.card TortureId == 20)
  , ("Meta-Schema: узлы не повторяются и покрывают все понятия ядра",
      decide ((metaSchema.map SchemaNode.notion).Nodup ∧
        ∀ n : KernelNotion, n ∈ metaSchema.map SchemaNode.notion))
  , ("Компилятор нетривиален: реализуются все четыре вердикта",
      decide (∀ v : Verdict, ∃ sc ∈ mcScenarios, (compile sc).verdict = v))
  ]

/-- Все вычислимые проверки протокола. -/
def allBoolChecks : List (String × Bool) := coreTortureChecks ++ otherBoolChecks

/-- Все проверки Torture Set пройдены. -/
theorem coreTortureChecks_pass : coreTortureChecks.all (fun c => c.2) = true := by decide

/-- Все остальные вычислимые проверки пройдены. -/
theorem otherBoolChecks_pass : otherBoolChecks.all (fun c => c.2) = true := by decide

/-- **Все вычислимые проверки пройдены.**  Утверждение доказано перебором,
а не объявлено. -/
theorem allBoolChecks_pass : allBoolChecks.all (fun c => c.2) = true := by
  rw [allBoolChecks, List.all_append, coreTortureChecks_pass, otherBoolChecks_pass]
  rfl

/-- Проверок в наборе двадцать семь. -/
theorem allBoolChecks_card : allBoolChecks.length = 27 := by
  simp [allBoolChecks, coreTortureChecks, otherBoolChecks]

/-- Печать сводки: `true` для каждой проверки. -/
def summary : String :=
  String.intercalate "\n"
    (allBoolChecks.map (fun c => (if c.2 then "PASS  " else "FAIL  ") ++ c.1))

#eval IO.println summary
#eval allBoolChecks.all (fun c => c.2)

/-! ## 3. Утверждения, которые вычислением не проверяются

Ниже перечислены результаты протокола, областями кванторов которых являются
бесконечные типы (`Op`, `KState`, `Pred`, `RegExp`, множества натуральных
чисел, произвольные типы).  Для них `#eval` неприменим; проверкой служит
доказательство, а `#print axioms` показывает, что оно опирается только на
стандартные аксиомы Lean. -/

section NonComputable

#print axioms torture_all_pass
#print axioms RVec.torture_T15_safe_beats_cheap
#print axioms lawbook_holds
#print axioms kernel_model_check
#print axioms metaSchema_is_faithful_serialization
#print axioms Polymath.OSA.goldDataset_conforms
#print axioms coverage_complete
#print axioms PolymathAtlas.Core.distinction_nontrivial
#print axioms PolymathAtlas.Core.informationGain_eq_zero_iff
#print axioms PolymathAtlas.AdaptiveAgent.live_iff_setOf_active_infinite
#print axioms PolymathAtlas.AdaptiveAgent.exists_fixed_point_selfMap
#print axioms PolymathAtlas.Gestalt.UCC.t5_pigeonholeRevisit
#print axioms PolymathAtlas.Gestalt.CoreBridge.reflexiveAdaptiveAgent_drawsDistinction
#print axioms UAM_Ring.regexRoundTrip_language

end NonComputable

end PolymathAtlas.AuditChecks
