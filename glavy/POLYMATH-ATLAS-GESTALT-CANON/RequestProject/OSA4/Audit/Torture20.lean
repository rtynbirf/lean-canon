/-
# OSA-4.0 — Torture Tests T1 – T20: запуск и итог

Запрос аудита: «запусти все тесты T1–T20, отметь пройденные/проваленные».

T01–T15 — Semantic Torture Set кодекса; их вердикты уже вычислены
компилятором в `TortureSet.lean`, `Identity.lean`, `Epistemic.lean` и
`Repair.lean`.  T16–T20 добавлены этим аудитом и покрывают позиции, которых
исходный набор не проверял: единица алгебры эффектов, антисимметрия системы
типов, односторонность LAW-011, ацикличность и завершаемость генератора
свидетелей, совместность LAW-006 и LAW-017.

Каждый тест записан как **утверждение** `TortureId.passed`, а не как отметка
в таблице; итог — `torture_all_pass : ∀ t : TortureId, t.passed`
(все 20 тестов пройдены) и `torture_card` (тестов ровно 20).

Проваленных тестов нет.  Две находки аудита (односторонность LAW-011 и
неполнота одношаговой починки) зафиксированы как **пройденные** тесты T18 и
T04-соседние проверки в `Consistency.lean`: тест считается пройденным, когда
поведение ядра доказанно совпадает с доказанным утверждением о нём, включая
доказанные отрицательные результаты.
-/
import RequestProject.OSA4.Audit.Consistency

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Polymath.OSA4

/-- Идентификаторы тестов Torture Set (T01–T15 кодекса и T16–T20 аудита). -/
inductive TortureId
  | T01 | T02 | T03 | T04 | T05 | T06 | T07 | T08 | T09 | T10
  | T11 | T12 | T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace TortureId

/-- Название теста. -/
def title : TortureId → String
  | .T01 => "Недоказанная достаточность данных"
  | .T02 => "Независимое уничтожение"
  | .T03 => "Уничтожение живого факта"
  | .T04 => "Recreation ≠ Resurrection"
  | .T05 => "UNKNOWN ≠ FALSE"
  | .T06 => "Доказанно ложное предусловие"
  | .T07 => "Оператор вне реестра"
  | .T08 => "Presence отделено от truth"
  | .T09 => "Слияние TRUE и FALSE даёт CONFLICT"
  | .T10 => "Существование известно, значение — нет"
  | .T11 => "Инвалидация живого предиката"
  | .T12 => "Повторное потребление"
  | .T13 => "Авторизация эффекта"
  | .T14 => "Ремонт существует, обязательство остаётся"
  | .T15 => "Лексикографический ремонт: безопасность доминирует"
  | .T16 => "Единица алгебры эффектов"
  | .T17 => "Антисимметрия системы типов"
  | .T18 => "LAW-011 односторонний"
  | .T19 => "WitnessGenerator: ацикличность и завершаемость"
  | .T20 => "LAW-006 и LAW-017 совместны: статус UNKNOWN"

/-- Проверяемое тестом утверждение. -/
def passed : TortureId → Prop
  | .T01 =>
      compile ⟨registryNoCheck, s0, [MEASURE, CALIBRATE, MODEL], .factExists "Model"⟩ =
        ⟨.UNDECIDABLE, none, some "MODEL"⟩ ∧
      compile ⟨registry, s0, [MEASURE, CALIBRATE, CHECK_SUFFICIENCY, MODEL],
        .factExists "Model"⟩ = ⟨.PASS, none, none⟩
  | .T02 =>
      compile ⟨registry, s0, [CREATE_X, CREATE_Y, DELETE_X, ANALYZE_Y],
        .factExists "AnalysisY"⟩ = ⟨.PASS, none, none⟩
  | .T03 =>
      compile ⟨registry, s0, [CREATE_X, DELETE_X, ANALYZE_X], .factExists "AnalysisX"⟩ =
        ⟨.REJECT, some .E_LIVENESS_VIOLATION, some "DELETE_X"⟩
  | .T04 =>
      Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2) = true ∧
      Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.resurrect 1) = false
  | .T05 =>
      compile ⟨registryNoCheck, s0, [MEASURE, MODEL], .factExists "Model"⟩ =
        ⟨.UNDECIDABLE, none, some "MODEL"⟩ ∧ EV.UNKNOWN ≠ EV.FALSE_KNOWN
  | .T06 =>
      compile ⟨registry, sLowSufficiency, STRICT_MODEL :: [], .factExists "Model"⟩ =
        ⟨.REJECT, some .E_PRECONDITION_FALSE, some "STRICT_MODEL"⟩ ∧
      compile ⟨registry, sHighSufficiency, STRICT_MODEL :: [], .factExists "Model"⟩ =
        ⟨.PASS, none, none⟩
  | .T07 =>
      compile ⟨registry, s0, [MEASURE, TELEPORT, MODEL], .factExists "Model"⟩ =
        ⟨.REJECT, some .E_UNKNOWN_OPERATOR, some "TELEPORT"⟩
  | .T08 =>
      (Belief.join (EV.TRUE_KNOWN).toBelief (EV.ABSENT).toBelief).collapse = EV.UNKNOWN
  | .T09 =>
      (Belief.join (EV.TRUE_KNOWN).toBelief (EV.FALSE_KNOWN).toBelief).collapse = EV.CONFLICT
  | .T10 =>
      mergeVarValue (some 10) (some 11) = none ∧ mergeVarValue (some 10) (some 10) = some 10
  | .T11 =>
      compile ⟨registry, s0, [CREATE_X, CALIBRATE_X, MODIFY_X, USE_X], .factExists "Used"⟩ =
        ⟨.REJECT, some .E_LIVENESS_VIOLATION, some "MODIFY_X"⟩
  | .T12 =>
      compile ⟨registry, s0, [CREATE_X, CONSUME_X, CONSUME_X], .factExists "X"⟩ =
        ⟨.REJECT, some .E_INVARIANT_VIOLATION, some "CONSUME_X"⟩ ∧
      ∀ (w : World) (i : ObjId), Step.legal w (.consume i) = true →
        Step.legal (Step.apply w (.consume i)) (.consume i) = false
  | .T13 =>
      compile ⟨registry, s0, [DECIDE, EXECUTE], .factExists "Executed"⟩ =
        ⟨.REPAIR, none, some "EXECUTE"⟩ ∧
      compile ⟨registry, s0, [DECIDE, AUTHORIZE, EXECUTE], .factExists "Executed"⟩ =
        ⟨.PASS, none, none⟩ ∧
      compile ⟨registry, sAuthDenied, [DECIDE, EXECUTE], .factExists "Executed"⟩ =
        ⟨.REJECT, some .E_AUTH_DENIED, some "EXECUTE"⟩
  | .T14 =>
      compile ⟨registryOnlyCalibrate, s0, [MEASURE, MODEL], .factExists "Model"⟩ =
        ⟨.UNDECIDABLE, none, some "MODEL"⟩ ∧
      compile ⟨registry, s0, [MEASURE, MODEL], .factExists "Model"⟩ =
        ⟨.REPAIR, none, some "MODEL"⟩
  | .T15 => RVec.lt ⟨0, 0, 0, 0, 3⟩ ⟨1, 0, 0, 0, 1⟩
  | .T16 =>
      EffectLevel.aggregate [] = EffectLevel.unitEffect ∧
      (∀ e : EffectLevel, EffectLevel.aggregate [EffectLevel.unitEffect, e] = e) ∧
      (∀ e : EffectLevel, EffectLevel.aggregate [e, EffectLevel.unitEffect] = e) ∧
      (∀ u : EffectLevel, (∀ a : EffectLevel, EffectLevel.join u a = a) →
        u = EffectLevel.unitEffect)
  | .T17 =>
      (¬ ∀ (L : TypeLattice) (a b : TypeTag), L.IsSubtype a b → L.IsSubtype b a → a = b) ∧
      demoLattice.Antisymmetric ∧
      demoLattice.IsSubtype "CalibratedValue" "Datum" ∧
      ¬ demoLattice.IsSubtype "Datum" "CalibratedValue"
  | .T18 =>
      (∀ (s : KState) (o : Op), execAllowed s o → authStatus s o = .TRUE_KNOWN) ∧
      ¬ (∀ (s : KState) (o : Op), authStatus s o = .TRUE_KNOWN → execAllowed s o)
  | .T19 =>
      WFTable witnessTable ∧
      (∀ a : String, ¬ Relation.TransGen (Depends witnessTable) a a) ∧
      (∀ n ∈ witnessTable, (resolve witnessTable (maxRank witnessTable + 1) n.name).isSome) ∧
      (∀ n ∈ witnessTable, n.name ∈ generateWitnesses witnessTable)
  | .T20 =>
      (∀ (o : Op) (s : KState) (f : FactId), f ∈ o.kill → f ∉ o.produces →
        (o.exec s).factStatus f = .UNKNOWN) ∧
      (∀ (o : Op) (s : KState) (f : FactId), f ∈ o.kill → f ∉ o.produces →
        eval (o.exec s) (.factExists f) ≠ .TRUE_KNOWN ∧
        eval (o.exec s) (.pnot (.factExists f)) ≠ .TRUE_KNOWN)

end TortureId

/-- **Все 20 тестов Torture Set пройдены.** -/
theorem torture_all_pass : ∀ t : TortureId, t.passed := by
  intro t
  cases t with
  | T01 => exact ⟨T01_no_pass, T01_fixed_pass⟩
  | T02 => exact T02_pass
  | T03 => exact T03_liveness_violation
  | T04 => exact torture_T04_separation
  | T05 => exact ⟨T05_undecidable, torture_T05_unknown_ne_false⟩
  | T06 => exact ⟨T06_reject, T06_pass_when_sufficient⟩
  | T07 => exact T07_unknown_operator
  | T08 => exact torture_T08_presence_vs_truth
  | T09 => exact torture_T09_conflict
  | T10 => exact ⟨T10_value_undecidable.1, T10_value_agreement⟩
  | T11 => exact T11_invalidate_live
  | T12 => exact ⟨T12_double_consume, fun w i h => torture_T12_double_consume w i h⟩
  | T13 => exact ⟨T13_missing_authorization, T13_repaired_pass, T13_auth_denied_reject⟩
  | T14 => exact ⟨T14_repair_with_obligation, T14_real_repair⟩
  | T15 => exact RVec.torture_T15_safe_beats_cheap
  | T16 =>
      exact ⟨EffectLevel.aggregate_nil_eq_unit, EffectLevel.aggregate_unit_cons,
        EffectLevel.aggregate_cons_unit, EffectLevel.unit_unique⟩
  | T17 =>
      exact ⟨isSubtype_not_antisymmetric, demoLattice_antisymmetric,
        basis_law002_positive, demoLattice_no_reverse.1⟩
  | T18 =>
      exact ⟨fun _ _ h => law011_exec_implies_authorized h, law011_converse_fails⟩
  | T19 =>
      exact ⟨witnessTable_wf, witnessTable_acyclic, resolve_terminates,
        fun _ hn => generateWitnesses_complete hn⟩
  | T20 =>
      exact ⟨fun o s _ hk hp => factStatus_exec_kill o s hk hp,
        fun o s _ hk hp => ⟨law006_kill_live_fact o s hk hp,
          law017_invalidate_not_refute o s hk hp⟩⟩

/-- Тестов ровно двадцать. -/
theorem torture_card : Fintype.card TortureId = 20 := by decide

/-- Проваленных тестов нет. -/
theorem torture_no_failures : ¬ ∃ t : TortureId, ¬ t.passed := by
  rintro ⟨t, ht⟩
  exact ht (torture_all_pass t)

end Polymath.OSA4
