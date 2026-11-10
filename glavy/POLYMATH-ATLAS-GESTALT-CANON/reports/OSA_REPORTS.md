# OSA-3.2 — вердикты компилятора по разобранным кейсам

Файл сгенерирован из `RequestProject/OSA/Cases.lean` (вывод `#eval allReports`).
Каждый вердикт ниже не просто напечатан, но и **доказан** в Lean: для каждого
кейса в `Cases.lean` есть теорема вида
`(compile stdRegistry caseX).status = … ∧ (compile stdRegistry caseX).code = …`,
закрытая вычислением (`by decide`).

Сводка:

| Кейс | Вердикт | Код |
|---|---|---|
| канонический путь §3 | PASS | NONE |
| DECIDE → EXECUTE без AUTHORIZE | REPAIR | E_EFFECT_POLICY_VIOLATION |
| DELETE → ANALYZE | REJECT | E_INVARIANT_VIOLATION |
| EXPERIMENT → AXIOMATIZE | REJECT | E_CONTRACT_LEAKAGE |
| MEASURE → EXECUTE (прыжок L1→L3) | REJECT | E_LEVEL_JUMP |
| MEASURE → VALIDATE (посредник есть) | REPAIR | E_MISSING_CONVERSION |
| MEASURE → VALIDATE (посредника нет в каталоге) | REJECT | E_TYPE_MISMATCH |
| MODEL без MEASURE | REPAIR | E_NOT_YET_SATISFIED |
| CERTIFY без доступного VERIFY | REJECT | E_UNSATISFIABLE_CONTRACT |
| SILENT_WRITE (эффект вне контракта) | REJECT | E_EFFECT_LEAKAGE |
| канонический путь без правила агрегации | SPEC_GAP | UNCERTAINTY_RULE_NOT_DEFINED |
| необратимое исполнение (порог 0.05) | REPAIR | E_EPISTEMIC_INSUFFICIENT |
| SIMULATE → … → DECIDE (порог 0.15) | REPAIR | E_EPISTEMIC_INSUFFICIENT |
| MEASURE → DELETE (глобальный инвариант) | REJECT | E_INVARIANT_VIOLATION |
| один MEASURE (выход L1) | SPEC_GAP | SPEC_GAP_UNDEFINED_THRESHOLD |

## Полные отчёты в формате §9

```
┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: GOLDEN: canonical path of §3
│ PROPOSED: MEASURE → CALIBRATE → MODEL → VALIDATE → DECIDE → AUTHORIZE → EXECUTE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    PASS
│ L3 EFFECT-SAFE:         PASS
│ L4 EPISTEMIC-JUSTIFIED: PASS
├─────────────────────────────────────────────────┤
│ VERDICT: PASS
│ ERROR_CODE: NONE
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: all four levels pass
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: DECIDE -> EXECUTE without AUTHORIZE
│ PROPOSED: MEASURE → CALIBRATE → MODEL → VALIDATE → DECIDE → EXECUTE_PLAN
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    PASS
│ L3 EFFECT-SAFE:         FAIL
│ L4 EPISTEMIC-JUSTIFIED: PASS
├─────────────────────────────────────────────────┤
│ VERDICT: REPAIR
│ ERROR_CODE: E_EFFECT_POLICY_VIOLATION
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: EXECUTE_PLAN is E4 and requires authorization
│ REPAIR SUGGESTION: insert AUTHORIZE before EXECUTE_PLAN
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: DELETE -> ANALYZE
│ PROPOSED: MEASURE → DELETE → ANALYZE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    PASS
│ L3 EFFECT-SAFE:         FAIL
│ L4 EPISTEMIC-JUSTIFIED: PASS
├─────────────────────────────────────────────────┤
│ VERDICT: REJECT
│ ERROR_CODE: E_INVARIANT_VIOLATION
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: ANALYZE requires an invariant destroyed earlier
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: EXPERIMENT -> AXIOMATIZE
│ PROPOSED: MEASURE → MODEL → EXPERIMENT → AXIOMATIZE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    FAIL
│ L3 EFFECT-SAFE:         PASS
│ L4 EPISTEMIC-JUSTIFIED: PASS
├─────────────────────────────────────────────────┤
│ VERDICT: REJECT
│ ERROR_CODE: E_CONTRACT_LEAKAGE
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: precondition of AXIOMATIZE is met only by a non-guaranteed side effect
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: MEASURE -> EXECUTE (level jump)
│ PROPOSED: MEASURE → EXECUTE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        FAIL
│ L2 CONTRACT-CORRECT:    FAIL
│ L3 EFFECT-SAFE:         FAIL
│ L4 EPISTEMIC-JUSTIFIED: PASS
├─────────────────────────────────────────────────┤
│ VERDICT: REJECT
│ ERROR_CODE: E_LEVEL_JUMP
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: level jump into EXECUTE
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: MEASURE -> VALIDATE (missing conversion)
│ PROPOSED: MEASURE → VALIDATE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        FAIL
│ L2 CONTRACT-CORRECT:    FAIL
│ L3 EFFECT-SAFE:         PASS
│ L4 EPISTEMIC-JUSTIFIED: PASS
├─────────────────────────────────────────────────┤
│ VERDICT: REPAIR
│ ERROR_CODE: E_MISSING_CONVERSION
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: output type is not accepted by VALIDATE
│ REPAIR SUGGESTION: insert MODEL before VALIDATE
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: MEASURE -> VALIDATE (missing conversion)
│ PROPOSED: MEASURE → VALIDATE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        FAIL
│ L2 CONTRACT-CORRECT:    FAIL
│ L3 EFFECT-SAFE:         PASS
│ L4 EPISTEMIC-JUSTIFIED: PASS
├─────────────────────────────────────────────────┤
│ VERDICT: REJECT
│ ERROR_CODE: E_TYPE_MISMATCH
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: output type is not accepted by VALIDATE
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: MODEL without MEASURE
│ PROPOSED: MODEL
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    FAIL
│ L3 EFFECT-SAFE:         PASS
│ L4 EPISTEMIC-JUSTIFIED: PASS
├─────────────────────────────────────────────────┤
│ VERDICT: REPAIR
│ ERROR_CODE: E_NOT_YET_SATISFIED
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: preconditions of MODEL are not established
│ REPAIR SUGGESTION: insert MEASURE before MODEL
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: CERTIFY with no verifier available
│ PROPOSED: MEASURE → MODEL → CERTIFY
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    FAIL
│ L3 EFFECT-SAFE:         PASS
│ L4 EPISTEMIC-JUSTIFIED: PASS
├─────────────────────────────────────────────────┤
│ VERDICT: REJECT
│ ERROR_CODE: E_UNSATISFIABLE_CONTRACT
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: preconditions of CERTIFY cannot be established
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: SILENT_WRITE (effect leakage)
│ PROPOSED: MEASURE → SILENT_WRITE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    PASS
│ L3 EFFECT-SAFE:         FAIL
│ L4 EPISTEMIC-JUSTIFIED: FAIL
├─────────────────────────────────────────────────┤
│ VERDICT: REJECT
│ ERROR_CODE: E_EFFECT_LEAKAGE
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: SILENT_WRITE produces an effect outside allowed_effects
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: GOLDEN without an aggregation rule
│ PROPOSED: MEASURE → CALIBRATE → MODEL → VALIDATE → DECIDE → AUTHORIZE → EXECUTE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    PASS
│ L3 EFFECT-SAFE:         PASS
│ L4 EPISTEMIC-JUSTIFIED: FAIL
├─────────────────────────────────────────────────┤
│ VERDICT: SPEC_GAP
│ ERROR_CODE: UNCERTAINTY_RULE_NOT_DEFINED
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: no aggregation rule is defined for this composition
│ REPAIR SUGGESTION: declare the aggregation rule of the composition
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: irreversible execution
│ PROPOSED: MEASURE → CALIBRATE → MODEL → VALIDATE → DECIDE → AUTHORIZE → EXECUTE_IRREVERSIBLE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    PASS
│ L3 EFFECT-SAFE:         PASS
│ L4 EPISTEMIC-JUSTIFIED: FAIL
├─────────────────────────────────────────────────┤
│ VERDICT: REPAIR
│ ERROR_CODE: E_EPISTEMIC_INSUFFICIENT
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: accumulated uncertainty exceeds the target threshold
│ REPAIR SUGGESTION: insert CALIBRATE to reduce uncertainty
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: SIMULATE -> ... -> DECIDE (epistemic budget)
│ PROPOSED: MEASURE → MODEL → SIMULATE → VALIDATE → DECIDE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    PASS
│ L3 EFFECT-SAFE:         PASS
│ L4 EPISTEMIC-JUSTIFIED: FAIL
├─────────────────────────────────────────────────┤
│ VERDICT: REPAIR
│ ERROR_CODE: E_EPISTEMIC_INSUFFICIENT
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: accumulated uncertainty exceeds the target threshold
│ REPAIR SUGGESTION: insert CALIBRATE to reduce uncertainty
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: MEASURE -> DELETE (global invariant)
│ PROPOSED: MEASURE → DELETE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    PASS
│ L3 EFFECT-SAFE:         FAIL
│ L4 EPISTEMIC-JUSTIFIED: FAIL
├─────────────────────────────────────────────────┤
│ VERDICT: REJECT
│ ERROR_CODE: E_INVARIANT_VIOLATION
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: the composition as a whole destroys a required invariant
└─────────────────────────────────────────────────┘

┌─ ARISTOTLE OSA-3.2 ─────────────────────────────┐
│ CASE: MEASURE alone (no threshold for an L1 output)
│ PROPOSED: MEASURE
├─────────────────────────────────────────────────┤
│ L1 TYPE-CORRECT:        PASS
│ L2 CONTRACT-CORRECT:    PASS
│ L3 EFFECT-SAFE:         PASS
│ L4 EPISTEMIC-JUSTIFIED: FAIL
├─────────────────────────────────────────────────┤
│ VERDICT: SPEC_GAP
│ ERROR_CODE: SPEC_GAP_UNDEFINED_THRESHOLD
├─────────────────────────────────────────────────┤
│ DETAILED ANALYSIS: OSA-3.2 defines no decision threshold for this output level
└─────────────────────────────────────────────────┘
```
