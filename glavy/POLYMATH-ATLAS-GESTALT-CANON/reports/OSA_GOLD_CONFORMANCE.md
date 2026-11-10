# OSA-3.2 — Gold Dataset, Conformance Matrix и слои §14–§19

Документ сгенерирован из Lean-исходников `RequestProject/OSA/`.
Каждая таблица ниже не просто напечатана: соответствующее утверждение
**доказано** в Lean (`by decide` по конечному набору кейсов либо
обычным доказательством для произвольного входа). Sorry и кастомных
аксиом нет; зависимости — только `propext`, `Classical.choice`,
`Quot.sound`.

Файлы:

| Файл | Раздел спецификации |
|---|---|
| `RequestProject/OSA/Spec.lean` | §2–§9: контракты, типы, правила компиляции, коды ошибок |
| `RequestProject/OSA/Theorems.lean` | общие теоремы о компиляторе |
| `RequestProject/OSA/Cases.lean` | разобранные кейсы (см. `OSA_REPORTS.md`) |
| `RequestProject/OSA/Gold.lean` | §12: Gold Dataset v0.1, 15 кейсов |
| `RequestProject/OSA/Conformance.lean` | §13: Conformance Matrix |
| `RequestProject/OSA/Interactive.lean` | §14: интерактивная сессия |
| `RequestProject/OSA/Docs.lean` | §15–§16: справочная система и расширенная диагностика |
| `RequestProject/OSA/Versioning.lean` | §17: версионирование композиций |
| `RequestProject/OSA/Visual.lean` | §18: ASCII / Graphviz / матрица совместимости типов |
| `RequestProject/OSA/Properties.lean` | §19: property-based свойства компилятора |

---

## 1. Gold Dataset v0.1 — вердикты компилятора

Теорема `goldDataset_conforms` (`Gold.lean`) доказывает, что для всех
15 кейсов вердикт, код ошибки и предложение починки, выданные
компилятором, совпадают с ожидаемыми полями кейса.

| Кейс | Домен | Предложенный граф | Вердикт | Код | Починка |
|---|---|---|---|---|---|
| ENG-001 | ENG | MEASURE → EXECUTE | REJECT | E_LEVEL_JUMP | — |
| ENG-002 | ENG | MEASURE → MODEL → REPRESENT_VERIFIED | REPAIR | E_NOT_YET_SATISFIED | insert VERIFY |
| ENG-003 | ENG | MEASURE → DELETE → ANALYZE | REJECT | E_INVARIANT_VIOLATION | — |
| IT-004 | IT | ALGORITHMICIZE → COMPILE → DEPLOY | REJECT | E_EFFECT_POLICY_VIOLATION | — |
| IT-005 | IT | MEASURE → MODEL_STRICT | REPAIR | E_MISSING_CONVERSION | insert CALIBRATE |
| IT-006 | IT | COMPARE → DECIDE | PASS | NONE | — |
| ML-007 | ML | MEASURE → CALIBRATE → MODEL_UNCERTAIN → VALIDATE → DECIDE → AUTHORIZE → EXECUTE | REJECT | E_EPISTEMIC_INSUFFICIENT | — |
| ML-008 | ML | SIMULATE → DECIDE → AUTHORIZE → TRANSFORM | REPAIR | E_MISSING_CONVERSION | insert VALIDATE |
| ML-009 | ML | CLUSTERIZE → DELETE_HARD | REPAIR | E_EFFECT_POLICY_VIOLATION | insert AUTHORIZE |
| SCI-010 | SCI | HYPOTHESIZE → EXPERIMENT → AXIOMATIZE | REJECT | E_CONTRACT_LEAKAGE | — |
| SCI-011 | SCI | OBSERVE → FORMALIZE → REPRESENT_DOC | PASS | NONE | — |
| BIZ-012 | BIZ | EVALUATE → DECIDE → AUTHORIZE → TRANSFORM | REJECT | E_EPISTEMIC_INSUFFICIENT | — |
| BIZ-013 | BIZ | STRUCTURE → EXECUTE_PLAN | REPAIR | E_MISSING_CONVERSION | insert VALIDATE and DECIDE |
| SAF-014 | SAF | DETECT → DIAGNOSE → EXECUTE_SAF | REJECT | E_NOT_YET_SATISFIED | — |
| SAF-015 | SAF | RECOGNIZE → INDEX | PASS | NONE | — |

Полные отчёты в формате §9 печатаются `#eval goldReports` в `Gold.lean`.

### 1.1 Аудит распределения (§12 vs факт)

§12 объявляет распределение **3 PASS + 6 REPAIR + 6 REJECT**.
Доказанное распределение (`gold_distribution`) — **3 PASS + 5 REPAIR +
7 REJECT**. Расхождение содержательно, а не арифметически:

* **SAF-014** (`DETECT → DIAGNOSE → EXECUTE_SAF`): диагноз —
  `E_NOT_YET_SATISFIED` (прекондиции `EXECUTE_SAF` не установлены, нет
  предшествующего AUTHORIZE), но при политике починки по умолчанию
  `forbid` вердикт эскалируется в REJECT: автоматическая вставка
  авторизации перед E4-действием запрещена. При явно разрешённой
  политике тот же кейс даёт REPAIR с тем же кодом — доказано
  (`SAF014_repair_under_allow`): эскалация меняет вердикт, но не
  диагноз. Отдельная находка: буквальный граф §12 `DETECT → EXECUTE`
  отвергается раньше, на уровне типов (прыжок L1 → L3), так что
  ожидаемый в §12 код `E_NOT_YET_SATISFIED` для него принципиально
  недостижим — §9 проверяет типы прежде контрактов
  (`SAF014_literal_graph_is_level_jump`).
* **IT-004** (`… → DEPLOY`) остаётся REJECT, пока в реестре нет
  оператора, выдающего человеческую авторизацию; с оператором
  `AUTHORIZE_HUMAN` кейс становится чинимым — доказано
  (`IT004_repairable_with_human_authorizer`).

### 1.2 Находка §12 по SAF-015

§12 отмечает конфликт «E3 → PASS»: наличие внешнего эффекта не равно
безопасности. В формализации это разведено доказательствами:

* `SAF015_repair_under_tight_threshold` — при более жёстком объявленном
  пороге неопределённости тот же граф перестаёт быть PASS;
* `SAF015_external_variant_needs_approval` — вариант с внешним
  индексом (E3) требует подтверждения, а не проходит автоматически.

---

## 2. Conformance Matrix (§13)

`Conformance.lean` проверяет каждый контракт по осям
`operator × input_type × output_type × preconditions × postconditions ×
preserves × destroys × effect_level × allowed_effects ×
forbidden_effects × uncertainty_model × reversibility ×
requires_authorization`.

Доказано:

* `catalog_local_checks` — все контракты каталога непротиворечивы по
  объявлению уровня, эффектов, инвариантов, авторизации, обратимости и
  модели неопределённости;
* `catalog_level_shift_findings = ["DEPLOY", "DIAGNOSE"]` — ровно два
  контракта §6 нарушают правило §3 «оператор сдвигает уровень не более
  чем на ±1»: `DEPLOY : L2_CompiledBinary → L4_Deployment` и
  `DIAGNOSE : L1_DetectedEvent → L3_DiagnosticResult`;
* `repaired_contracts_conformant` — исправленные контракты
  `DEPLOY_TOKEN` (`L3_AuthorizationToken → L4_Deployment`) и
  `DIAGNOSE_L2` (`L1_DetectedEvent → L2_AnalysisResult`) проходят
  полную проверку;
* `silentWrite_not_conformant` — контракт с недекларированным эффектом
  проверку не проходит (EFFECT_LEAKAGE);
* `catalog_ids_nodup` — идентификаторы операторов уникальны;
* `goldDataset_covered_by_matrix` — каждый оператор каждого из 15
  кейсов имеет строку в матрице, то есть весь датасет механически
  проверяем.

Матрица целиком печатается `#eval conformanceMatrixRender`.

---

## 3. Слои §14–§19

### §14 — интерактивная сессия
`InteractiveSession = {registry, base, currentOps, currentState,
history}`; операции `start / add / rollback`. Доказано:
`start_consistent`, `add_consistent` (состояние сессии всегда совпадает
с вердиктом компилятора для текущей цепочки), `rollback_add`
(безусловный откат ровно на один шаг), `accepted_four_levels`
(принятая сессия прошла все четыре уровня §9). Демонстрация
воспроизводит транскрипт §14: `MEASURE ✓ → CALIBRATE ✓ → DELETE ✗
(E_INVARIANT_VIOLATION) → rollback → MODEL ✓`.

### §15–§16 — справочная система и расширенная диагностика
Для каждого оператора: назначение, описание входа/выхода, совместимые
предшественники и преемники, типовые паттерны, известные проблемы.
Для каждого кода ошибки §8: описание, причины, шаги исправления
(`errorDoc_complete`). Расширенная диагностика: объяснение типовой
несовместимости (`levelJump_explained`), перечень неустановленных
прекондиций (`missingPreconditions_eq_nil_iff`), подбор оператора,
устанавливающего недостающий факт (`suggestOperatorForFact_sound`).

### §17 — версионирование
`CompositionVersion = {version, timestamp, ops, report, notes}`,
архив с откатом, diff и журналом. Доказано: `commit_ordered` (журнал
строго упорядочен), `commit_report` (сохранённый отчёт совпадает с
вердиктом компилятора для зафиксированной цепочки — журнал не может
«разойтись» с компилятором), `rollbackTo_current`, `rollbackTo_suffix`,
`diff_self`, `diff_nonempty_means_change`.

### §18 — визуализация
ASCII-цепочка, Graphviz (DOT) и матрица совместимости типов. Доказано:
`chainTokens_mem` (отрисовка не теряет операторов), `dotEdges_length`
(рёбер ровно на одно меньше числа операторов), `dotEdges_sound` (граф
не изобретает узлов), `compatMatrix_sound`, `compat_same_level`
(совместимость типов никогда не пересекает границу уровня L0–L4),
`pass_edges_typeCompatible` (у PASS-композиции каждое нарисованное
ребро — допустимый переход типов).

### §19 — property-based свойства
Доказаны для произвольных реестра и композиции, а не только для
Gold-кейсов: `pass_implies_head_compatible`, `repair_implies_suggestion`,
`pass_excludes_reject`, `status_total`, `pass_implies_four_levels`,
`pass_semantics` (полная семантика PASS по всем четырём уровням),
`forbid_policy_never_repairs`.

---

## 4. Ограничение

Формализован **компилятор композиций** и его свойства: типовая
корректность, контрактная корректность, безопасность эффектов и
эпистемическая обоснованность в том виде, в каком они определены
в §2–§9. Ничто в этом документе не утверждает эмпирической
адекватности OSA-3.2 как модели интеллектуальных задач: статус —
архитектурная гипотеза, проверяемая через Conformance Matrix и
расширение Gold Dataset. Метрики §11 (False Accept / False Reject
и др.) требуют внешнего Gold Standard и здесь не измерялись.
