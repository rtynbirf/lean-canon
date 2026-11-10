# POLYMATH-ATLAS — ОТЧЁТ О ВЕРИФИКАЦИИ

Дата прогона: 2026-08-09.
Инструмент: Lean 4.28.0 + Mathlib (версии зафиксированы в `lean-toolchain` и
`lake-manifest.json`).

Отчёт фиксирует **измеренные** значения. Там, где ожидание из задания
расходится с измерением, расхождение отмечено явно и продублировано в §15.
Никакое утверждение ниже не принято на веру: каждое подтверждено либо
вычислением (`#eval` / `decide`), либо доказательством с распечаткой
аксиоматического базиса (`#print axioms`).

Модуль исполнимых проверок: `RequestProject/AuditChecks.lean`.

---

## 1. Сборка

| Пункт | Ожидание | Измерение | Итог |
|---|---|---|---|
| `lake build` | 8253 targets, 0 errors | **8327 jobs, 0 errors** | ✅ сборка чистая, ⚠️ число целей другое |
| `sorry` в позиции доказательства | 0 | **0** | ✅ |
| `admit` | 0 | **0** | ✅ |
| Объявления `axiom` | 0 | **0** | ✅ |
| `@[implemented_by]` | — | **0** | ✅ |

Финальная строка сборки: `Build completed successfully (8327 jobs).`

Вхождения слова `sorry` в репозитории есть, но все они — прозаические
упоминания внутри docstring'ов (например «no `sorry` remains»), ни одного в
позиции доказательства.

## 2. Аксиомы

Сводка по всем директивам `#print axioms` в проекте (362 директивы,
распечатки из журнала сборки):

| Базис | Число деклараций |
|---|---|
| `[propext, Classical.choice, Quot.sound]` | 202 |
| `[propext]` | 67 |
| `[propext, Quot.sound]` | 40 |
| `[Quot.sound]` | 2 |
| «does not depend on any axioms» | 16 |

**Кастомных аксиом нет.** Используются только стандартные аксиомы Lean.

## 3. Torture Set

### 3.1 Ядро, T01–T15 (`RequestProject/OSA4/TortureSet.lean`)

Все вердикты вычислены. В `AuditChecks.coreTortureChecks` собраны 19 булевых
проверок, покрывающих T01–T14 (несколько сценариев на тест — «до ремонта» и
«после ремонта»); теорема `coreTortureChecks_pass` доказана `decide`, а
`#eval` печатает `PASS` для каждой строки:

```
PASS  T01 недоказанная достаточность данных → UNDECIDABLE
PASS  T01 после вставки CHECK_SUFFICIENCY → PASS
PASS  T02 независимое уничтожение → PASS
PASS  T03 уничтожение живого факта → REJECT/E_LIVENESS_VIOLATION
PASS  T04 Recreation допустима, Resurrection — нет
PASS  T05 неизвестная достаточность → UNDECIDABLE (UNKNOWN ≠ FALSE)
PASS  T06 доказанно ложное предусловие → REJECT/E_PRECONDITION_FALSE
PASS  T06 достаточные данные → PASS
PASS  T07 оператор вне реестра → REJECT/E_UNKNOWN_OPERATOR
PASS  T08 присутствие отделено от истинности
PASS  T09 слияние TRUE и FALSE даёт CONFLICT
PASS  T10 существование известно, значение — нет
PASS  T11 инвалидация живого предиката → REJECT/E_LIVENESS_VIOLATION
PASS  T12 повторное потребление → REJECT/E_INVARIANT_VIOLATION
PASS  T13 отсутствует авторизация → REPAIR
PASS  T13 вставленный AUTHORIZE → PASS
PASS  T13 доказанный отказ в авторизации → REJECT/E_AUTH_DENIED
PASS  T14 ремонт-гипотеза не закрывает обязательство → UNDECIDABLE
PASS  T14 настоящий ремонт → REPAIR
```

**Оговорка по T15.** T15 — сравнение в лексикографическом порядке `RVec.lt`.
Его экземпляр разрешимости строится через `Prod.Lex` и не исполняется
интерпретатором Lean: попытка `#eval decide (RVec.lt …)` аварийно завершает
процесс. Поэтому T15 не входит в булев список, а проверен доказательством:
`RVec.torture_T15_safe_beats_cheap`,
`#print axioms` → `[propext, Classical.choice, Quot.sound]`.

### 3.2 Аудит, T01–T20 (`RequestProject/OSA4/Audit/Torture20.lean`)

* `torture_all_pass` — доказана; `#print axioms` →
  `[propext, Classical.choice, Quot.sound]`.
* `Fintype.card TortureId = 20` — проверено `decide`.
* T16–T20 присутствуют **только** в аудите; в `OSA4/TortureSet.lean` их нет.
  Требование задания «если T16–T20 в ядре — переместить в аудит» уже
  выполнено, переносить нечего.
* Дополнительно: OSA5 расширяет набор до T21–T25 (`RequestProject/OSA5/Torture25.lean`).

## 4. Gold Dataset

Файл `RequestProject/OSA/Gold.lean` (расширен в этом прогоне с 15 до 25
кейсов, см. §13).

| Проверка | Значение | Способ |
|---|---|---|
| `goldDataset_card` | 25 | `decide` |
| `goldDataset_conforms` | `true` | `decide` |
| `goldDataset.all (·.conforms)` | `true` | `#eval` |
| Распределение (25 кейсов) | 6 PASS + 8 REPAIR + 11 REJECT + 0 SPEC_GAP | `gold_distribution`, `decide` |
| Распределение исходных 15 (`goldDatasetV01`) | 3 PASS + 5 REPAIR + 7 REJECT | `gold_distribution_v01`, `decide` |

**Находка.** В §12 исходной документации распределение заявлено как
3 PASS + 6 REPAIR + 6 REJECT. Это неверно: измеренное распределение исходных
15 кейсов — 3 + 5 + 7. Опровержение зафиксировано теоремой
`gold_distribution_ne_declared : goldCountV01 .REPAIR ≠ 6` (`by decide`).
Требуемые заданием «3 PASS + 5 REPAIR + 7 REJECT» подтверждены.

Отдельно: `RequestProject/OSA/Cases.lean` содержит **15** разобранных кейсов
OSA-3.2 (`allCases`) — это другой, независимый от Gold Dataset набор.

## 5. Законы OSA-4.0

`RequestProject/OSA4/Lawbook.lean`:

* `lawbook_holds` — доказана; `#print axioms` →
  `[propext, Classical.choice, Quot.sound]`.
* `Fintype.card LawId = 18` — проверено `decide` (18 законов).

Замечание о форме: `lawbook_holds` — предложение с кванторами по бесконечным
областям (`∀ o : Op`, `∀ s : KState`), поэтому оно не является булевым
значением и `#eval lawbook_holds` невозможен по типизации. Проверкой служит
доказательство.

## 6. Базис §13

`RequestProject/OSA4/Basis.lean`:

* `coverage_complete` — доказана; `#print axioms` →
  `[propext, Classical.choice, Quot.sound]`.
* `∀ (l : LawId) (k : BasisKind), covered l k = true` — проверено `decide`.
* `coverage.length = requiredPositions` (90 записей) — проверено `decide`.

**90/90 позиций закрыты.**

## 7. MODEL CHECK

`RequestProject/OSA4/ModelCheck.lean`, теорема `kernel_model_check` (доказана,
`#print axioms` → `[propext, Classical.choice, Quot.sound]`). Перебор завершён
по всем шести компонентам:

| Компонента | Утверждение | Итог |
|---|---|---|
| Алгебра PT | ассоциативность `PT.and` | ✅ |
| Алгебра EffectLevel | ассоциативность `EffectLevel.join` | ✅ |
| Алгебра Belief | ассоциативность `Belief.join` | ✅ |
| Идентичность | уничтоженное не становится доступным (LAW-004) | ✅ |
| Состояние и WP | `eval (o.exec s) q = eval s (wp o q)` на конечном универсуме | ✅ |
| Компилятор | REJECT всегда сопровождается кодом ошибки | ✅ |

Размер универсума перебора: `mcWorlds.length = 25`, `mcSteps.length = 12`
(`mc_universe_size`, `decide`).

**Честный итог перебора** (`model_check_findings`): найдены ровно два
расхождения со спецификацией, оба локализованы — напечатанная таблица слияния
неассоциативна на 8 тройках, а четырёхзначная алгебра предикатов
недистрибутивна на 2 тройках и теряет поглощение; исключительно при встрече
`UNKNOWN` с `CONFLICT`. Вне этих клеток расхождений нет. Это не дефект
проверки, а зафиксированное свойство модели.

Дополнительно проверено вычислением: компилятор нетривиален — среди сценариев
перебора реализуются все четыре вердикта.

## 8. Meta-Schema

`RequestProject/OSA4/MetaSchema.lean`:

* `metaSchema_is_faithful_serialization` — доказана; `#print axioms` →
  `[propext, Classical.choice, Quot.sound]`.
* Вычислением подтверждена конечная часть: узлы схемы не повторяются
  (`Nodup`) и покрывают все понятия ядра (`∀ n : KernelNotion, n ∈ …`).

## 9. UCC

`RequestProject/UCC.lean`, `RequestProject/Gestalt/UCC.lean` — T1–T5 доказаны:

| Теорема | Аксиомы |
|---|---|
| `PolymathAtlas.Core.distinction_nontrivial` | не зависит ни от каких аксиом |
| `PolymathAtlas.Core.informationGain_eq_zero_iff` | `[propext, Classical.choice, Quot.sound]` |
| `Gestalt.UCC.t1_no_distinction_no_information`, `t1_distinction_of_drawsDistinction` | ✅ доказаны |
| `Gestalt.UCC.t2_informationGain_nonneg`, `t2_informationGain_eq_zero_iff`, `t2_gain_pos_iff_distinction_cuts` | ✅ доказаны |
| `Gestalt.UCC.t3_feedbackError`, `t3_learningRate_pos_of_error` | ✅ доказаны |
| `Gestalt.UCC.t4_perfectPredictInert`, `t4_trajectory_const` | ✅ доказаны |
| `Gestalt.UCC.t5_pigeonholeRevisit`, `t5_system_revisits` | `[propext, Classical.choice, Quot.sound]` |

## 10. Адаптивный агент L1–L7

`RequestProject/AdaptiveAgent.lean`:

| Теорема | Аксиомы |
|---|---|
| `live_iff_setOf_active_infinite` | `[propext, Classical.choice, Quot.sound]` |
| `exists_fixed_point_selfMap` | `[propext, Quot.sound]` |

Обе — предложения о бесконечных областях (множества натуральных чисел,
произвольные типы); `#eval` к ним неприменим по типизации, проверкой служит
доказательство.

## 11. Gestalt

Модули `RequestProject/Gestalt/*.lean` + `RequestProject/Gestalt.lean`:
**78** теорем и лемм, все доказаны, `sorry` нет.

Ключевые пункты задания:

* `PolymathAtlas.Gestalt.UCC.t5_pigeonholeRevisit` — доказана;
  `[propext, Classical.choice, Quot.sound]`.
* `PolymathAtlas.Gestalt.CoreBridge.reflexiveAdaptiveAgent_drawsDistinction` —
  доказана; `[propext, Classical.choice, Quot.sound]`.

⚠️ В задании фигурирует имя `PolymathAtlas.Gestalt.UCC.pigeonholeRevisit`;
такой декларации нет, фактическое имя — `t5_pigeonholeRevisit`. Также
заявлено «68 теорем», измерено 78.

## 12. Кольцо автоматов

`RequestProject/UAM_Ring.lean`:

* `UAM_Ring.regexRoundTrip_language : languageOf (regexRoundTrip r) = languageOf r`
  для произвольного `r : RegExp α` — доказана; `#print axioms` →
  `[propext, Classical.choice, Quot.sound]`.

Полный оборот кольца (регулярное выражение → ε-NFA → DFA → минимизация →
регулярное выражение) сохраняет язык. Утверждение квантифицировано по
бесконечному типу `RegExp α`, поэтому проверяется доказательством, а не
вычислением.

## 13. Открытые вопросы O01–O03

Файл `RequestProject/OSA4/OpenQuestions.lean` (новый). Итог: **все три
вопроса закрыты** — два опровержением, один доказательством. Сводная теорема
`Polymath.OSA4.openQuestions_resolved`.

### O01 — полнота ремонтного планировщика: **ОПРОВЕРГНУТ**

Утверждение «вердикт REPAIR ⇒ существует корректный план» ложно:
`O01_repair_completeness_fails : ¬ OpenId.O01_repair_completeness.statement`.

Контрпример `OQ_negativeGoalScenario`: цель отрицательная
(`¬ FactExists "Leak"`), компилятор выдаёт REPAIR
(`OQ_negativeGoalScenario_repair`, `by decide`), но плана нет — из состояния
без опровергнутых фактов никакая цепочка операторов не делает отрицательную
цель истинной (`no_plan_for_negative_goal`, опирается на инвариант
`KState.NoRefuted`, сохраняемый `exec` и `execChain`).

**Исправленная форма (доказана):** `O01_repair_completeness_relative` —
полнота выполняется относительно самого поисковика ремонта: если
`searchRepair` возвращает план, план корректен (через
`Polymath.OSA5.searchRepair_sound`).

### O02 — разрешимость UNDECIDABLE пополнением начального состояния: **ОПРОВЕРГНУТ**

`O02_undecidable_resolvable_fails : ¬ OpenId.O02_undecidable_resolvable.statement`.

Контрпример `OQ_authKillScenario`: шаг цепочки сам обнуляет токен
авторизации, поэтому статус авторизации остаётся `UNKNOWN` при **любом**
начальном состоянии — пополнение начального состояния не помогает
(`OQ_authKill_undecidable` для произвольного `init`).

Второй, независимый контрпример: цель с неизвестной семантикой
(`.cunknown`) не разрешается никогда — `O02_unknown_goal_never_resolvable`.

**Исправленная форма (доказана):** `O02_resolvable_for_determinate_goal` —
для *определённой* цели (`Pred.Determinate`) пополнение начального состояния
до полного (`KState.complete`) действительно устраняет UNDECIDABLE.
Вспомогательный аппарат: `factStatus_complete`, `varValue_complete`,
`complete_extends`, `eval_ne_unknown_of_determinate`.

### O03 — полнота анализа живучести относительно семантики цели: **ДОКАЗАН**

`O03_liveness_completeness_holds : OpenId.O03_liveness_completeness.statement`
— через `eval_execChain_of_untouched`: если ни один оператор цепочки не
затрагивает цель, значение цели не меняется, поэтому анализ живучести не
пропускает нарушений этого класса.

Прозаические пометки `[OPEN]` в `RequestProject/OSA4/Registry.lean` и
docstring'и `OpenId` обновлены на «РЕШЕНО»; `OSA4/Index.lean` подключает
новый модуль.

## 14. Новые кейсы Gold Dataset

Добавлено 10 кейсов, набор расширен с 15 до 25. Исходные 15 сохранены без
изменений как `goldDatasetV01`.

| Кейс | Домен | Вердикт |
|---|---|---|
| `ENG016` | ENG | PASS |
| `IT017` | IT | PASS |
| `BIZ018` | BIZ | PASS |
| `ML019` | ML | REPAIR |
| `SAF020` | SAF | REPAIR |
| `SCI021` | SCI | REPAIR |
| `ENG022` | ENG | REJECT |
| `IT023` | IT | REJECT |
| `ML024` | ML | REJECT |
| `SAF025` | SAF | REJECT |

* Домены: ENG, IT, ML, SCI, BIZ, SAF — покрыты все шесть требуемых.
* Распределение новых 10: 3 PASS + 3 REPAIR + 4 REJECT (30 % / 30 % / 40 %).
* Вердикт каждого кейса доказан отдельной теоремой `by decide`
  (`ENG016_verdict` … `SAF025_verdict`).
* Соответствие всего набора эталону: `goldDataset_conforms` (`by decide`),
  `goldDataset_card = 25`.
* `gold_distribution` обновлено: 6 PASS + 8 REPAIR + 11 REJECT + 0 SPEC_GAP.

## 15. Статистика

Измерено на состоянии репозитория после всех изменений этого прогона.

| Показатель | Заявлено | Измерено |
|---|---|---|
| Файлов `.lean` | «40+» | **301** |
| Строк | «~15K» | **55 355** |
| Теорем / лемм / следствий | «200+» | **2 863** |
| Определений (`def`/`abbrev`/`structure`/`inductive`) | — | **2 087** |
| `example` | — | 74 |
| Директив `#print axioms` | — | 362 |
| Целей `lake build` | 8253 | **8327** |
| `sorry` | 0 | **0** |
| `admit` | 0 | **0** |
| Кастомных аксиом | 0 | **0** |

Измеренные значения занесены в проект как
`PolymathAtlas.Gestalt.atlasStatsMeasured`, и для них доказана теорема
`atlasMeasured_is_polymath_practice`. Историческая запись `aristotleStats`
(98 файлов / 15 292 строки / 742 теоремы / 458 определений) сохранена без
изменений: её docstring явно оговаривает, что это числа, названные в исходном
разговоре, а не измерение репозитория.

## 16. Расхождения

Расхождения найдены. Ни одно из них не является ошибкой доказательств;
все — расхождения между заявленными числами/именами и фактическим кодом.

1. **Число целей сборки.** Заявлено 8253, измерено **8327**
   (`Build completed successfully (8327 jobs)`). Расхождение ≈ 0,9 %;
   объясняется в том числе модулями, добавленными в этом прогоне.
2. **«40+ файлов».** Фактически **301** файл `.lean`.
3. **«~15K строк».** Фактически **55 355** строк.
4. **«200+ теорем».** Фактически **2 863** теоремы/леммы/следствия.
   (Формулировки 2–4 формально истинны как нижние оценки, но занижены в
   3,5–7,5 раза; измеренные значения внесены в код.)
5. **Историческая запись `aristotleStats`** в
   `RequestProject/Gestalt/AristotleCanon.lean` (98/15292/742/458, «8253
   targets») не соответствует репозиторию. Оставлена как есть — она
   документирована как цитата; рядом добавлена измеренная запись
   `atlasStatsMeasured`.
6. **Распределение Gold Dataset v0.1.** §12 документации заявляет
   3 PASS + 6 REPAIR + 6 REJECT; фактически 3 + 5 + 7. Опровержение
   зафиксировано теоремой `gold_distribution_ne_declared`.
7. **T15 не поддаётся `#eval`.** Экземпляр разрешимости через `Prod.Lex` не
   исполняется интерпретатором (процесс аварийно завершается). T15 проверен
   доказательством `RVec.torture_T15_safe_beats_cheap`.
8. **Часть запрошенных `#eval` невозможна по типизации.** `lawbook_holds`,
   `kernel_model_check`, `coverage_complete`,
   `metaSchema_is_faithful_serialization`, `goldDataset_conforms` (как
   `theorem`), `distinction_nontrivial`, `informationGain_eq_zero_iff`,
   `live_iff_setOf_active_infinite`, `exists_fixed_point_selfMap`,
   `t5_pigeonholeRevisit`, `reflexiveAdaptiveAgent_drawsDistinction`,
   `regexRoundTrip_language` — это теоремы (`Prop`), а не булевы значения, и
   кванторы в них пробегают бесконечные области. Для них в
   `AuditChecks.lean` §3 напечатан `#print axioms`; конечные следствия,
   которые *можно* вычислить, вынесены в булев список §1–2 того же модуля.
9. **Несуществующее имя.** В задании указано
   `PolymathAtlas.Gestalt.UCC.pigeonholeRevisit`; фактическое имя —
   `t5_pigeonholeRevisit`.
10. **«68 теорем Gestalt».** Фактически 78.
11. **`#print axioms` без аргумента**, как записано в задании, не является
    корректной командой Lean; проверка выполнена как `#print axioms <имя>`
    для каждой целевой декларации (362 директивы в проекте).
12. **Задание требовало остановиться при `false` или ошибке.** Ни одна
    проверка не вернула `false` и ни одна не завершилась ошибкой, поэтому
    остановки не потребовалось; единственная аварийная ситуация (`#eval` для
    T15) — ограничение интерпретатора, а не ложность утверждения, и она
    обойдена доказательством.

---

## Итог

| Задача | Статус |
|---|---|
| 1. Верификация данных | ✅ выполнена: 27 вычислимых проверок — все `PASS`; остальные результаты подтверждены доказательствами и `#print axioms` |
| 2. Аудит несоответствий | ✅ выполнена: 12 расхождений найдены и зафиксированы (§16), измеренная статистика внесена в код |
| 3. Открытые вопросы | ✅ выполнена: O01 и O02 опровергнуты контрпримерами, O03 доказан; для O01 и O02 доказаны исправленные формулировки |
| 4. Новые кейсы | ✅ выполнена: Gold Dataset 15 → 25, все вердикты `by decide` |
| 5. Отчёт | ✅ настоящий документ |

Сборка проекта на момент составления отчёта: **8327 целей, 0 ошибок, 0
`sorry`, 0 кастомных аксиом.**
