# OSA-4.0 — отчёт формальной верификации ядра

Документ фиксирует результат приведения ядра OSA-4.0 к строго научной форме:
каждый термин имеет формальное определение, каждое утверждение — формулировку
в виде логической формулы, каждое доказательство — машинно-проверенный вывод,
каждый пример — вычислимый тест или доказанный контрпример.

Проверка: `lake build` проходит целиком; `sorry`/`admit` в слое отсутствуют;
новые аксиомы не вводились (все результаты опираются только на `propext`,
`Classical.choice`, `Quot.sound`; см. блок `#print axioms` в
`RequestProject/Main.lean`).

Область настоящего прохода — **ядро OSA-4.0**: 18 законов, пять пространств,
операторы, инварианты, эффекты, U (неопределённость), P (предикаты).

---

## 1. Термины и их формальные определения

Полный машинно-проверяемый список — `Polymath.OSA4.termCatalogue`
(`RequestProject/OSA4/Registry.lean`, 63 имени, без повторов:
`termCatalogue_nodup`). Существование каждой декларации проверяется
компилятором в §5 того же модуля.

### 1.1 Пять пространств (оси A–E)

| термин | формальное определение | модуль |
|---|---|---|
| пространство (ось) | `inductive Axis` (5 конструкторов) | `OSA4/Spaces.lean` |
| носитель пространства | `Axis.Carrier : Axis → Type` | `OSA4/Spaces.lean` |
| координата артефакта | `Axis.proj : (a : Axis) → ArtifactType → a.Carrier` | `OSA4/Spaces.lean` |
| артефакт | `structure ArtifactType` | `OSA4/Axes.lean` |
| категория / роль / уровень / фаза | `Category`, `Role`, `Level`, `Phase` | `OSA4/Axes.lean` |
| решётка типов, отношение подтипа | `TypeLattice`, `TypeLattice.IsSubtype` | `OSA4/Axes.lean` |
| **ортогональность** (в источнике — без определения) | `def Orthogonal` — предикат первого порядка | `OSA4/Spaces.lean` |

### 1.2 Пространство предикатов P

| термин | формальное определение | модуль |
|---|---|---|
| истинностное значение | `inductive PT` (TRUE_KNOWN / FALSE_KNOWN / UNKNOWN / CONFLICT) | `OSA4/Kernel.lean` |
| предикат | `inductive Pred` | `OSA4/Kernel.lean` |
| семантика предиката | `eval : KState → Pred → PT` | `OSA4/Kernel.lean` |
| «условие сильнее» | `Entails`, `StrictlyStronger` | `OSA4/Criteria.lean` |
| состояние | `structure KState`, `KState.factStatus`, `KState.varValue` | `OSA4/Kernel.lean` |

### 1.3 Операторы

| термин | формальное определение | модуль |
|---|---|---|
| оператор | `structure Op` (контракт + вектор эффектов) | `OSA4/Kernel.lean` |
| исполнение | `Op.exec` | `OSA4/Kernel.lean` |
| применимость | `Op.enabled`, `Op.WellFormedIn`, `execAllowed` | `OSA4/Kernel.lean`, `OSA4/Criteria.lean` |
| обратный трансформер предикатов | `wp`, `wpChain` | `OSA4/Kernel.lean` |
| композиция | `execChain` | `OSA4/Kernel.lean` |

### 1.4 Инварианты (термин, ранее не определённый)

| термин | формальное определение | модуль |
|---|---|---|
| инвариант | `structure Invariant` (имя + условие) | `OSA4/Invariants.lean` |
| выполнение инварианта | `Invariant.holdsIn` (разрешимо) | `OSA4/Invariants.lean` |
| сохранение оператором | `Op.preserves` | `OSA4/Invariants.lean` |
| «оператор не затрагивает инвариант» | `Untouched` (синтаксический критерий) | `OSA4/Criteria.lean` |
| детектор нарушений | `violation`, `chainViolation`, `statesAfter` | `OSA4/Invariants.lean` |
| содержание кода `E_INVARIANT_VIOLATION` | `singleConsumption` | `OSA4/Invariants.lean` |

### 1.5 Эффекты

| термин | формальное определение | модуль |
|---|---|---|
| уровень эффекта | `inductive EffectLevel` (E0–E4), `EffectLevel.rank` | `OSA4/Kernel.lean` |
| агрегация | `EffectLevel.join`, `EffectLevel.aggregate` | `OSA4/Effects.lean` |
| «эффект сильнее» | `EffectLevel.Severer` (строгий порядок по рангу) | `OSA4/Criteria.lean` |
| политика эффектов | `EffectPolicy`, `EffectPolicy.allows` | `OSA4/Effects.lean` |
| авторизация | `authFact`, `authStatus`, `authVerdict`, `execAllowed` | `OSA4/Effects.lean` |

### 1.6 Неопределённость U

| термин | формальное определение | модуль |
|---|---|---|
| шаг переноса неопределённости | `structure UStep` (значения в сотых долях) | `OSA4/Effects.lean` |
| честность шага | `UStep.honest` | `OSA4/Effects.lean` |
| цепочка | `UChain` | `OSA4/Effects.lean` |
| «неопределённость снизилась» | `UStep.Reduces` | `OSA4/Criteria.lean` |
| порог | `UWithin` | `OSA4/Criteria.lean` |
| уверенность | `UStep.confidence` | `OSA4/Criteria.lean` |

### 1.7 Прочее ядро

| термин | формальное определение | модуль |
|---|---|---|
| эпистемические свидетельства | `EV`, `joinSpec`, `Belief`, `Belief.join` | `OSA4/Epistemic.lean` |
| идентичность объекта, шаг мира | `World`, `Step`, `Step.legal`, `Step.apply` | `OSA4/Identity.lean` |
| вердикт, код ошибки, отчёт, сценарий | `Verdict`, `ErrCode`, `Report`, `Scenario`, `compile` | `OSA4/Compiler.lean` |
| план ремонта, качество плана | `RepairPlan`, `RepairPlan.sound`, `RVec`, `RVec.Better` | `OSA4/Repair.lean`, `OSA4/Criteria.lean` |
| закон | `LawId`, `LawId.holds` | `OSA4/Lawbook.lean` |

---

## 2. Утверждения как логические формулы

### 2.1 Восемнадцать законов

`LawId.holds : LawId → Prop` даёт формулировку каждого закона как формулы;
`lawbook_holds : ∀ l : LawId, l.holds` — доказательство всех восемнадцати;
`lawbook_card : Fintype.card LawId = 18`. Законы **не аксиомы**.

Зафиксированное расхождение с источником: LAW-014 (ассоциативность слияния)
**ложен** для напечатанной пятизначной таблицы (`joinSpec_not_assoc`, 8
контрпримеров: `joinSpec_assoc_failures_card`); закон доказан для исправленной
алгебры свидетельств `Belief` (`law014_fails_for_printed_table`).

### 2.2 Реестр утверждений ядра

`StatementId.holds` (18 пунктов) и `statements_hold : ∀ s, s.holds`
(`OSA4/Registry.lean`). Все доказаны.

| id | формулировка | доказательство |
|---|---|---|
| S01 | `Fintype.card Axis = 5` | `axis_card` |
| S02 | артефакт ≡ набор координат | `ofCoords_proj`, `artifactEquivCoords` |
| S03 | `Orthogonal Axis.proj` | `artifact_orthogonal` |
| S04 | ни одна ось не определяется остальными | `axis_not_determined` |
| S05 | `Entails` — предпорядок | `entails_refl`, `entails_trans` |
| S06 | WP монотонен по силе предиката | `wp_monotone` |
| S07 | `eval (exec o s) q = eval s (wp o q)` | `eval_exec_eq_eval_wp` |
| S08 | `rank (join a b) = max (rank a) (rank b)` | `EffectLevel.rank_join` |
| S09 | ранг агрегата мажорирует ранги элементов | `EffectLevel.rank_le_aggregate` |
| S10 | снижение U требует свидетельства | `uncertainty_drop_needs_evidence` |
| S11 | критерий сохранения инварианта через WP | `preserves_iff_wp` |
| S12 | сохранение инварианта композицией | `execChain_preserves` |
| S13 | детектор нарушений корректен **и** полон | `chainViolation_eq_none_iff` |
| S14 | PASS ⇒ однократность потребления | `pass_singleConsumption` |
| S15 | PASS ⇒ цепочка исполнима и цель доказана | `pass_chain_executable` |
| S16 | компилятор тотален | `compile_total` |
| S17 | всякий REJECT снабжён кодом | `reject_has_code` |
| S18 | все 18 законов выполняются | `lawbook_holds` |

Дополнительно доказано (`OSA4/Criteria.lean`, `OSA4/Invariants.lean`):
`strictlyStronger_trans`, `entails_ctrue`, `cfalse_entails`, `cunknown_entails`,
`entails_pand_left/right`, `EffectLevel.severer_trans`, `confidence_antitone`,
`preserves_of_wp_eq`, `preserves_of_untouched`, `wp_eq_self_of_untouched`,
`chainViolation_none_of_preserves`, `doubleConsume_rejects`,
`violation_eq_none_iff`, `epiPass_pass_sound`.

---

## 3. Оценочная лексика → формальные критерии

| было (оценка) | стало (критерий) |
|---|---|
| «более сильный эффект» | `EffectLevel.Severer a b := b.rank < a.rank`, `rank_join` |
| «добавление оператора не может ослабить эффект» | `rank_le_aggregate` (числовое неравенство) |
| «сильное / слабое предусловие» | `Entails`, `StrictlyStronger`; «слабейшее предусловие» = равносильность `law012_wp_sound` + `law012_wp_complete` |
| «хороший ремонт» | `RVec.Better` — лексикографический порядок с доминированием `safety` (`better_of_safety`) |
| «оператор не трогает инвариант» | `Untouched` + `wp_eq_self_of_untouched`; доказано, что критерий достаточен, но не необходим (`untouched_not_necessary`) |
| «оператор применим» | `Op.WellFormedIn` (разрешимый предикат) |
| «шаг обоснован» | `UStep.honest` + `reduces_needs_evidence` |
| «дыра T01» | «дефект конфигурации T01»: отсутствие предиката `DataSufficiency` в реестре; вердикт вычислен (`T01_no_pass`) и исправлен (`T01_fixed_pass`) |
| «ядро v0.2 не закрывало дыру» | отсутствие точной характеризации предикатов после исполнения; устранено `eval_exec_eq_eval_wp` |
| «PASS не самоочевидно» (§12 слоя OSA-3.2) | «PASS не выводится из уровня эффекта» |
| «планировщик ищет доказуемый план, а не удачный сценарий» | «выбор определяется доказанным критерием минимальности» (`law018_repair_sound`) |

---

## 4. Примеры: тесты и контрпримеры

* Semantic Torture Set T01–T15 (`OSA4/TortureSet.lean`): каждый кейс —
  вычисленное равенство вердикта, а не иллюстрация.
* Вычислимые тесты (`OSA4/Registry.lean` §4): агрегация эффектов, отношение
  `Severer`, отношение `Better`, нечестный шаг U — все закрыты `decide`.
* Контрпримеры (доказанные, а не описанные):
  * `example_joinSpec_not_assoc` — напечатанная таблица слияния не
    ассоциативна;
  * `example_untouched_not_necessary` — синтаксический критерий сохранения
    инварианта достаточен, но не необходим;
  * `law014_fails_for_printed_table` — расхождение LAW-014 с источником.
* Иллюстраций без формальной нагрузки в слое ядра не осталось.

---

## 5. Открытые вопросы `[OPEN]`

Записаны как формулы в `OpenId.statement` (`OSA4/Registry.lean`).
Они **не доказаны и не постулированы**: ни `axiom`, ни `sorry`; в проекте они
присутствуют только как определения типа `Prop`.

| id | формулировка | статус |
|---|---|---|
| O01 | полнота ремонтного планировщика: `verdict = REPAIR ⇒ ∃ корректный план` | `[OPEN]` |
| O02 | всякий `UNDECIDABLE` разрешим пополнением начального состояния | `[OPEN]` |
| O03 | полнота анализа живучести относительно семантики цели | `[OPEN]` |

`openId_card : Fintype.card OpenId = 3`.

---

## 6. Ограничения

1. Ось D (метки типов) бесконечна (`typeTag_infinite`), поэтому исчерпывающий
   перебор по пространству артефактов невозможен; утверждения о ней доказаны
   для произвольной решётки `TypeLattice`.
2. Формализована **спецификация** ядра и её свойства. Эмпирическая адекватность
   модели (соответствие внешней предметной области) формальными средствами не
   утверждается и не проверялась.
3. Настоящий проход охватывает ядро OSA-4.0. Слои `RequestProject/OSA/*`
   (OSA-3.2) и `RequestProject/Gestalt/*` содержат собственные докстринги;
   в них при сканировании не обнаружено метафор или ссылок на «очевидность»,
   но полная ревизия их формулировок в объём этого прохода не входила.
