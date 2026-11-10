/-
# OSA-4.0 — реестр терминов, утверждений и открытых вопросов

Модуль фиксирует результат формальной верификации стиля ядра OSA-4.0:

1. **Термины.**  `termCatalogue` — список полных имён деклараций, дающих
   формальное определение каждому термину ядра (пять пространств, операторы,
   инварианты, эффекты, U, P, законы).  Список не содержит повторов
   (`termCatalogue_nodup`), а существование каждой декларации проверяется
   компилятором в блоке `#check` в конце модуля.
2. **Утверждения.**  `StatementId` — все ключевые утверждения ядра сверх
   восемнадцати законов; `StatementId.holds` даёт формулировку каждого как
   формулу первого порядка, `statements_hold` — доказательство всех.
3. **Вопросы первой редакции.**  `OpenId` и `OpenId.statement`: три
   утверждения, записанные как формулы.  В настоящем модуле они не выводятся
   и не постулируются (ни аксиом, ни `sorry`); все три закрыты в
   `OSA4/OpenQuestions.lean` — два опровергнуты контрпримерами, одно
   доказано.
4. **Примеры.**  Все иллюстрации ядра представлены либо вычислимыми
   тестами (`Torture Set`, `#guard` ниже), либо доказанными
   контрпримерами (`joinSpec_not_assoc`, `untouched_not_necessary`).
-/
import RequestProject.OSA4.Criteria
import RequestProject.OSA4.Spaces
import RequestProject.OSA4.Lawbook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-! ## 1. Каталог терминов -/

/-- Полные имена деклараций, формализующих термины ядра OSA-4.0.
Каждому термину источника соответствует ровно одна строка. -/
def termCatalogue : List String :=
  [ -- пять пространств (оси A–E) и пространство артефактов
    "Polymath.OSA4.Axis",
    "Polymath.OSA4.Axis.Carrier",
    "Polymath.OSA4.Axis.proj",
    "Polymath.OSA4.ArtifactType",
    "Polymath.OSA4.Category",
    "Polymath.OSA4.Role",
    "Polymath.OSA4.Level",
    "Polymath.OSA4.Phase",
    "Polymath.OSA4.TypeLattice",
    "Polymath.OSA4.Orthogonal",
    -- пространство предикатов P
    "Polymath.OSA4.PT",
    "Polymath.OSA4.Pred",
    "Polymath.OSA4.eval",
    "Polymath.OSA4.Entails",
    "Polymath.OSA4.StrictlyStronger",
    -- состояние
    "Polymath.OSA4.KState",
    "Polymath.OSA4.KState.factStatus",
    "Polymath.OSA4.KState.varValue",
    -- операторы
    "Polymath.OSA4.Op",
    "Polymath.OSA4.Op.exec",
    "Polymath.OSA4.Op.enabled",
    "Polymath.OSA4.Op.WellFormedIn",
    "Polymath.OSA4.wp",
    "Polymath.OSA4.execChain",
    "Polymath.OSA4.wpChain",
    -- инварианты
    "Polymath.OSA4.Invariant",
    "Polymath.OSA4.Invariant.holdsIn",
    "Polymath.OSA4.Op.preserves",
    "Polymath.OSA4.Untouched",
    "Polymath.OSA4.violation",
    "Polymath.OSA4.chainViolation",
    "Polymath.OSA4.singleConsumption",
    -- эффекты
    "Polymath.OSA4.EffectLevel",
    "Polymath.OSA4.EffectLevel.join",
    "Polymath.OSA4.EffectLevel.aggregate",
    "Polymath.OSA4.EffectLevel.Severer",
    "Polymath.OSA4.EffectPolicy",
    "Polymath.OSA4.authStatus",
    "Polymath.OSA4.execAllowed",
    -- неопределённость U
    "Polymath.OSA4.UStep",
    "Polymath.OSA4.UStep.honest",
    "Polymath.OSA4.UStep.Reduces",
    "Polymath.OSA4.UChain",
    "Polymath.OSA4.UWithin",
    -- эпистемическое слияние
    "Polymath.OSA4.EV",
    "Polymath.OSA4.joinSpec",
    "Polymath.OSA4.Belief",
    "Polymath.OSA4.Belief.join",
    -- идентичность
    "Polymath.OSA4.World",
    "Polymath.OSA4.Step",
    "Polymath.OSA4.Step.legal",
    "Polymath.OSA4.Step.apply",
    -- компилятор и ремонт
    "Polymath.OSA4.Verdict",
    "Polymath.OSA4.ErrCode",
    "Polymath.OSA4.Report",
    "Polymath.OSA4.Scenario",
    "Polymath.OSA4.compile",
    "Polymath.OSA4.RVec",
    "Polymath.OSA4.RVec.Better",
    "Polymath.OSA4.RepairPlan",
    "Polymath.OSA4.RepairPlan.sound",
    -- законы
    "Polymath.OSA4.LawId",
    "Polymath.OSA4.LawId.holds" ]

/-- Каталог не содержит повторов: одному термину — одна декларация. -/
theorem termCatalogue_nodup : termCatalogue.Nodup := by decide

/-- Размер каталога терминов. -/
theorem termCatalogue_length : termCatalogue.length = 63 := by decide

/-! ## 2. Реестр утверждений ядра -/

/-- Идентификаторы ключевых утверждений ядра сверх восемнадцати законов. -/
inductive StatementId
  /-- Пространств ровно пять. -/
  | S01_five_spaces
  /-- Пространство артефактов есть произведение пяти пространств. -/
  | S02_artifact_is_product
  /-- Оси ортогональны. -/
  | S03_axes_orthogonal
  /-- Ни одна ось не определяется остальными. -/
  | S04_axis_not_determined
  /-- Отношение «сильнее» на предикатах — предпорядок. -/
  | S05_entails_preorder
  /-- WP монотонен по силе предиката. -/
  | S06_wp_monotone
  /-- WP точен: значение после исполнения равно значению WP-образа до. -/
  | S07_wp_exact
  /-- Агрегация эффектов есть максимум рангов. -/
  | S08_effect_join_is_max
  /-- Ранг агрегата не меньше ранга любого элемента. -/
  | S09_effect_aggregate_dominates
  /-- Снижение неопределённости требует свидетельства. -/
  | S10_uncertainty_needs_evidence
  /-- Критерий сохранения инварианта через WP. -/
  | S11_invariant_wp_criterion
  /-- Сохранение инварианта композицией. -/
  | S12_invariant_chain_preservation
  /-- Детектор нарушений инвариантов корректен и полон. -/
  | S13_invariant_detector_exact
  /-- Вердикт PASS влечёт однократность потребления. -/
  | S14_pass_single_consumption
  /-- Вердикт PASS влечёт исполнимость цепочки и достижение цели. -/
  | S15_pass_semantically_sound
  /-- Компилятор тотален. -/
  | S16_compiler_total
  /-- Всякий REJECT снабжён кодом ошибки. -/
  | S17_reject_has_code
  /-- Все восемнадцать законов выполняются. -/
  | S18_lawbook
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace StatementId

/-- Формальная формулировка утверждения. -/
def holds : StatementId → Prop
  | .S01_five_spaces => Fintype.card Axis = 5
  | .S02_artifact_is_product =>
      ∀ x : ArtifactType, ofCoords (fun a => a.proj x) = x
  | .S03_axes_orthogonal => Orthogonal Axis.proj
  | .S04_axis_not_determined =>
      ∀ (a : Axis) (u v : a.Carrier), u ≠ v → ∀ x : ArtifactType,
        ∃ y z : ArtifactType,
          (∀ b : Axis, b ≠ a → b.proj y = b.proj x ∧ b.proj z = b.proj x) ∧
            a.proj y ≠ a.proj z
  | .S05_entails_preorder =>
      (∀ p : Pred, Entails p p) ∧
      (∀ p q r : Pred, Entails p q → Entails q r → Entails p r)
  | .S06_wp_monotone =>
      ∀ (o : Op) (p q : Pred), Entails p q → Entails (wp o p) (wp o q)
  | .S07_wp_exact =>
      ∀ (o : Op) (s : KState) (q : Pred), eval (o.exec s) q = eval s (wp o q)
  | .S08_effect_join_is_max =>
      ∀ a b : EffectLevel, (EffectLevel.join a b).rank = max a.rank b.rank
  | .S09_effect_aggregate_dominates =>
      ∀ (l : List EffectLevel) (a : EffectLevel),
        a ∈ l → a.rank ≤ (EffectLevel.aggregate l).rank
  | .S10_uncertainty_needs_evidence =>
      ∀ s : UStep, s.Reduces → s.honest → s.evidence = true
  | .S11_invariant_wp_criterion =>
      ∀ (o : Op) (I : Invariant),
        o.preserves I ↔
          ∀ s : KState, eval s I.cond = .TRUE_KNOWN →
            eval s (wp o I.cond) = .TRUE_KNOWN
  | .S12_invariant_chain_preservation =>
      ∀ (I : Invariant) (ops : List Op), (∀ o ∈ ops, o.preserves I) →
        ∀ s : KState, I.holdsIn s → I.holdsIn (execChain ops s)
  | .S13_invariant_detector_exact =>
      ∀ (Is : List Invariant) (ops : List Op) (s : KState),
        chainViolation Is ops s = none ↔
          ∀ t ∈ statesAfter ops s, InvSet.holdsIn Is t
  | .S14_pass_single_consumption =>
      ∀ sc : Scenario, (compile sc).verdict = .PASS → singleConsumption sc.chain
  | .S15_pass_semantically_sound =>
      ∀ sc : Scenario, (compile sc).verdict = .PASS →
        chainEnabled sc.chain sc.init ∧
          eval (execChain sc.chain sc.init) sc.goal = .TRUE_KNOWN
  | .S16_compiler_total =>
      ∀ sc : Scenario,
        (compile sc).verdict = .PASS ∨ (compile sc).verdict = .REJECT ∨
        (compile sc).verdict = .REPAIR ∨ (compile sc).verdict = .UNDECIDABLE
  | .S17_reject_has_code =>
      ∀ sc : Scenario, (compile sc).verdict = .REJECT → (compile sc).error.isSome
  | .S18_lawbook => ∀ l : LawId, l.holds

end StatementId

/-- **Все зарегистрированные утверждения ядра доказаны.** -/
theorem statements_hold : ∀ s : StatementId, s.holds := by
  intro s
  cases s with
  | S01_five_spaces => exact axis_card
  | S02_artifact_is_product => exact fun x => ofCoords_proj x
  | S03_axes_orthogonal => exact artifact_orthogonal
  | S04_axis_not_determined => exact fun a _ _ huv x => axis_not_determined a huv x
  | S05_entails_preorder =>
      exact ⟨entails_refl, fun _ _ _ hpq hqr => entails_trans hpq hqr⟩
  | S06_wp_monotone => exact fun o _ _ h => wp_monotone o h
  | S07_wp_exact => exact fun o s q => eval_exec_eq_eval_wp o s q
  | S08_effect_join_is_max => exact EffectLevel.rank_join
  | S09_effect_aggregate_dominates => exact fun l a ha => EffectLevel.rank_le_aggregate l a ha
  | S10_uncertainty_needs_evidence => exact fun _ h hh => reduces_needs_evidence h hh
  | S11_invariant_wp_criterion => exact preserves_iff_wp
  | S12_invariant_chain_preservation => exact fun I ops h s hs => execChain_preserves I ops h s hs
  | S13_invariant_detector_exact => exact fun Is ops s => chainViolation_eq_none_iff Is ops s
  | S14_pass_single_consumption => exact fun sc h => pass_singleConsumption sc h
  | S15_pass_semantically_sound => exact fun sc h => pass_chain_executable sc h
  | S16_compiler_total => exact compile_total
  | S17_reject_has_code => exact reject_has_code
  | S18_lawbook => exact lawbook_holds

/-- Зарегистрированных утверждений восемнадцать (сверх восемнадцати законов,
которые входят в реестр одним пунктом `S18`). -/
theorem statements_card : Fintype.card StatementId = 18 := by decide

/-! ## 3. Вопросы, оставшиеся открытыми в первой редакции

Три утверждения ниже записаны как формулы и в этом модуле не выводятся и не
постулируются.  Все три **закрыты** в `OSA4/OpenQuestions.lean`, который
импортирует настоящий модуль:

* O01 — опровергнут (`O01_repair_completeness_fails`); причина указана точно
  (`no_plan_for_negative_goal`), верная форма — `O01_repair_completeness_relative`;
* O02 — опровергнут (`O02_undecidable_resolvable_fails`), верная форма —
  `O02_resolvable_for_determinate_goal`;
* O03 — доказан (`O03_liveness_completeness_holds`).
-/

/-- Идентификаторы открытых вопросов ядра. -/
inductive OpenId
  /-- [РЕШЕНО: опровергнут] Полнота ремонтного планировщика. -/
  | O01_repair_completeness
  /-- [РЕШЕНО: опровергнут] Разрешимость вердикта UNDECIDABLE пополнением
  состояния. -/
  | O02_undecidable_resolvable
  /-- [РЕШЕНО: доказан] Полнота анализа живучести относительно семантики. -/
  | O03_liveness_completeness
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Состояние `s'` пополняет `s`: всякий известный в `s` статус факта
сохраняется. -/
def KState.Extends (s' s : KState) : Prop :=
  ∀ f : FactId, s.factStatus f ≠ .UNKNOWN → s'.factStatus f = s.factStatus f

namespace OpenId

/-- Формулировка открытого вопроса. -/
def statement : OpenId → Prop
  | .O01_repair_completeness =>
      ∀ sc : Scenario, (compile sc).verdict = .REPAIR →
        ∃ p : RepairPlan, p.sound sc.init sc.goal
  | .O02_undecidable_resolvable =>
      ∀ sc : Scenario, (compile sc).verdict = .UNDECIDABLE →
        ∃ init' : KState, init'.Extends sc.init ∧
          (compile ⟨sc.registry, init', sc.chain, sc.goal⟩).verdict ≠ .UNDECIDABLE
  | .O03_liveness_completeness =>
      ∀ (goal : Pred) (ops : List Op) (s : KState),
        livenessViolation goal ops = none →
        eval s goal = .TRUE_KNOWN →
        (∀ o ∈ ops, Untouched o goal) →
        eval (execChain ops s) goal = .TRUE_KNOWN

end OpenId

/-- Вопросов первой редакции ровно три. -/
theorem openId_card : Fintype.card OpenId = 3 := by decide

/-! ## 4. Примеры как вычислимые тесты и доказанные контрпримеры -/

/-- Тест: агрегация эффектов E1 и E4 даёт E4. -/
example : EffectLevel.aggregate [.E1, .E4, .E0] = .E4 := by decide

/-- Тест: E4 строже E1. -/
example : EffectLevel.Severer .E4 .E1 := by decide

/-- Тест: план с меньшим числом нарушений безопасности лучше более дешёвого. -/
example : RVec.Better ⟨0, 3, 0, 0, 99⟩ ⟨1, 0, 0, 0, 1⟩ := by decide

/-- Тест: шаг, снижающий неопределённость без свидетельства, нечестен. -/
example : ¬ (UStep.honest ⟨50, 10, false⟩) := by decide

/-- Контрпример (не иллюстрация): напечатанная таблица слияния не
ассоциативна. -/
theorem example_joinSpec_not_assoc :
    ¬ ∀ x y z : EV, joinSpec (joinSpec x y) z = joinSpec x (joinSpec y z) :=
  joinSpec_not_assoc

/-- Контрпример: синтаксический критерий `Untouched` достаточен, но не
необходим для сохранения инварианта. -/
theorem example_untouched_not_necessary :
    ∃ (o : Op) (I : Invariant), o.preserves I ∧ ¬ Untouched o I.cond :=
  untouched_not_necessary

/-! ## 5. Проверка существования всех деклараций каталога

Каждое имя из `termCatalogue` ниже элаборируется компилятором: если
декларация отсутствует или переименована, модуль не соберётся. -/

section CatalogueCheck

example := @Polymath.OSA4.Axis
example := @Polymath.OSA4.Axis.Carrier
example := @Polymath.OSA4.Axis.proj
example := @Polymath.OSA4.ArtifactType
example := @Polymath.OSA4.Category
example := @Polymath.OSA4.Role
example := @Polymath.OSA4.Level
example := @Polymath.OSA4.Phase
example := @Polymath.OSA4.TypeLattice
example := @Polymath.OSA4.Orthogonal
example := @Polymath.OSA4.PT
example := @Polymath.OSA4.Pred
example := @Polymath.OSA4.eval
example := @Polymath.OSA4.Entails
example := @Polymath.OSA4.StrictlyStronger
example := @Polymath.OSA4.KState
example := @Polymath.OSA4.KState.factStatus
example := @Polymath.OSA4.KState.varValue
example := @Polymath.OSA4.Op
example := @Polymath.OSA4.Op.exec
example := @Polymath.OSA4.Op.enabled
example := @Polymath.OSA4.Op.WellFormedIn
example := @Polymath.OSA4.wp
example := @Polymath.OSA4.execChain
example := @Polymath.OSA4.wpChain
example := @Polymath.OSA4.Invariant
example := @Polymath.OSA4.Invariant.holdsIn
example := @Polymath.OSA4.Op.preserves
example := @Polymath.OSA4.Untouched
example := @Polymath.OSA4.violation
example := @Polymath.OSA4.chainViolation
example := @Polymath.OSA4.singleConsumption
example := @Polymath.OSA4.EffectLevel
example := @Polymath.OSA4.EffectLevel.join
example := @Polymath.OSA4.EffectLevel.aggregate
example := @Polymath.OSA4.EffectLevel.Severer
example := @Polymath.OSA4.EffectPolicy
example := @Polymath.OSA4.authStatus
example := @Polymath.OSA4.execAllowed
example := @Polymath.OSA4.UStep
example := @Polymath.OSA4.UStep.honest
example := @Polymath.OSA4.UStep.Reduces
example := @Polymath.OSA4.UChain
example := @Polymath.OSA4.UWithin
example := @Polymath.OSA4.EV
example := @Polymath.OSA4.joinSpec
example := @Polymath.OSA4.Belief
example := @Polymath.OSA4.Belief.join
example := @Polymath.OSA4.World
example := @Polymath.OSA4.Step
example := @Polymath.OSA4.Step.legal
example := @Polymath.OSA4.Step.apply
example := @Polymath.OSA4.Verdict
example := @Polymath.OSA4.ErrCode
example := @Polymath.OSA4.Report
example := @Polymath.OSA4.Scenario
example := @Polymath.OSA4.compile
example := @Polymath.OSA4.RVec
example := @Polymath.OSA4.RVec.Better
example := @Polymath.OSA4.RepairPlan
example := @Polymath.OSA4.RepairPlan.sound
example := @Polymath.OSA4.LawId
example := @Polymath.OSA4.LawId.holds

end CatalogueCheck

end Polymath.OSA4
