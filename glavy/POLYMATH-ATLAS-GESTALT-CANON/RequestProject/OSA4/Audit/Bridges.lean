/-
# OSA-4.0 — мосты между слоями ядра (Bridge 1 – Bridge 4)

Ядро OSA-4.0 состоит из четырёх независимо определённых слоёв: система типов
(ось D), пространство идентичностей (`World`/`Step`, ось E), семантическое
ядро (`KState`/`Op`/WP) и исполнимый компилятор с законами.  «Мост» — это
доказанное утверждение о том, что два слоя согласованы: понятие одного слоя
переводится в понятие другого, и перевод сохраняет вердикты.

| мост | что связывает | ключевая теорема |
|------|---------------|------------------|
| Bridge 1 | ось D (типы) ↔ пространство артефактов | `bridge1_type_artifact` |
| Bridge 2 | ядро (`Op`, `execAllowed`) ↔ эффекты и авторизация | `bridge2_kernel_effects` |
| Bridge 3 | идентичности (`World`, фазы) ↔ ядро (факты, `PT`) | `bridge3_identity_kernel` |
| Bridge 4 | законы (Lawbook) ↔ компилятор (`compile`) | `bridge4_lawbook_compiler` |

Все четыре моста доказаны; итог — `bridges_valid`.
-/
import RequestProject.OSA4.Audit.TypeSystem
import RequestProject.OSA4.Audit.Effects
import RequestProject.OSA4.Audit.Operators
import RequestProject.OSA4.Criteria

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-! ## Bridge 1 — система типов ↔ пространство артефактов -/

/-- Артефакт `a` подставим вместо артефакта `b`, если он занимает ту же
позицию по осям A, B, C, E, а его тип — подтип требуемого. -/
def ArtifactType.SubstitutableFor (L : TypeLattice) (a b : ArtifactType) : Prop :=
  L.IsSubtype a.typeTag b.typeTag ∧ a.category = b.category ∧ a.role = b.role ∧
    a.level = b.level ∧ a.phase = b.phase

/-- Подставимость рефлексивна (перевод LAW-001 на артефакты). -/
theorem ArtifactType.substitutableFor_refl (L : TypeLattice) (a : ArtifactType) :
    ArtifactType.SubstitutableFor L a a :=
  ⟨L.isSubtype_refl _, rfl, rfl, rfl, rfl⟩

/-- Подставимость транзитивна (перевод LAW-002 на артефакты). -/
theorem ArtifactType.substitutableFor_trans (L : TypeLattice) {a b c : ArtifactType}
    (hab : ArtifactType.SubstitutableFor L a b) (hbc : ArtifactType.SubstitutableFor L b c) :
    ArtifactType.SubstitutableFor L a c :=
  ⟨TypeLattice.isSubtype_trans _ hab.1 hbc.1,
    hab.2.1.trans hbc.2.1, hab.2.2.1.trans hbc.2.2.1,
    hab.2.2.2.1.trans hbc.2.2.2.1, hab.2.2.2.2.trans hbc.2.2.2.2⟩

/-- В градуированной решётке подставимость антисимметрична: взаимно подставимые
артефакты совпадают. -/
theorem ArtifactType.substitutableFor_antisymm {L : TypeLattice} {r : TypeTag → ℕ}
    (hg : TypeLattice.Graded L r) {a b : ArtifactType}
    (hab : ArtifactType.SubstitutableFor L a b) (hba : ArtifactType.SubstitutableFor L b a) :
    a = b := by
  have htag : a.typeTag = b.typeTag := TypeLattice.antisymmetric_of_graded hg _ _ hab.1 hba.1
  cases a; cases b
  simp_all [ArtifactType.SubstitutableFor]

/-- **Bridge 1.**  Отношение подтипизации оси D поднимается до отношения
подставимости артефактов: перевод сохраняет LAW-001 и LAW-002, а в
градуированной решётке — и антисимметрию.  Ортогональность осей при этом не
нарушается: подставимость ничего не говорит об осях A, B, C, E, кроме
совпадения. -/
theorem bridge1_type_artifact (L : TypeLattice) :
    (∀ a : ArtifactType, ArtifactType.SubstitutableFor L a a) ∧
    (∀ a b c : ArtifactType, ArtifactType.SubstitutableFor L a b →
      ArtifactType.SubstitutableFor L b c → ArtifactType.SubstitutableFor L a c) ∧
    (∀ (c : Category) (ro : Role) (l : Level) (p : Phase) (x y : TypeTag),
      L.IsSubtype x y →
        ArtifactType.SubstitutableFor L ⟨c, ro, l, x, p⟩ ⟨c, ro, l, y, p⟩) :=
  ⟨ArtifactType.substitutableFor_refl L,
    fun _ _ _ hab hbc => ArtifactType.substitutableFor_trans L hab hbc,
    fun _ _ _ _ _ _ h => ⟨h, rfl, rfl, rfl, rfl⟩⟩

/-! ## Bridge 2 — ядро ↔ эффекты и авторизация -/

/-- Список уровней эффекта цепочки операторов. -/
def chainEffects (ops : List Op) : List EffectLevel := ops.map Op.effect

/-- Исполнимая цепочка авторизована пооперационно: для каждого оператора
цепочки есть состояние, в котором он исполняется и в котором его авторизация
доказана (LAW-011 вдоль цепочки). -/
theorem chainEnabled_authorized :
    ∀ (ops : List Op) (s : KState), chainEnabled ops s →
      ∀ o ∈ ops, ∃ st : KState, execAllowed st o ∧ authStatus st o = .TRUE_KNOWN := by
  intro ops
  induction ops with
  | nil => intro s _ o ho; exact absurd ho (by simp)
  | cons a t ih =>
      intro s h o ho
      rcases List.mem_cons.mp ho with rfl | hto
      · exact ⟨s, h.1, h.1.2⟩
      · exact ih (a.exec s) h.2 o hto

/-- Политика эффектов соблюдена цепочкой ровно тогда, когда её соблюдает
каждый оператор: агрегация не прячет запрещённый эффект (LAW-008). -/
theorem chainEffects_policy_iff (p : EffectPolicy) (ops : List Op) :
    p.allows (chainEffects ops) = true ↔ ∀ o ∈ ops, o.effect.rank ≤ p.maxLevel.rank := by
  rw [chainEffects, EffectPolicy.allows_iff]
  simp

/-- Суммарный эффект цепочки не зависит от разбиения на участки. -/
theorem chainEffects_append (l₁ l₂ : List Op) :
    EffectLevel.aggregate (chainEffects (l₁ ++ l₂)) =
      EffectLevel.join (EffectLevel.aggregate (chainEffects l₁))
        (EffectLevel.aggregate (chainEffects l₂)) := by
  rw [chainEffects, List.map_append, EffectLevel.aggregate_append]
  rfl

/-- Пустая цепочка имеет единичный эффект. -/
@[simp] theorem chainEffects_nil_aggregate :
    EffectLevel.aggregate (chainEffects []) = EffectLevel.unitEffect := rfl

/-- **Bridge 2.**  Слой исполнения (`execAllowed`, `chainEnabled`) согласован
со слоем эффектов и авторизации: исполнимость влечёт авторизацию каждого
оператора (LAW-011), политика эффектов проверяется пооперационно (LAW-008),
а оператор, требующий токена, в состоянии без токена неисполним. -/
theorem bridge2_kernel_effects (p : EffectPolicy) :
    (∀ (ops : List Op) (s : KState), chainEnabled ops s →
      ∀ o ∈ ops, ∃ st : KState, execAllowed st o ∧ authStatus st o = .TRUE_KNOWN) ∧
    (∀ ops : List Op,
      p.allows (chainEffects ops) = true ↔ ∀ o ∈ ops, o.effect.rank ≤ p.maxLevel.rank) ∧
    (∀ (s : KState) (o : Op), o.requiresAuth = true →
      s.factStatus (authFact o) = .UNKNOWN → ¬ execAllowed s o) :=
  ⟨chainEnabled_authorized, chainEffects_policy_iff p,
    fun _ _ hreq h => no_exec_without_token hreq h⟩

/-! ## Bridge 3 — идентичности ↔ семантическое ядро -/

/-- Перевод фазы ресурса в эпистемический статус факта «ресурс доступен»:
доказана только фаза `Available`; отсутствие объекта, фаза `Created`,
`Consumed` и `Destroyed` дают `UNKNOWN` — потребление и уничтожение
обесценивают знание, но не доказывают отрицания (LAW-017). -/
def phasePT : Option Phase → PT
  | some .Available => .TRUE_KNOWN
  | _ => .UNKNOWN

/-- Перевод фаз никогда не выдаёт `FALSE_KNOWN`: «ресурса нет» — не теорема. -/
theorem phasePT_ne_false (p : Option Phase) : phasePT p ≠ .FALSE_KNOWN := by
  rcases p with _ | p
  · decide
  · cases p <;> decide

/-- Допустимость потребления в пространстве идентичностей равносильна
доказанности соответствующего факта в ядре. -/
theorem legal_consume_iff_phasePT (w : World) (i : ObjId) :
    Step.legal w (.consume i) = true ↔ phasePT (w.phaseOf i) = .TRUE_KNOWN := by
  rw [law005_consume_iff_available]
  cases h : w.phaseOf i with
  | none => simp [phasePT]
  | some p => cases p <;> simp [phasePT]

/-- **Коммутирующий квадрат потребления.**  Потребление ресурса в пространстве
идентичностей и потребление факта в ядре дают один и тот же эпистемический
статус: `UNKNOWN`. -/
theorem consume_square (w : World) (i : ObjId) (o : Op) (s : KState) {f : FactId}
    (hleg : Step.legal w (.consume i) = true) (hc : f ∈ o.consumes) (hp : f ∉ o.produces) :
    phasePT ((Step.apply w (.consume i)).phaseOf i) = (o.exec s).factStatus f := by
  rw [(consume_destroys hleg).1, (consume_kills_fact o s hc hp).1]
  rfl

/-- **Bridge 3.**  Пространство идентичностей и семантическое ядро согласованы:
перевод фаз в эпистемические статусы переводит допустимость `.consume` в
доказанность факта, потребление — в потерю знания (а не в доказательство
отрицания), а уничтоженный объект никогда не выглядит доступным (LAW-004). -/
theorem bridge3_identity_kernel :
    (∀ (w : World) (i : ObjId),
      Step.legal w (.consume i) = true ↔ phasePT (w.phaseOf i) = .TRUE_KNOWN) ∧
    (∀ (w : World) (i : ObjId) (o : Op) (s : KState) (f : FactId),
      Step.legal w (.consume i) = true → f ∈ o.consumes → f ∉ o.produces →
        phasePT ((Step.apply w (.consume i)).phaseOf i) = (o.exec s).factStatus f) ∧
    (∀ p : Option Phase, phasePT p ≠ .FALSE_KNOWN) ∧
    (∀ (w : World) (st : Step) (i : ObjId), Step.legal w st = true →
      w.phaseOf i = some .Destroyed →
        phasePT ((Step.apply w st).phaseOf i) = .UNKNOWN) :=
  ⟨legal_consume_iff_phasePT,
    fun w i o s _ hleg hc hp => consume_square w i o s hleg hc hp,
    phasePT_ne_false,
    fun w st i hleg hd => by
      have := law004_no_resurrection w st i hleg hd
      cases h : (Step.apply w st).phaseOf i with
      | none => rfl
      | some p =>
          rw [h] at this
          cases p <;> first | rfl | exact absurd rfl this⟩

/-! ## Bridge 4 — законы ↔ компилятор -/

/-- **Bridge 4.**  Вердикт компилятора не является декларацией: `PASS` влечёт
операционное содержание законов ядра — отсутствие неизвестных операторов,
однократность потребления (LAW-005), сохранность живых предикатов (LAW-006),
пошаговую исполнимость с доказанной авторизацией (LAW-011), достижение цели и
её WP-характеризацию в начальном состоянии (LAW-012). -/
theorem bridge4_lawbook_compiler (sc : Scenario) (h : (compile sc).verdict = .PASS) :
    unknownOperator sc.registry sc.chain = none ∧
    doubleConsume [] sc.chain = none ∧
    livenessViolation sc.goal sc.chain = none ∧
    chainEnabled sc.chain sc.init ∧
    (∀ o ∈ sc.chain, ∃ st : KState, execAllowed st o ∧ authStatus st o = .TRUE_KNOWN) ∧
    eval (execChain sc.chain sc.init) sc.goal = .TRUE_KNOWN ∧
    eval sc.init (wpChain sc.chain sc.goal) = .TRUE_KNOWN := by
  obtain ⟨henab, hgoal⟩ := pass_chain_executable sc h
  refine ⟨pass_no_unknown_operator sc h, pass_no_double_consume sc h,
    pass_no_liveness_violation sc h, henab,
    chainEnabled_authorized sc.chain sc.init henab, hgoal, ?_⟩
  rwa [← eval_execChain_eq_eval_wpChain]

/-- Мост 4 не пуст: существует сценарий с вердиктом `PASS`, к которому он
применяется. -/
theorem bridge4_nonvacuous :
    (compile ⟨registry, s0, [MEASURE, CALIBRATE, CHECK_SUFFICIENCY, MODEL],
      .factExists "Model"⟩).verdict = .PASS := by
  rw [T01_fixed_pass]

/-! ## Итог -/

/-- **Все четыре моста валидны.** -/
theorem bridges_valid :
    (∀ L : TypeLattice,
      (∀ a : ArtifactType, ArtifactType.SubstitutableFor L a a) ∧
      (∀ a b c : ArtifactType, ArtifactType.SubstitutableFor L a b →
        ArtifactType.SubstitutableFor L b c → ArtifactType.SubstitutableFor L a c) ∧
      (∀ (c : Category) (ro : Role) (l : Level) (p : Phase) (x y : TypeTag),
        L.IsSubtype x y →
          ArtifactType.SubstitutableFor L ⟨c, ro, l, x, p⟩ ⟨c, ro, l, y, p⟩)) ∧
    (∀ p : EffectPolicy,
      (∀ (ops : List Op) (s : KState), chainEnabled ops s →
        ∀ o ∈ ops, ∃ st : KState, execAllowed st o ∧ authStatus st o = .TRUE_KNOWN) ∧
      (∀ ops : List Op,
        p.allows (chainEffects ops) = true ↔ ∀ o ∈ ops, o.effect.rank ≤ p.maxLevel.rank) ∧
      (∀ (s : KState) (o : Op), o.requiresAuth = true →
        s.factStatus (authFact o) = .UNKNOWN → ¬ execAllowed s o)) ∧
    ((∀ (w : World) (i : ObjId),
      Step.legal w (.consume i) = true ↔ phasePT (w.phaseOf i) = .TRUE_KNOWN) ∧
     (∀ (w : World) (i : ObjId) (o : Op) (s : KState) (f : FactId),
       Step.legal w (.consume i) = true → f ∈ o.consumes → f ∉ o.produces →
         phasePT ((Step.apply w (.consume i)).phaseOf i) = (o.exec s).factStatus f) ∧
     (∀ p : Option Phase, phasePT p ≠ .FALSE_KNOWN) ∧
     (∀ (w : World) (st : Step) (i : ObjId), Step.legal w st = true →
       w.phaseOf i = some .Destroyed →
         phasePT ((Step.apply w st).phaseOf i) = .UNKNOWN)) ∧
    (∀ sc : Scenario, (compile sc).verdict = .PASS →
      chainEnabled sc.chain sc.init ∧
      eval (execChain sc.chain sc.init) sc.goal = .TRUE_KNOWN) :=
  ⟨bridge1_type_artifact, bridge2_kernel_effects, bridge3_identity_kernel,
    fun sc h => ⟨(bridge4_lawbook_compiler sc h).2.2.2.1,
      (bridge4_lawbook_compiler sc h).2.2.2.2.2.1⟩⟩

end Polymath.OSA4
