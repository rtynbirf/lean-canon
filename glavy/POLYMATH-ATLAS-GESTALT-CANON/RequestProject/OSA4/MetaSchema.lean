/-
# OSA-4.0 — замыкание Kernel v0.4 и Atlas S-1.0 Meta-Schema

Кодекс задаёт жёсткий порядок:

    KERNEL → LAWBOOK (18 законов) → MINIMAL BASIS TORTURE SET → MODEL CHECK
      → KERNEL v0.4 (closed) → ONLY THEN → Atlas S-1.0 Meta-Schema

и требование к самой схеме: «Meta-Schema должна быть **сериализацией уже
определённой математики**, а не местом, где математика впервые появляется».
Пока замыкание не доказано, схема помечена `FROZEN / DEFERRED`.

Этот модуль делает две вещи.

1. **Замыкание ядра доказано** (`kernel_v04_closed`): все 18 законов —
   теоремы (`lawbook_holds`), минимальный базисный набор §13 закрыт целиком
   (`coverage_complete`), MODEL CHECK на конечных областях пройден
   (`mc_wp_exact`, `mc_law004`, `mc_compiler`).  Тем самым условие,
   при котором кодекс разрешает генерировать схему, выполнено
   (`metaSchema_gate_open`).

2. **Схема построена именно как сериализация.**  Никаких новых
   математических понятий она не вводит: значения ядра переводятся в
   примитивный обменный формат (строки, числа, булевы значения, списки) и
   восстанавливаются обратно **точно** — доказаны теоремы обратимости для
   конечных осей (`Level`, `Phase`, `Category`, `Role`, `EffectLevel`, `PT`,
   `Verdict`, `LawId`), для языка предикатов (`pred_roundtrip`), для
   операторов (`op_roundtrip`), состояний (`kstate_roundtrip`) и цепочек
   (`chain_roundtrip`).  Обратимость и означает «сериализация, а не новая
   математика»: по сериализованному виду исходный объект ядра
   восстанавливается однозначно.

   Каталог узлов схемы (`metaSchema`) находится во взаимно однозначном
   соответствии с перечнем понятий ядра (`metaSchema_bijective`): нет ни
   узла без математического источника, ни понятия ядра без узла.
-/
import RequestProject.OSA4.ModelCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Polymath.OSA4

/-! ## 1. Замыкание Kernel v0.4 -/

/-- Условие кодекса, при котором Meta-Schema разрешено генерировать: ядро
замкнуто — законы доказаны, базисный набор §13 полон, MODEL CHECK пройден. -/
def KernelClosed : Prop :=
  (∀ l : LawId, l.holds) ∧
  (∀ (l : LawId) (k : BasisKind), covered l k = true) ∧
  (∀ o ∈ mcOps, ∀ s ∈ mcStates, ∀ q ∈ mcPreds, eval (o.exec s) q = eval s (wp o q)) ∧
  (∀ w ∈ mcWorlds, ∀ st ∈ mcSteps, ∀ i ∈ mcIds,
    Step.legal w st = true → w.phaseOf i = some .Destroyed →
      (Step.apply w st).phaseOf i ≠ some .Available) ∧
  (∀ sc ∈ mcScenarios,
    (compile sc).verdict = .REJECT → (compile sc).error.isSome = true)

/-- **Kernel v0.4 замкнут.**  Все четыре этапа кодекса пройдены. -/
theorem kernel_v04_closed : KernelClosed :=
  ⟨lawbook_holds, coverage_complete, mc_wp_exact, mc_law004,
   fun sc hsc => (mc_compiler sc hsc).1⟩

/-- **Шлюз открыт.**  Условие, при котором кодекс разрешает строить
Atlas S-1.0 Meta-Schema, выполнено — поэтому схема ниже строится законно. -/
theorem metaSchema_gate_open : KernelClosed := kernel_v04_closed

/-! ## 2. Обменный формат: только примитивы

Схема оперирует строками, числами, булевыми значениями и списками — то есть
ничем, чего не было бы в любом JSON/YAML.  Вся математика остаётся в ядре. -/

/-! ### 2.1 Конечные оси: имя ↔ значение -/

/-- Имя уровня абстракции. -/
def Level.wire : Level → String
  | .L0 => "L0" | .L1 => "L1" | .L2 => "L2" | .L3 => "L3" | .L4 => "L4"

/-- Разбор имени уровня. -/
def Level.ofWire (s : String) : Option Level :=
  if s = "L0" then some .L0 else if s = "L1" then some .L1
  else if s = "L2" then some .L2 else if s = "L3" then some .L3
  else if s = "L4" then some .L4 else none

/-- Имя фазы. -/
def Phase.wire : Phase → String
  | .Created => "Created" | .Available => "Available"
  | .Consumed => "Consumed" | .Destroyed => "Destroyed"

/-- Разбор имени фазы. -/
def Phase.ofWire (s : String) : Option Phase :=
  if s = "Created" then some .Created else if s = "Available" then some .Available
  else if s = "Consumed" then some .Consumed else if s = "Destroyed" then some .Destroyed
  else none

/-- Имя категории. -/
def Category.wire : Category → String
  | .Object => "Object" | .Data => "Data" | .Model => "Model"
  | .Decision => "Decision" | .Action => "Action" | .Meta => "Meta"

/-- Разбор имени категории. -/
def Category.ofWire (s : String) : Option Category :=
  if s = "Object" then some .Object else if s = "Data" then some .Data
  else if s = "Model" then some .Model else if s = "Decision" then some .Decision
  else if s = "Action" then some .Action else if s = "Meta" then some .Meta else none

/-- Имя роли. -/
def Role.wire : Role → String
  | .Input => "Input" | .Output => "Output" | .Resource => "Resource"
  | .Target => "Target" | .Constraint => "Constraint"

/-- Разбор имени роли. -/
def Role.ofWire (s : String) : Option Role :=
  if s = "Input" then some .Input else if s = "Output" then some .Output
  else if s = "Resource" then some .Resource else if s = "Target" then some .Target
  else if s = "Constraint" then some .Constraint else none

/-- Имя уровня эффекта. -/
def EffectLevel.wire : EffectLevel → String
  | .E0 => "E0" | .E1 => "E1" | .E2 => "E2" | .E3 => "E3" | .E4 => "E4"

/-- Разбор имени уровня эффекта. -/
def EffectLevel.ofWire (s : String) : Option EffectLevel :=
  if s = "E0" then some .E0 else if s = "E1" then some .E1
  else if s = "E2" then some .E2 else if s = "E3" then some .E3
  else if s = "E4" then some .E4 else none

/-- Имя истинностного значения. -/
def PT.wire : PT → String
  | .TRUE_KNOWN => "TRUE_KNOWN" | .FALSE_KNOWN => "FALSE_KNOWN"
  | .UNKNOWN => "UNKNOWN" | .CONFLICT => "CONFLICT"

/-- Разбор имени истинностного значения. -/
def PT.ofWire (s : String) : Option PT :=
  if s = "TRUE_KNOWN" then some .TRUE_KNOWN else if s = "FALSE_KNOWN" then some .FALSE_KNOWN
  else if s = "UNKNOWN" then some .UNKNOWN else if s = "CONFLICT" then some .CONFLICT else none

/-- Имя вердикта. -/
def Verdict.wire : Verdict → String
  | .PASS => "PASS" | .REJECT => "REJECT" | .REPAIR => "REPAIR"
  | .UNDECIDABLE => "UNDECIDABLE"

/-- Разбор имени вердикта. -/
def Verdict.ofWire (s : String) : Option Verdict :=
  if s = "PASS" then some .PASS else if s = "REJECT" then some .REJECT
  else if s = "REPAIR" then some .REPAIR else if s = "UNDECIDABLE" then some .UNDECIDABLE
  else none

/-- Идентификатор закона строкой. -/
def LawId.wire : LawId → String
  | .LAW_001 => "LAW-001" | .LAW_002 => "LAW-002" | .LAW_003 => "LAW-003"
  | .LAW_004 => "LAW-004" | .LAW_005 => "LAW-005" | .LAW_006 => "LAW-006"
  | .LAW_007 => "LAW-007" | .LAW_008 => "LAW-008" | .LAW_009 => "LAW-009"
  | .LAW_010 => "LAW-010" | .LAW_011 => "LAW-011" | .LAW_012 => "LAW-012"
  | .LAW_013 => "LAW-013" | .LAW_014 => "LAW-014" | .LAW_015 => "LAW-015"
  | .LAW_016 => "LAW-016" | .LAW_017 => "LAW-017" | .LAW_018 => "LAW-018"

/-- Все идентификаторы законов списком. -/
def LawId.all : List LawId :=
  [.LAW_001, .LAW_002, .LAW_003, .LAW_004, .LAW_005, .LAW_006, .LAW_007,
   .LAW_008, .LAW_009, .LAW_010, .LAW_011, .LAW_012, .LAW_013, .LAW_014,
   .LAW_015, .LAW_016, .LAW_017, .LAW_018]

/-- Разбор идентификатора закона. -/
def LawId.ofWire (s : String) : Option LawId := LawId.all.find? (fun l => l.wire == s)

/-- Обратимость для истинностных значений — отдельной леммой (используется
при сериализации состояний). -/
theorem pt_wire_roundtrip : ∀ x : PT, PT.ofWire x.wire = some x := by decide

/-- Сериализация конечных осей обратима: по имени значение восстанавливается
однозначно. -/
theorem axes_roundtrip :
    (∀ x : Level, Level.ofWire x.wire = some x) ∧
    (∀ x : Phase, Phase.ofWire x.wire = some x) ∧
    (∀ x : Category, Category.ofWire x.wire = some x) ∧
    (∀ x : Role, Role.ofWire x.wire = some x) ∧
    (∀ x : EffectLevel, EffectLevel.ofWire x.wire = some x) ∧
    (∀ x : PT, PT.ofWire x.wire = some x) ∧
    (∀ x : Verdict, Verdict.ofWire x.wire = some x) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Сериализация идентификаторов законов обратима. -/
theorem lawId_roundtrip : ∀ l : LawId, LawId.ofWire l.wire = some l := by decide

/-- Имена законов различны: сериализация не склеивает законы. -/
theorem lawId_wire_injective : Function.Injective LawId.wire := by decide

/-! ### 2.2 Язык предикатов: постфиксная лента токенов -/

/-- Примитивный токен обменного формата предиката. -/
inductive PTok
  /-- Атомарный факт. -/
  | fact (f : FactId)
  /-- Отрицание. -/
  | tnot
  /-- Конъюнкция. -/
  | tand
  /-- Дизъюнкция. -/
  | tor
  /-- Импликация. -/
  | timp
  /-- Сравнение «не меньше». -/
  | tgte (v : VarName) (n : ℕ)
  /-- Сравнение на равенство. -/
  | teq (v : VarName) (n : ℕ)
  /-- Константа «истинно». -/
  | ttrue
  /-- Константа «ложно». -/
  | tfalse
  /-- Константа «нет информации». -/
  | tunknown
  deriving DecidableEq, Repr, Inhabited

/-- Сериализация предиката в постфиксную ленту токенов. -/
def encodePred : Pred → List PTok
  | .factExists f => [.fact f]
  | .pnot p => encodePred p ++ [.tnot]
  | .pand p q => encodePred p ++ encodePred q ++ [.tand]
  | .por p q => encodePred p ++ encodePred q ++ [.tor]
  | .pimp p q => encodePred p ++ encodePred q ++ [.timp]
  | .gte v n => [.tgte v n]
  | .peq v n => [.teq v n]
  | .ctrue => [.ttrue]
  | .cfalse => [.tfalse]
  | .cunknown => [.tunknown]

/-- Разбор ленты стековой машиной (структурная рекурсия по ленте). -/
def runStack : List PTok → List Pred → Option (List Pred)
  | [], st => some st
  | .fact f :: r, st => runStack r (.factExists f :: st)
  | .tnot :: r, p :: st => runStack r (.pnot p :: st)
  | .tand :: r, q :: p :: st => runStack r (.pand p q :: st)
  | .tor :: r, q :: p :: st => runStack r (.por p q :: st)
  | .timp :: r, q :: p :: st => runStack r (.pimp p q :: st)
  | .tgte v n :: r, st => runStack r (.gte v n :: st)
  | .teq v n :: r, st => runStack r (.peq v n :: st)
  | .ttrue :: r, st => runStack r (.ctrue :: st)
  | .tfalse :: r, st => runStack r (.cfalse :: st)
  | .tunknown :: r, st => runStack r (.cunknown :: st)
  | _, _ => none

/-- Разбор ленты в предикат. -/
def decodePred (l : List PTok) : Option Pred :=
  match runStack l [] with
  | some [p] => some p
  | _ => none

/-- Лента предиката, положенная перед любым продолжением, кладёт на стек в
точности исходный предикат. -/
theorem runStack_encodePred :
    ∀ (p : Pred) (rest : List PTok) (st : List Pred),
      runStack (encodePred p ++ rest) st = runStack rest (p :: st) := by
  intro p
  induction p with
  | factExists f => intro rest st; rfl
  | pnot p ih => intro rest st; simp only [encodePred, List.append_assoc, ih]; rfl
  | pand p q ihp ihq =>
      intro rest st
      simp only [encodePred, List.append_assoc, ihp, ihq]; rfl
  | por p q ihp ihq =>
      intro rest st
      simp only [encodePred, List.append_assoc, ihp, ihq]; rfl
  | pimp p q ihp ihq =>
      intro rest st
      simp only [encodePred, List.append_assoc, ihp, ihq]; rfl
  | gte v n => intro rest st; rfl
  | peq v n => intro rest st; rfl
  | ctrue => intro rest st; rfl
  | cfalse => intro rest st; rfl
  | cunknown => intro rest st; rfl

/-- **Сериализация предикатов точна.**  Разбор ленты возвращает исходный
предикат: обменный формат ничего не теряет и ничего не добавляет. -/
theorem pred_roundtrip (p : Pred) : decodePred (encodePred p) = some p := by
  have h := runStack_encodePred p [] []
  simp only [List.append_nil] at h
  simp [decodePred, h, runStack]

/-- Как следствие, сериализация предикатов инъективна. -/
theorem encodePred_injective : Function.Injective encodePred := by
  intro p q h
  have hp := pred_roundtrip p
  rw [h, pred_roundtrip q] at hp
  exact (Option.some.inj hp).symm

/-- Разбор списка лент. -/
def decodePreds : List (List PTok) → Option (List Pred)
  | [] => some []
  | l :: t =>
      match decodePred l, decodePreds t with
      | some p, some ps => some (p :: ps)
      | _, _ => none

/-- Сериализация списка предикатов (контракта оператора) точна. -/
theorem preds_roundtrip (ps : List Pred) : decodePreds (ps.map encodePred) = some ps := by
  induction ps with
  | nil => rfl
  | cons p t ih => simp [decodePreds, pred_roundtrip p, ih]

/-! ### 2.3 Операторы, состояния и цепочки -/

/-- Сериализованный оператор: только строки, числа, булевы значения и списки. -/
structure OpWire where
  /-- Имя оператора. -/
  name : String
  /-- Контракт в виде лент токенов. -/
  requires : List (List PTok)
  /-- Производимые факты. -/
  produces : List String
  /-- Потребляемые ресурсы. -/
  consumes : List String
  /-- Инвалидируемые предикаты. -/
  invalidates : List String
  /-- Изменяемые переменные. -/
  modifies : List String
  /-- Имя уровня эффекта. -/
  effect : String
  /-- Требуется ли авторизация. -/
  requiresAuth : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Сериализация оператора. -/
def opToWire (o : Op) : OpWire :=
  ⟨o.name, o.requires.map encodePred, o.produces, o.consumes, o.invalidates,
   o.modifies, o.effect.wire, o.requiresAuth⟩

/-- Восстановление оператора. -/
def wireToOp (w : OpWire) : Option Op :=
  match decodePreds w.requires, EffectLevel.ofWire w.effect with
  | some rs, some e =>
      some ⟨w.name, rs, w.produces, w.consumes, w.invalidates, w.modifies, e, w.requiresAuth⟩
  | _, _ => none

/-- **Сериализация операторов точна.** -/
theorem op_roundtrip (o : Op) : wireToOp (opToWire o) = some o := by
  cases o with
  | mk name requires produces consumes invalidates modifies effect requiresAuth =>
      have he : EffectLevel.ofWire (EffectLevel.wire effect) = some effect := by
        revert effect; decide
      simp [opToWire, wireToOp, preds_roundtrip, he]

/-- Сериализованное состояние ядра. -/
structure KStateWire where
  /-- Факты: имя и имя статуса. -/
  facts : List (String × String)
  /-- Переменные: имя и значение, если известно. -/
  vars : List (String × Option ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- Сериализация состояния. -/
def kstateToWire (s : KState) : KStateWire :=
  ⟨s.facts.map (fun p => (p.1, p.2.wire)), s.vars⟩

/-- Восстановление списка фактов. -/
def decodeFacts : List (String × String) → Option (List (FactId × PT))
  | [] => some []
  | (f, v) :: t =>
      match PT.ofWire v, decodeFacts t with
      | some x, some r => some ((f, x) :: r)
      | _, _ => none

/-- Восстановление состояния. -/
def wireToKState (w : KStateWire) : Option KState :=
  match decodeFacts w.facts with
  | some fs => some ⟨fs, w.vars⟩
  | none => none

/-- **Сериализация состояний точна.** -/
theorem kstate_roundtrip (s : KState) : wireToKState (kstateToWire s) = some s := by
  cases s with
  | mk facts vars =>
      have h : ∀ l : List (FactId × PT),
          decodeFacts (l.map (fun p => (p.1, p.2.wire))) = some l := by
        intro l
        induction l with
        | nil => rfl
        | cons p t ih =>
            simp [decodeFacts, pt_wire_roundtrip p.2, ih]
      simp [kstateToWire, wireToKState, h]

/-- Восстановление цепочки операторов. -/
def wireToChain : List OpWire → Option (List Op)
  | [] => some []
  | w :: t =>
      match wireToOp w, wireToChain t with
      | some o, some os => some (o :: os)
      | _, _ => none

/-- **Сериализация цепочек точна**: композиция, отданная наружу в обменном
формате, возвращается той же самой композицией. -/
theorem chain_roundtrip (ops : List Op) : wireToChain (ops.map opToWire) = some ops := by
  induction ops with
  | nil => rfl
  | cons o t ih => simp [wireToChain, op_roundtrip o, ih]

/-- Сериализация цепочек сохраняет вердикт компилятора: схема не может
«разойтись» с ядром, потому что восстанавливает ровно ту же цепочку. -/
theorem chain_wire_verdict (reg : List Op) (s : KState) (ops : List Op) (goal : Pred)
    (ops' : List Op) (h : wireToChain (ops.map opToWire) = some ops') :
    compile ⟨reg, s, ops', goal⟩ = compile ⟨reg, s, ops, goal⟩ := by
  rw [chain_roundtrip ops] at h
  rw [Option.some.inj h]

/-! ## 3. Каталог схемы: узлы ↔ понятия ядра -/

/-- Понятия ядра, подлежащие сериализации. -/
inductive KernelNotion
  /-- Пять ортогональных осей. -/
  | axes
  /-- Решётка типов. -/
  | typeLattice
  /-- Язык предикатов и его семантика. -/
  | predicates
  /-- Состояние ядра. -/
  | state
  /-- Операторы и их контракты. -/
  | operators
  /-- Обратный трансформер предикатов. -/
  | wpTransformer
  /-- Уровни и агрегация эффектов. -/
  | effects
  /-- Авторизация исполнения. -/
  | authorization
  /-- Алгебра слияния ветвей. -/
  | epistemicJoin
  /-- Алгебра идентичности. -/
  | identity
  /-- Оптимизатор ремонта. -/
  | repair
  /-- Вердикты компилятора. -/
  | verdicts
  /-- Законы ядра. -/
  | laws
  /-- Минимальный базисный набор проверок. -/
  | basis
  /-- Model check. -/
  | modelCheck
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Узел схемы: понятие ядра, его имя в обменном формате, поля и модуль-источник. -/
structure SchemaNode where
  /-- Сериализуемое понятие ядра. -/
  notion : KernelNotion
  /-- Имя узла в схеме. -/
  name : String
  /-- Поля узла. -/
  fields : List String
  /-- Модуль, в котором понятие определено математически. -/
  source : String
  deriving DecidableEq, Repr, Inhabited

/-- **Atlas S-1.0 Meta-Schema.**  Каждый узел — сериализация понятия,
определённого в ядре; поле `source` указывает, где именно оно определено. -/
def metaSchema : List SchemaNode :=
  [ ⟨.axes, "ArtifactType",
     ["category", "role", "level", "typeTag", "phase"], "OSA4/Axes.lean"⟩,
    ⟨.typeLattice, "TypeLattice", ["edges"], "OSA4/Axes.lean"⟩,
    ⟨.predicates, "Pred", ["tokens(postfix)"], "OSA4/Kernel.lean"⟩,
    ⟨.state, "KState", ["facts", "vars"], "OSA4/Kernel.lean"⟩,
    ⟨.operators, "Op",
     ["name", "requires", "produces", "consumes", "invalidates", "modifies",
      "effect", "requiresAuth"], "OSA4/Kernel.lean"⟩,
    ⟨.wpTransformer, "WP", ["operator", "postcondition"], "OSA4/Kernel.lean"⟩,
    ⟨.effects, "EffectLevel", ["level", "policy.maxLevel"], "OSA4/Effects.lean"⟩,
    ⟨.authorization, "Authorization", ["authFact", "authStatus"], "OSA4/Effects.lean"⟩,
    ⟨.epistemicJoin, "Belief", ["present", "absent", "isTrue", "isFalse"],
     "OSA4/Epistemic.lean"⟩,
    ⟨.identity, "Obj", ["id", "phase", "lineage"], "OSA4/Identity.lean"⟩,
    ⟨.repair, "RVec",
     ["safety", "obligations", "policy", "uncertainty", "cost"], "OSA4/Repair.lean"⟩,
    ⟨.verdicts, "Report", ["verdict", "error", "step"], "OSA4/Compiler.lean"⟩,
    ⟨.laws, "LawId", ["id", "title"], "OSA4/Lawbook.lean"⟩,
    ⟨.basis, "Coverage", ["law", "kind", "witness"], "OSA4/Basis.lean"⟩,
    ⟨.modelCheck, "ModelCheck", ["domain", "result"], "OSA4/ModelCheck.lean"⟩ ]

/-- Узлов ровно столько же, сколько понятий ядра. -/
theorem metaSchema_card : metaSchema.length = Fintype.card KernelNotion := by decide

/-- **Схема — точная сериализация ядра.**  Понятия узлов не повторяются и
покрывают все понятия ядра: нет ни узла без математического источника, ни
определения ядра без узла. -/
theorem metaSchema_bijective :
    (metaSchema.map SchemaNode.notion).Nodup ∧
    ∀ n : KernelNotion, n ∈ metaSchema.map SchemaNode.notion := by
  refine ⟨by decide, by decide⟩

/-- Каждый узел ссылается на модуль ядра, а не вводит понятие сам. -/
theorem metaSchema_sources_are_kernel_modules :
    ∀ nd ∈ metaSchema, nd.source ∈
      ["OSA4/Axes.lean", "OSA4/Kernel.lean", "OSA4/Effects.lean", "OSA4/Epistemic.lean",
       "OSA4/Identity.lean", "OSA4/Repair.lean", "OSA4/Compiler.lean", "OSA4/Lawbook.lean",
       "OSA4/Basis.lean", "OSA4/ModelCheck.lean"] := by
  decide

/-- **Итог §S-1.0.**  Шлюз открыт (ядро замкнуто), схема построена и является
сериализацией: перевод в обменный формат и обратно возвращает исходные
объекты ядра — предикаты, операторы, состояния и цепочки. -/
theorem metaSchema_is_faithful_serialization :
    KernelClosed ∧
    (∀ p : Pred, decodePred (encodePred p) = some p) ∧
    (∀ o : Op, wireToOp (opToWire o) = some o) ∧
    (∀ s : KState, wireToKState (kstateToWire s) = some s) ∧
    (∀ ops : List Op, wireToChain (ops.map opToWire) = some ops) ∧
    (metaSchema.map SchemaNode.notion).Nodup ∧
    (∀ n : KernelNotion, n ∈ metaSchema.map SchemaNode.notion) :=
  ⟨kernel_v04_closed, pred_roundtrip, op_roundtrip, kstate_roundtrip, chain_roundtrip,
   metaSchema_bijective.1, metaSchema_bijective.2⟩

end Polymath.OSA4
