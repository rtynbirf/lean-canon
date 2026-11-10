/-
# OSA-4.0 — пространство инвариантов

В ядре OSA-4.0 термин «инвариант» использовался только как имя кода ошибки
`E_INVARIANT_VIOLATION` компилятора и не имел определения.  Здесь он
определён формально и снабжён доказанными свойствами:

* `Invariant` — структура (имя и предикат языка `Pred`);
* `Invariant.holdsIn` — выполнение инварианта в состоянии (разрешимо);
* `Op.preserves` — сохранение инварианта оператором;
* `preserves_iff_wp` — критерий сохранения через обратный трансформер
  предикатов: сохранение эквивалентно импликации `I ⊑ wp(o, I)`;
* `execChain_preserves` — сохранение инварианта композицией;
* `chainViolation` — вычислимый детектор первого нарушения вдоль цепочки,
  доказанно корректный и полный (`chainViolation_eq_none_iff`);
* `singleConsumption` — формальное содержание кода `E_INVARIANT_VIOLATION`
  (однократность потребления ресурса), доказанное для вердикта `PASS`.
-/
import RequestProject.OSA4.Compiler

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-! ## Инвариант -/

/-- Инвариант ядра: именованный предикат языка `Pred`, который обязан
оставаться доказанным во всех состояниях рассматриваемого исполнения. -/
structure Invariant where
  /-- Идентификатор инварианта. -/
  name : String
  /-- Условие инварианта. -/
  cond : Pred
  deriving DecidableEq, Repr, Inhabited

namespace Invariant

/-- Инвариант выполнен в состоянии, если его условие доказанно истинно
(значение `UNKNOWN` или `CONFLICT` выполнением не считается). -/
def holdsIn (I : Invariant) (s : KState) : Prop := eval s I.cond = .TRUE_KNOWN

instance (I : Invariant) (s : KState) : Decidable (I.holdsIn s) := by
  unfold holdsIn; infer_instance

/-- Булев тест выполнения инварианта. -/
def check (I : Invariant) (s : KState) : Bool := eval s I.cond == .TRUE_KNOWN

@[simp] theorem check_eq_true_iff (I : Invariant) (s : KState) :
    I.check s = true ↔ I.holdsIn s := by
  simp [check, holdsIn]

end Invariant

/-! ## Сохранение инварианта оператором -/

/-- Оператор сохраняет инвариант, если из выполнения инварианта до исполнения
следует его выполнение после. -/
def Op.preserves (o : Op) (I : Invariant) : Prop :=
  ∀ s : KState, I.holdsIn s → I.holdsIn (o.exec s)

/-- **Критерий сохранения через WP.**  Оператор сохраняет инвариант тогда и
только тогда, когда условие инварианта влечёт свой WP-образ. -/
theorem preserves_iff_wp (o : Op) (I : Invariant) :
    o.preserves I ↔
      ∀ s : KState, eval s I.cond = .TRUE_KNOWN → eval s (wp o I.cond) = .TRUE_KNOWN := by
  unfold Op.preserves Invariant.holdsIn
  constructor
  · intro h s hs; rw [← eval_exec_eq_eval_wp]; exact h s hs
  · intro h s hs; rw [eval_exec_eq_eval_wp]; exact h s hs

/-- Инвариант, не упоминающий ни одного изменяемого оператором факта или
переменной, сохраняется этим оператором.  Синтаксический достаточный
критерий: WP-образ совпадает с самим условием. -/
theorem preserves_of_wp_eq (o : Op) (I : Invariant) (h : wp o I.cond = I.cond) :
    o.preserves I := by
  rw [preserves_iff_wp]
  intro s hs
  rw [h]; exact hs

/-- Сохранение инварианта замкнуто относительно композиции двух операторов. -/
theorem preserves_comp {a b : Op} {I : Invariant}
    (ha : a.preserves I) (hb : b.preserves I) :
    ∀ s : KState, I.holdsIn s → I.holdsIn (b.exec (a.exec s)) :=
  fun s hs => hb _ (ha s hs)

/-- Сохранение инварианта каждым оператором цепочки влечёт его сохранение
всей цепочкой. -/
theorem execChain_preserves (I : Invariant) :
    ∀ (ops : List Op), (∀ o ∈ ops, o.preserves I) →
      ∀ s : KState, I.holdsIn s → I.holdsIn (execChain ops s) := by
  intro ops
  induction ops with
  | nil => intro _ s hs; simpa using hs
  | cons o t ih =>
      intro h s hs
      rw [execChain_cons]
      exact ih (fun r hr => h r (by simp [hr])) _ (h o (by simp) s hs)

/-! ## Наборы инвариантов и детектор нарушений -/

/-- Все инварианты набора выполнены в состоянии. -/
def InvSet.holdsIn (Is : List Invariant) (s : KState) : Prop := ∀ I ∈ Is, I.holdsIn s

instance (Is : List Invariant) (s : KState) : Decidable (InvSet.holdsIn Is s) := by
  unfold InvSet.holdsIn; infer_instance

/-- Первый нарушенный инвариант набора в данном состоянии. -/
def violation (Is : List Invariant) (s : KState) : Option String :=
  (Is.find? (fun I => !I.check s)).map Invariant.name

/-- Детектор нарушения корректен и полон: он молчит тогда и только тогда,
когда выполнены все инварианты набора. -/
theorem violation_eq_none_iff (Is : List Invariant) (s : KState) :
    violation Is s = none ↔ InvSet.holdsIn Is s := by
  simp only [violation, InvSet.holdsIn, Option.map_eq_none_iff, List.find?_eq_none,
    Bool.not_eq_true, Bool.not_eq_false', Invariant.check_eq_true_iff]

/-- Состояния, проходимые цепочкой после каждого шага. -/
def statesAfter : List Op → KState → List KState
  | [], _ => []
  | o :: t, s => o.exec s :: statesAfter t (o.exec s)

/-- Первое нарушение инварианта вдоль цепочки: имя оператора и имя
нарушенного инварианта. -/
def chainViolation (Is : List Invariant) : List Op → KState → Option (String × String)
  | [], _ => none
  | o :: t, s =>
      match violation Is (o.exec s) with
      | some inv => some (o.name, inv)
      | none => chainViolation Is t (o.exec s)

/-- **Корректность и полнота детектора.**  Нарушений вдоль цепочки нет тогда
и только тогда, когда все инварианты выполнены в каждом промежуточном
состоянии. -/
theorem chainViolation_eq_none_iff (Is : List Invariant) :
    ∀ (ops : List Op) (s : KState),
      chainViolation Is ops s = none ↔ ∀ t ∈ statesAfter ops s, InvSet.holdsIn Is t := by
  intro ops
  induction ops with
  | nil => intro s; simp [chainViolation, statesAfter]
  | cons o t ih =>
      intro s
      rcases hv : violation Is (o.exec s) with _ | inv
      · have hhold : InvSet.holdsIn Is (o.exec s) := (violation_eq_none_iff Is _).1 hv
        simp only [chainViolation, hv, statesAfter, List.mem_cons]
        rw [ih (o.exec s)]
        constructor
        · rintro h u (rfl | hu)
          · exact hhold
          · exact h u hu
        · intro h u hu; exact h u (Or.inr hu)
      · have hbad : ¬ InvSet.holdsIn Is (o.exec s) := by
          intro hc
          rw [(violation_eq_none_iff Is _).2 hc] at hv
          simp at hv
        simp only [chainViolation, hv, statesAfter, List.mem_cons]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h; exact absurd (h _ (Or.inl rfl)) hbad

/-- Если каждый оператор цепочки сохраняет каждый инвариант набора и все
инварианты выполнены в начальном состоянии, детектор нарушений молчит. -/
theorem chainViolation_none_of_preserves (Is : List Invariant) :
    ∀ (ops : List Op) (s : KState),
      (∀ o ∈ ops, ∀ I ∈ Is, o.preserves I) → InvSet.holdsIn Is s →
        chainViolation Is ops s = none := by
  intro ops
  induction ops with
  | nil => intro s _ _; rfl
  | cons o t ih =>
      intro s hpres hinit
      have hstep : InvSet.holdsIn Is (o.exec s) :=
        fun I hI => hpres o (by simp) I hI s (hinit I hI)
      have hv : violation Is (o.exec s) = none := (violation_eq_none_iff Is _).2 hstep
      simp only [chainViolation, hv]
      exact ih (o.exec s) (fun r hr => hpres r (by simp [hr])) hstep

/-! ## Инвариант однократного потребления -/

/-- **Формальное содержание кода `E_INVARIANT_VIOLATION`.**  Ни один ресурс
не потребляется дважды без повторного порождения. -/
def singleConsumption (ops : List Op) : Prop := doubleConsume [] ops = none

instance (ops : List Op) : Decidable (singleConsumption ops) := by
  unfold singleConsumption; infer_instance

/-- Вердикт `PASS` влечёт однократность потребления. -/
theorem pass_singleConsumption (sc : Scenario) (h : (compile sc).verdict = .PASS) :
    singleConsumption sc.chain :=
  pass_no_double_consume sc h

/-- Обратно: нарушение однократности потребления при известных операторах
даёт `REJECT` с кодом `E_INVARIANT_VIOLATION`. -/
theorem doubleConsume_rejects (sc : Scenario)
    (hreg : unknownOperator sc.registry sc.chain = none)
    (hdc : ¬ singleConsumption sc.chain) :
    (compile sc).verdict = .REJECT ∧ (compile sc).error = some .E_INVARIANT_VIOLATION := by
  unfold singleConsumption at hdc
  rcases hd : doubleConsume [] sc.chain with _ | n
  · exact absurd hd hdc
  · constructor <;> simp [compile, hreg, hd]

end Polymath.OSA4
