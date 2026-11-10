/-
# OSA-3.2 — интерактивная сессия (§14)

Пользователь строит композицию пошагово, компилятор проверяет каждый стык
в реальном времени:

```
  >> add MEASURE      ✓ OK
  >> add CALIBRATE    ✓ OK
  >> add DELETE       ✗ REJECT / E_INVARIANT_VIOLATION
  >> rollback         ✓ Reverted to CALIBRATE
  >> add MODEL        ✓ OK
```

Состояние сессии — `registry`, `currentOps`, `currentState`, `history`
(§14).  Ключевое отличие от однократной компиляции: незавершённая цепочка
не обязана проходить эпистемический уровень L4 — порог применяется к
*результату* композиции.  Поэтому шаг считается принятым (`stepOk`), если
пройдены уровни L1–L3, а сессия завершена успешно (`accepted`), если полный
вердикт равен `PASS`.

Доказано: `rollback` в точности отменяет `add`, состояние сессии всегда
равно вердикту компилятора для текущей цепочки, история растёт на один шаг
за операцию, и приведённый выше протокол §14 воспроизводится вычислением.
-/
import RequestProject.OSA.Gold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

/-! ## Состояние сессии -/

/-- Интерактивная сессия §14. -/
structure InteractiveSession where
  /-- Реестр доступных операторов. -/
  registry : List Operator
  /-- Контекст композиции (начальный тип, факты, инварианты, политика). -/
  base : Composition
  /-- Текущая цепочка. -/
  currentOps : List Operator
  /-- Последний отчёт компилятора. -/
  currentState : Report
  /-- История: цепочка и отчёт на каждом шаге, для отката. -/
  history : List (List Operator × Report)
  deriving Inhabited

/-- Композиция, отвечающая текущей цепочке сессии. -/
def InteractiveSession.composition (s : InteractiveSession) : Composition :=
  { s.base with ops := s.currentOps }

/-- Отчёт компилятора для текущей цепочки. -/
def InteractiveSession.recompile (s : InteractiveSession) : Report :=
  compile s.registry s.composition

/-- Начало сессии: пустая цепочка. -/
def InteractiveSession.start (reg : List Operator) (base : Composition) :
    InteractiveSession :=
  let s : InteractiveSession :=
    { registry := reg, base := base, currentOps := [], currentState := default
    , history := [] }
  { s with currentState := s.recompile }

/-- `>> add OP`: добавление оператора в конец цепочки с немедленной
перекомпиляцией; предыдущее состояние уходит в историю. -/
def InteractiveSession.add (s : InteractiveSession) (o : Operator) :
    InteractiveSession :=
  let s' : InteractiveSession :=
    { s with currentOps := s.currentOps ++ [o]
           , history := (s.currentOps, s.currentState) :: s.history }
  { s' with currentState := s'.recompile }

/-- `>> rollback`: возврат к предыдущему состоянию. -/
def InteractiveSession.rollback (s : InteractiveSession) : InteractiveSession :=
  match s.history with
  | [] => s
  | (ops, rep) :: rest =>
      { s with currentOps := ops, currentState := rep, history := rest }

/-- Шаг принят: пройдены уровни L1–L3.  Эпистемический порог L4 относится
к результату всей композиции и на незавершённой цепочке не применяется. -/
def InteractiveSession.stepOk (s : InteractiveSession) : Bool :=
  s.currentState.l1 && s.currentState.l2 && s.currentState.l3

/-- Сессия завершена успешно: полный вердикт `PASS`. -/
def InteractiveSession.accepted (s : InteractiveSession) : Bool :=
  s.currentState.status == Status.PASS

/-- Ответ сессии на шаг в формате §14. -/
def InteractiveSession.line (s : InteractiveSession) : String :=
  if s.stepOk then "OK"
  else "REJECT / " ++ s.currentState.code.toCodeString ++
       (if s.currentState.suggestion == "" then ""
        else "\n    Suggestion: " ++ s.currentState.suggestion)

/-! ## Свойства сессии -/

/-- Состояние сессии согласовано: `currentState` — это вердикт компилятора
для текущей цепочки. -/
def InteractiveSession.consistent (s : InteractiveSession) : Prop :=
  s.currentState = s.recompile

/-- Начальная сессия согласована. -/
theorem start_consistent (reg : List Operator) (base : Composition) :
    (InteractiveSession.start reg base).consistent := rfl

/-- `add` сохраняет согласованность состояния. -/
theorem add_consistent (s : InteractiveSession) (o : Operator) :
    (s.add o).consistent := rfl

/-- `add` дописывает оператор в конец цепочки. -/
theorem add_ops (s : InteractiveSession) (o : Operator) :
    (s.add o).currentOps = s.currentOps ++ [o] := rfl

/-- `add` удлиняет историю ровно на один шаг. -/
theorem add_history_length (s : InteractiveSession) (o : Operator) :
    (s.add o).history.length = s.history.length + 1 := rfl

/-- **`rollback` в точности отменяет `add`**: откат возвращает исходное
состояние целиком — вместе с цепочкой, отчётом и историей. -/
theorem rollback_add (s : InteractiveSession) (o : Operator) :
    (s.add o).rollback = s := rfl

/-- Откат из пустой истории оставляет сессию неизменной. -/
theorem rollback_empty (s : InteractiveSession) (h : s.history = []) :
    s.rollback = s := by
  unfold InteractiveSession.rollback
  rw [h]

/-- Откат сохраняет согласованность, если согласовано записанное в историю
состояние. -/
theorem rollback_consistent (s : InteractiveSession) (hs : s.consistent)
    (h : ∀ p ∈ s.history, p.2 = compile s.registry { s.base with ops := p.1 }) :
    s.rollback.consistent := by
  unfold InteractiveSession.consistent InteractiveSession.rollback
  cases hh : s.history with
  | nil => exact hs
  | cons p rest =>
      have hp := h p (by simp [hh])
      simpa [InteractiveSession.recompile, InteractiveSession.composition] using hp

/-- Принятая сессия проходит все четыре уровня корректности (§9, §19.4). -/
theorem accepted_four_levels (s : InteractiveSession) (hs : s.consistent)
    (h : s.accepted = true) :
    s.currentState.l1 = true ∧ s.currentState.l2 = true ∧
    s.currentState.l3 = true ∧ s.currentState.l4 = true := by
  have hst : s.currentState.status = Status.PASS := by
    simpa [InteractiveSession.accepted] using h
  rw [hs] at hst ⊢
  exact (compile_status_pass_iff s.registry s.composition).mp hst

/-- Принятая сессия непуста лишь при выполнении всех контрактов: если она
принята, то каждый оператор цепочки принимает приходящий на его вход
тип. -/
theorem accepted_types (s : InteractiveSession) (hs : s.consistent)
    (h : s.accepted = true)
    (pre : List Operator) (o : Operator) (suf : List Operator)
    (hops : s.currentOps = pre ++ o :: suf) :
    typeCompatible (outAfter s.base.initialType pre) o.inputType = true := by
  have hst : (compile s.registry s.composition).status = Status.PASS := by
    have : s.currentState.status = Status.PASS := by
      simpa [InteractiveSession.accepted] using h
    rwa [hs] at this
  have hnone : diagL1 s.registry s.composition = none :=
    ((firstFailure_eq_none_iff _ _).mp ((compile_pass_iff_no_failure _ _).mp hst)).1
  rw [diagL1] at hnone
  have hops' : s.composition.ops = pre ++ o :: suf := hops
  rw [hops'] at hnone
  exact typeDiag_none_at _ pre o suf _ hnone

/-! ## Протокол §14, воспроизведённый вычислением -/

/-- Сессия из примера §14: канонический инженерный контекст. -/
def demoSession : InteractiveSession :=
  InteractiveSession.start goldRegistry { goldBase with caseId := "interactive demo" }

/-- Шаг 1: `add MEASURE` — принят. -/
theorem demo_step1 : (demoSession.add MEASURE).stepOk = true := by decide

/-- Шаг 2: `add CALIBRATE` — принят. -/
theorem demo_step2 :
    ((demoSession.add MEASURE).add CALIBRATE).stepOk = true := by decide

/-- Шаг 3: `add DELETE` — отвергнут с кодом `E_INVARIANT_VIOLATION`:
композиция в целом уничтожает инвариант `DataExistence`, объявленный
обязательным. -/
theorem demo_step3 :
    (((demoSession.add MEASURE).add CALIBRATE).add DELETE).stepOk = false ∧
    (((demoSession.add MEASURE).add CALIBRATE).add DELETE).currentState.code =
      ErrCode.E_INVARIANT_VIOLATION := by decide

/-- Шаг 4: `rollback` — возврат ровно к состоянию после CALIBRATE. -/
theorem demo_step4 :
    ((((demoSession.add MEASURE).add CALIBRATE).add DELETE).rollback) =
      ((demoSession.add MEASURE).add CALIBRATE) :=
  rollback_add _ DELETE

/-- Шаг 5: `add MODEL` — принят. -/
theorem demo_step5 :
    (((((demoSession.add MEASURE).add CALIBRATE).add DELETE).rollback).add MODEL).stepOk
      = true := by decide

/-- Печать протокола §14. -/
def demoTranscript : String :=
  let s1 := demoSession.add MEASURE
  let s2 := s1.add CALIBRATE
  let s3 := s2.add DELETE
  let s4 := s3.rollback
  let s5 := s4.add MODEL
  ">> add MEASURE\n  " ++ s1.line ++
  "\n>> add CALIBRATE\n  " ++ s2.line ++
  "\n>> add DELETE\n  " ++ s3.line ++
  "\n>> rollback\n  Reverted to " ++
    (match s4.currentOps.getLast? with | some o => o.id | none => "<empty>") ++
  "\n>> add MODEL\n  " ++ s5.line

#eval IO.println demoTranscript

end Polymath.OSA
