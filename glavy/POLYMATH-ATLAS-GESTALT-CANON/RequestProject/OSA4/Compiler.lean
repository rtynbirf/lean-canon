/-
# OSA-4.0 — компилятор цепочек: вердикт вычислением

Формализация семантики вердиктов ядра v0.2/v0.4 (§8 Full Unified Codex):

    any FALSE                      → REJECT
    all TRUE                       → PASS
    valid repair (no Unknown)      → REPAIR
    repair exists but has Unknown  → UNDECIDABLE

плюс структурные проверки, которые нельзя свести к эпистемической оценке:
анализ живучести предикатов (LAW-006), запрет повторного потребления
(LAW-005) и реестр операторов.  Все проверки вычислимы, поэтому вердикт
конкретного сценария получается вычислением, а не декларацией.
-/
import RequestProject.OSA4.Repair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-- Атомарные факты, встречающиеся в предикате. -/
def Pred.factIds : Pred → List FactId
  | .factExists f => [f]
  | .pnot p => p.factIds
  | .pand p q => p.factIds ++ q.factIds
  | .por p q => p.factIds ++ q.factIds
  | .pimp p q => p.factIds ++ q.factIds
  | .gte _ _ => []
  | .peq _ _ => []
  | .ctrue => []
  | .cfalse => []
  | .cunknown => []

/-- Коды ошибок компилятора. -/
inductive ErrCode
  /-- Оператора нет в реестре. -/
  | E_UNKNOWN_OPERATOR
  /-- Уничтожен факт, нужный продолжению. -/
  | E_LIVENESS_VIOLATION
  /-- Нарушен инвариант (например, повторное потребление). -/
  | E_INVARIANT_VIOLATION
  /-- Предусловие доказанно ложно или противоречиво. -/
  | E_PRECONDITION_FALSE
  /-- Авторизация доказанно отсутствует. -/
  | E_AUTH_DENIED
  /-- Цель доказанно не достигается. -/
  | E_GOAL_FALSE
  deriving DecidableEq, Repr, Inhabited

/-- Отчёт компилятора. -/
structure Report where
  /-- Вердикт. -/
  verdict : Verdict
  /-- Код ошибки, если есть. -/
  error : Option ErrCode
  /-- Оператор, на котором проверка не прошла. -/
  step : Option String
  deriving DecidableEq, Repr, Inhabited

/-- Сценарий: реестр операторов, начальное состояние, цепочка и цель. -/
structure Scenario where
  /-- Реестр известных операторов. -/
  registry : List Op
  /-- Начальное состояние. -/
  init : KState
  /-- Цепочка операторов. -/
  chain : List Op
  /-- Требование продолжения (LIVE_OUT). -/
  goal : Pred

/-! ## Проверка реестра -/

/-- Первый оператор цепочки, отсутствующий в реестре. -/
def unknownOperator (reg : List Op) : List Op → Option String
  | [] => none
  | o :: t => if reg.any (fun r => r.name == o.name) then unknownOperator reg t else some o.name

/-! ## Анализ живучести (LAW-006) -/

/-- Обратный проход: возвращает имя оператора, уничтожающего факт, нужный
продолжению, и множество фактов, живых перед цепочкой. -/
def liveWalk (goal : Pred) : List Op → Option String × List FactId
  | [] => (none, goal.factIds)
  | o :: t =>
      let (err, live) := liveWalk goal t
      let liveBefore :=
        live.filter (fun f => !o.produces.contains f) ++ o.requires.flatMap Pred.factIds
      if err.isSome then (err, liveBefore)
      else if o.kill.any (fun f => live.contains f) then (some o.name, liveBefore)
      else (none, liveBefore)

/-- Нарушение живучести в цепочке, если оно есть. -/
def livenessViolation (goal : Pred) (ops : List Op) : Option String :=
  (liveWalk goal ops).1

/-! ## Инвариант однократного потребления (LAW-005) -/

/-- Повторное потребление уже потреблённого ресурса. -/
def doubleConsume : List FactId → List Op → Option String
  | _, [] => none
  | gone, o :: t =>
      if o.consumes.any (fun f => gone.contains f) then some o.name
      else doubleConsume (gone.filter (fun f => !o.produces.contains f) ++ o.consumes) t

/-! ## Эпистемический проход -/

/-- Существует ли в реестре оператор, после исполнения которого предикат
становится доказанным. -/
def repairFor (reg : List Op) (s : KState) (q : Pred) : Bool :=
  reg.any (fun r => eval (r.exec s) q == .TRUE_KNOWN)

/-- Существует ли в реестре оператор, выдающий токен авторизации. -/
def authorizerFor (reg : List Op) (o : Op) : Bool :=
  reg.any (fun r => r.produces.contains (authFact o))

/-- Прямой проход по цепочке с вычислением вердикта. -/
def epiPass (reg : List Op) : List Op → KState → Pred → Report
  | [], s, goal =>
      match eval s goal with
      | .TRUE_KNOWN => ⟨.PASS, none, none⟩
      | .FALSE_KNOWN => ⟨.REJECT, some .E_GOAL_FALSE, none⟩
      | .CONFLICT => ⟨.REJECT, some .E_GOAL_FALSE, none⟩
      | .UNKNOWN => ⟨.UNDECIDABLE, none, none⟩
  | o :: t, s, goal =>
      match eval s (conj o.requires) with
      | .FALSE_KNOWN => ⟨.REJECT, some .E_PRECONDITION_FALSE, some o.name⟩
      | .CONFLICT => ⟨.REJECT, some .E_PRECONDITION_FALSE, some o.name⟩
      | .UNKNOWN =>
          if repairFor reg s (conj o.requires) then ⟨.REPAIR, none, some o.name⟩
          else ⟨.UNDECIDABLE, none, some o.name⟩
      | .TRUE_KNOWN =>
          match authStatus s o with
          | .TRUE_KNOWN => epiPass reg t (o.exec s) goal
          | .FALSE_KNOWN => ⟨.REJECT, some .E_AUTH_DENIED, some o.name⟩
          | .CONFLICT => ⟨.REJECT, some .E_AUTH_DENIED, some o.name⟩
          | .UNKNOWN =>
              if authorizerFor reg o then ⟨.REPAIR, none, some o.name⟩
              else ⟨.UNDECIDABLE, none, some o.name⟩

/-- Компиляция сценария: реестр → инвариант потребления → живучесть →
эпистемический проход. -/
def compile (sc : Scenario) : Report :=
  match unknownOperator sc.registry sc.chain with
  | some n => ⟨.REJECT, some .E_UNKNOWN_OPERATOR, some n⟩
  | none =>
    match doubleConsume [] sc.chain with
    | some n => ⟨.REJECT, some .E_INVARIANT_VIOLATION, some n⟩
    | none =>
      match livenessViolation sc.goal sc.chain with
      | some n => ⟨.REJECT, some .E_LIVENESS_VIOLATION, some n⟩
      | none => epiPass sc.registry sc.chain sc.init sc.goal

/-! ## Общие свойства компилятора -/

/-- Компилятор всегда выдаёт ровно один вердикт (тотальность). -/
theorem compile_total (sc : Scenario) :
    (compile sc).verdict = .PASS ∨ (compile sc).verdict = .REJECT ∨
    (compile sc).verdict = .REPAIR ∨ (compile sc).verdict = .UNDECIDABLE := by
  rcases h : (compile sc).verdict with _ | _ | _ | _
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- Эпистемический проход не отвергает молча. -/
theorem epiPass_reject_has_code (reg : List Op) :
    ∀ (ops : List Op) (s : KState) (goal : Pred),
      (epiPass reg ops s goal).verdict = .REJECT →
        (epiPass reg ops s goal).error.isSome := by
  intro ops
  induction ops with
  | nil =>
      intro s goal h
      simp only [epiPass] at h ⊢
      split at h <;> simp_all
  | cons o t ih =>
      intro s goal h
      simp only [epiPass] at h ⊢
      split at h <;>
        first
          | simp_all
          | (split at h <;>
              first
                | exact ih _ _ h
                | simp_all
                | (split at h <;> simp_all))

/-- Всякий REJECT снабжён кодом ошибки: компилятор не отвергает молча. -/
theorem reject_has_code (sc : Scenario) :
    (compile sc).verdict = .REJECT → (compile sc).error.isSome := by
  unfold compile
  split
  · intro _; simp
  · split
    · intro _; simp
    · split
      · intro _; simp
      · exact epiPass_reject_has_code _ _ _ _

/-- PASS означает, что все структурные проверки пройдены: неизвестных
операторов нет. -/
theorem pass_no_unknown_operator (sc : Scenario) (h : (compile sc).verdict = .PASS) :
    unknownOperator sc.registry sc.chain = none := by
  cases hu : unknownOperator sc.registry sc.chain with
  | none => rfl
  | some n => rw [compile, hu] at h; exact absurd h (by simp)

/-- PASS означает, что повторного потребления в цепочке нет. -/
theorem pass_no_double_consume (sc : Scenario) (h : (compile sc).verdict = .PASS) :
    doubleConsume [] sc.chain = none := by
  have hu := pass_no_unknown_operator sc h
  cases hd : doubleConsume [] sc.chain with
  | none => rfl
  | some n =>
      rw [compile, hu, hd] at h
      exact absurd h (by simp)

/-- PASS означает, что живучесть не нарушена (LAW-006). -/
theorem pass_no_liveness_violation (sc : Scenario) (h : (compile sc).verdict = .PASS) :
    livenessViolation sc.goal sc.chain = none := by
  have hu := pass_no_unknown_operator sc h
  have hd := pass_no_double_consume sc h
  cases hl : livenessViolation sc.goal sc.chain with
  | none => rfl
  | some n =>
      rw [compile, hu, hd, hl] at h
      exact absurd h (by simp)

/-- Пустая цепочка с доказанной целью даёт PASS. -/
theorem compile_nil_pass (reg : List Op) (s : KState) (goal : Pred)
    (h : eval s goal = .TRUE_KNOWN) :
    compile ⟨reg, s, [], goal⟩ = ⟨.PASS, none, none⟩ := by
  simp [compile, unknownOperator, doubleConsume, livenessViolation, liveWalk,
    epiPass, h]

end Polymath.OSA4
