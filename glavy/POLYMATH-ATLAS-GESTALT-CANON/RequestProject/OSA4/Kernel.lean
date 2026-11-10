/-
# OSA-4.0 — семантическое ядро v0.4: предикаты, состояние, операторы, WP

Формализация §5.1–§5.4 / §7–§11 кодекса OSA-4.0:

* язык предикатов `Pred` (FactExists, Not, And, Or, Implies, Gte, Eq) и его
  четырёхзначная семантика `PT` (TRUE_KNOWN / FALSE_KNOWN / UNKNOWN / CONFLICT);
* состояние `KState` (факты, переменные) с ключевым правилом кодекса:
  «если X просто отсутствует в state-map, `DataExists(X) = UNKNOWN`,
  а не `FALSE_KNOWN`»;
* оператор `Op` с вектором эффектов (produces / consumes / invalidates /
  modifies / requires) и исполнением `exec`;
* **обратный трансформер предикатов WP** — замена теоретико-множественного
  вычитания FactID, при котором ядро v0.2 не давало точной характеризации
  предикатов после исполнения:
  `wp` определён синтаксически, и доказано точное соответствие
  `eval (exec o s) q = eval s (wp o q)` (`eval_exec_eq_eval_wp`), откуда
  LAW-012 (Predicate Transformer Soundness) следует как частный случай.

Здесь же доказываются LAW-003 (State Conservation), LAW-006 (Destroy /
Predicate Liveness Safety), LAW-017 (Predicate Invalidation Soundness:
инвалидация *не* доказывает отрицание) и композиционность WP.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace Polymath.OSA4

/-! ## Четырёхзначная истинность предиката -/

/-- Истинностное значение предиката в состоянии (`ABSENT` сюда намеренно не
входит: присутствие ресурса — отдельное пространство, см. `Epistemic.lean`). -/
inductive PT
  | TRUE_KNOWN | FALSE_KNOWN | UNKNOWN | CONFLICT
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace PT

/-- Отрицание: `UNKNOWN` и `CONFLICT` — неподвижные точки. -/
def neg : PT → PT
  | .TRUE_KNOWN => .FALSE_KNOWN
  | .FALSE_KNOWN => .TRUE_KNOWN
  | .UNKNOWN => .UNKNOWN
  | .CONFLICT => .CONFLICT

/-- Конъюнкция: доказанная ложь поглощает, затем противоречие, затем незнание. -/
def and : PT → PT → PT
  | .FALSE_KNOWN, _ => .FALSE_KNOWN
  | _, .FALSE_KNOWN => .FALSE_KNOWN
  | .CONFLICT, _ => .CONFLICT
  | _, .CONFLICT => .CONFLICT
  | .UNKNOWN, _ => .UNKNOWN
  | _, .UNKNOWN => .UNKNOWN
  | .TRUE_KNOWN, .TRUE_KNOWN => .TRUE_KNOWN

/-- Дизъюнкция: доказанная истина поглощает, затем противоречие, затем незнание. -/
def or : PT → PT → PT
  | .TRUE_KNOWN, _ => .TRUE_KNOWN
  | _, .TRUE_KNOWN => .TRUE_KNOWN
  | .CONFLICT, _ => .CONFLICT
  | _, .CONFLICT => .CONFLICT
  | .UNKNOWN, _ => .UNKNOWN
  | _, .UNKNOWN => .UNKNOWN
  | .FALSE_KNOWN, .FALSE_KNOWN => .FALSE_KNOWN

/-- Импликация. -/
def imp (a b : PT) : PT := or (neg a) b

@[simp] theorem neg_neg (a : PT) : neg (neg a) = a := by cases a <;> rfl

theorem and_comm' (a b : PT) : and a b = and b a := by revert a b; decide

theorem or_comm' (a b : PT) : or a b = or b a := by revert a b; decide

theorem and_assoc' (a b c : PT) : and (and a b) c = and a (and b c) := by
  revert a b c; decide

theorem or_assoc' (a b c : PT) : or (or a b) c = or a (or b c) := by
  revert a b c; decide

theorem and_idem (a : PT) : and a a = a := by cases a <;> rfl

theorem or_idem (a : PT) : or a a = a := by cases a <;> rfl

/-- Де Морган. -/
theorem neg_and (a b : PT) : neg (and a b) = or (neg a) (neg b) := by
  revert a b; decide

/-- Де Морган (двойственная форма). -/
theorem neg_or (a b : PT) : neg (or a b) = and (neg a) (neg b) := by
  revert a b; decide

/-- Конъюнкция истинна только если истинны оба конъюнкта: недостаток данных
не может быть «замаскирован» под доказательство. -/
theorem and_eq_true_iff (a b : PT) :
    and a b = .TRUE_KNOWN ↔ a = .TRUE_KNOWN ∧ b = .TRUE_KNOWN := by
  revert a b; decide

end PT

/-! ## Состояние -/

/-- Идентификатор факта. -/
abbrev FactId := String

/-- Имя переменной состояния. -/
abbrev VarName := String

/-- Состояние ядра: эпистемический статус атомарных фактов и значения
переменных.  Обе компоненты — частичные отображения. -/
structure KState where
  /-- Известный статус атомарных фактов. -/
  facts : List (FactId × PT)
  /-- Известные значения переменных состояния (`none` — значение забыто). -/
  vars : List (VarName × Option ℕ)
  deriving Repr, Inhabited

namespace KState

/-- Статус факта: **отсутствие записи даёт `UNKNOWN`, а не `FALSE_KNOWN`**
(ключевое требование кодекса, тест T05). -/
def factStatus (s : KState) (f : FactId) : PT :=
  match s.facts.find? (fun p => p.1 == f) with
  | some p => p.2
  | none => .UNKNOWN

/-- Значение переменной, если оно известно. -/
def varValue (s : KState) (v : VarName) : Option ℕ :=
  match s.vars.find? (fun p => p.1 == v) with
  | some p => p.2
  | none => none

/-- Установить статус факта (последняя запись перекрывает предыдущие). -/
def setFact (s : KState) (f : FactId) (v : PT) : KState :=
  ⟨(f, v) :: s.facts, s.vars⟩

/-- Забыть значение переменной (после `modifies`). -/
def clearVar (s : KState) (v : VarName) : KState :=
  ⟨s.facts, (v, none) :: s.vars⟩

@[simp] theorem factStatus_setFact_self (s : KState) (f : FactId) (v : PT) :
    (s.setFact f v).factStatus f = v := by
  simp [factStatus, setFact]

theorem factStatus_setFact_of_ne (s : KState) {f g : FactId} (h : g ≠ f) (v : PT) :
    (s.setFact f v).factStatus g = s.factStatus g := by
  simp [factStatus, setFact, List.find?_cons_of_neg, Ne.symm h]

@[simp] theorem varValue_clearVar_self (s : KState) (v : VarName) :
    (s.clearVar v).varValue v = none := by
  simp [varValue, clearVar]

theorem varValue_clearVar_of_ne (s : KState) {v w : VarName} (h : w ≠ v) :
    (s.clearVar v).varValue w = s.varValue w := by
  simp [varValue, clearVar, List.find?_cons_of_neg, Ne.symm h]

@[simp] theorem varValue_setFact (s : KState) (f : FactId) (x : PT) (v : VarName) :
    (s.setFact f x).varValue v = s.varValue v := rfl

@[simp] theorem factStatus_clearVar (s : KState) (v : VarName) (f : FactId) :
    (s.clearVar v).factStatus f = s.factStatus f := rfl

end KState

/-! ## Язык предикатов -/

/-- Язык предусловий ядра v0.1 плюс три константы, необходимые обратному
трансформеру предикатов. -/
inductive Pred
  /-- Атомарный факт. -/
  | factExists (f : FactId)
  /-- Отрицание. -/
  | pnot (p : Pred)
  /-- Конъюнкция. -/
  | pand (p q : Pred)
  /-- Дизъюнкция. -/
  | por (p q : Pred)
  /-- Импликация. -/
  | pimp (p q : Pred)
  /-- Переменная состояния не меньше значения. -/
  | gte (v : VarName) (n : ℕ)
  /-- Переменная состояния равна значению. -/
  | peq (v : VarName) (n : ℕ)
  /-- Константа «доказано истинно». -/
  | ctrue
  /-- Константа «доказано ложно». -/
  | cfalse
  /-- Константа «нет информации». -/
  | cunknown
  deriving DecidableEq, Repr, Inhabited

/-- Семантика предиката в состоянии. -/
def eval (s : KState) : Pred → PT
  | .factExists f => s.factStatus f
  | .pnot p => (eval s p).neg
  | .pand p q => PT.and (eval s p) (eval s q)
  | .por p q => PT.or (eval s p) (eval s q)
  | .pimp p q => PT.imp (eval s p) (eval s q)
  | .gte v n =>
      match s.varValue v with
      | some m => if n ≤ m then .TRUE_KNOWN else .FALSE_KNOWN
      | none => .UNKNOWN
  | .peq v n =>
      match s.varValue v with
      | some m => if m = n then .TRUE_KNOWN else .FALSE_KNOWN
      | none => .UNKNOWN
  | .ctrue => .TRUE_KNOWN
  | .cfalse => .FALSE_KNOWN
  | .cunknown => .UNKNOWN

/-- Конъюнкция списка требований. -/
def conj : List Pred → Pred
  | [] => .ctrue
  | p :: ps => .pand p (conj ps)

/-- Список требований выполнен тогда и только тогда, когда доказано каждое. -/
theorem eval_conj_true_iff (s : KState) (ps : List Pred) :
    eval s (conj ps) = .TRUE_KNOWN ↔ ∀ p ∈ ps, eval s p = .TRUE_KNOWN := by
  induction ps with
  | nil => simp [conj, eval]
  | cons p ps ih =>
      simp only [conj, eval, PT.and_eq_true_iff, List.mem_cons, forall_eq_or_imp]
      exact and_congr Iff.rfl ih

/-! ## Оператор и его исполнение -/

/-- Уровень эффекта (§4 OSA-3.x, сохранён в v0.4). -/
inductive EffectLevel
  | E0 | E1 | E2 | E3 | E4
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Числовой ранг уровня эффекта. -/
def EffectLevel.rank : EffectLevel → ℕ
  | .E0 => 0 | .E1 => 1 | .E2 => 2 | .E3 => 3 | .E4 => 4

/-- Оператор ядра: контракт (`requires`) и вектор эффектов. -/
structure Op where
  /-- Имя оператора. -/
  name : String
  /-- Предусловия. -/
  requires : List Pred
  /-- Факты, которые оператор доказывает. -/
  produces : List FactId
  /-- Ресурсы, которые оператор потребляет. -/
  consumes : List FactId
  /-- Предикаты, доказательства которых оператор обесценивает. -/
  invalidates : List FactId
  /-- Переменные состояния, значения которых оператор меняет. -/
  modifies : List VarName
  /-- Уровень эффекта. -/
  effect : EffectLevel
  /-- Требуется ли авторизация для исполнения. -/
  requiresAuth : Bool
  deriving Repr, Inhabited

namespace Op

/-- Факты, знание о которых оператор уничтожает: потребление и инвалидация. -/
def kill (o : Op) : List FactId := o.consumes ++ o.invalidates

/-- Исполнение оператора: произведённые факты становятся доказанными,
уничтоженные — **неизвестными** (а не ложными, LAW-017), изменённые
переменные теряют известное значение. -/
def exec (o : Op) (s : KState) : KState :=
  let s₁ := o.kill.foldl (fun st f => st.setFact f .UNKNOWN) s
  let s₂ := o.produces.foldl (fun st f => st.setFact f .TRUE_KNOWN) s₁
  o.modifies.foldl (fun st v => st.clearVar v) s₂

/-- Предусловие оператора выполнено в состоянии. -/
def enabled (o : Op) (s : KState) : Prop := eval s (conj o.requires) = .TRUE_KNOWN

instance (o : Op) (s : KState) : Decidable (o.enabled s) := by
  unfold enabled; infer_instance

end Op

/-! ### Поведение `exec` на фактах и переменных -/

private theorem factStatus_foldl_setFact (l : List FactId) (v : PT) :
    ∀ (s : KState) (g : FactId),
      (l.foldl (fun st f => st.setFact f v) s).factStatus g =
        if g ∈ l then v else s.factStatus g := by
  induction l with
  | nil => intro s g; simp
  | cons f t ih =>
      intro s g
      rw [List.foldl_cons, ih]
      by_cases hgt : g ∈ t
      · simp [hgt]
      · by_cases hgf : g = f
        · subst hgf; simp [hgt]
        · simp [hgt, hgf, KState.factStatus_setFact_of_ne s hgf]

private theorem varValue_foldl_setFact (l : List FactId) (v : PT) :
    ∀ (s : KState) (w : VarName),
      (l.foldl (fun st f => st.setFact f v) s).varValue w = s.varValue w := by
  induction l with
  | nil => intro s w; rfl
  | cons f t ih => intro s w; rw [List.foldl_cons, ih]; rfl

private theorem factStatus_foldl_clearVar (l : List VarName) :
    ∀ (s : KState) (g : FactId),
      (l.foldl (fun st v => st.clearVar v) s).factStatus g = s.factStatus g := by
  induction l with
  | nil => intro s g; rfl
  | cons v t ih => intro s g; rw [List.foldl_cons, ih]; rfl

private theorem varValue_foldl_clearVar (l : List VarName) :
    ∀ (s : KState) (w : VarName),
      (l.foldl (fun st v => st.clearVar v) s).varValue w =
        if w ∈ l then none else s.varValue w := by
  induction l with
  | nil => intro s w; simp
  | cons v t ih =>
      intro s w
      rw [List.foldl_cons, ih]
      by_cases hwt : w ∈ t
      · simp [hwt]
      · by_cases hwv : w = v
        · subst hwv; simp [hwt]
        · simp [hwt, hwv, KState.varValue_clearVar_of_ne s hwv]

/-- Статус произведённого факта после исполнения — доказанная истина. -/
theorem factStatus_exec_produces (o : Op) (s : KState) {f : FactId}
    (h : f ∈ o.produces) : (o.exec s).factStatus f = .TRUE_KNOWN := by
  simp [Op.exec, factStatus_foldl_clearVar, factStatus_foldl_setFact, h]

/-- Статус уничтоженного (и не произведённого заново) факта — `UNKNOWN`:
инвалидация обесценивает доказательство, но **не доказывает отрицание**
(LAW-017). -/
theorem factStatus_exec_kill (o : Op) (s : KState) {f : FactId}
    (hk : f ∈ o.kill) (hp : f ∉ o.produces) :
    (o.exec s).factStatus f = .UNKNOWN := by
  simp [Op.exec, factStatus_foldl_clearVar, factStatus_foldl_setFact, hk, hp]

/-- **LAW-003 (State Conservation).**  Факт, которого оператор не касается,
сохраняет свой статус. -/
theorem factStatus_exec_untouched (o : Op) (s : KState) {f : FactId}
    (hk : f ∉ o.kill) (hp : f ∉ o.produces) :
    (o.exec s).factStatus f = s.factStatus f := by
  simp [Op.exec, factStatus_foldl_clearVar, factStatus_foldl_setFact, hk, hp]

/-- **LAW-003 (State Conservation), переменные.**  Неизменяемая переменная
сохраняет значение. -/
theorem varValue_exec_untouched (o : Op) (s : KState) {v : VarName}
    (h : v ∉ o.modifies) : (o.exec s).varValue v = s.varValue v := by
  simp [Op.exec, varValue_foldl_clearVar, varValue_foldl_setFact, h]

/-- Изменённая переменная теряет известное значение. -/
theorem varValue_exec_modified (o : Op) (s : KState) {v : VarName}
    (h : v ∈ o.modifies) : (o.exec s).varValue v = none := by
  simp [Op.exec, varValue_foldl_clearVar, h]

/-! ## Обратный трансформер предикатов (WP) -/

/-- Обратный трансформер предикатов: `wp o Q` — предикат о состоянии *до*
исполнения, равносильный `Q` *после* исполнения. -/
def wp (o : Op) : Pred → Pred
  | .factExists f =>
      if f ∈ o.produces then .ctrue
      else if f ∈ o.kill then .cunknown
      else .factExists f
  | .pnot p => .pnot (wp o p)
  | .pand p q => .pand (wp o p) (wp o q)
  | .por p q => .por (wp o p) (wp o q)
  | .pimp p q => .pimp (wp o p) (wp o q)
  | .gte v n => if v ∈ o.modifies then .cunknown else .gte v n
  | .peq v n => if v ∈ o.modifies then .cunknown else .peq v n
  | .ctrue => .ctrue
  | .cfalse => .cfalse
  | .cunknown => .cunknown

/-- **Точная характеризация WP.**  Значение предиката после исполнения
оператора совпадает со значением его WP-образа до исполнения. -/
theorem eval_exec_eq_eval_wp (o : Op) (s : KState) :
    ∀ q : Pred, eval (o.exec s) q = eval s (wp o q) := by
  intro q
  induction q with
  | factExists f =>
      by_cases hp : f ∈ o.produces
      · simp [wp, eval, hp, factStatus_exec_produces o s hp]
      · by_cases hk : f ∈ o.kill
        · simp [wp, eval, hp, hk, factStatus_exec_kill o s hk hp]
        · simp [wp, eval, hp, hk, factStatus_exec_untouched o s hk hp]
  | pnot p ih => simp [wp, eval, ih]
  | pand p q ihp ihq => simp [wp, eval, ihp, ihq]
  | por p q ihp ihq => simp [wp, eval, ihp, ihq]
  | pimp p q ihp ihq => simp [wp, eval, ihp, ihq]
  | gte v n =>
      by_cases h : v ∈ o.modifies
      · simp [wp, eval, h, varValue_exec_modified o s h]
      · simp [wp, eval, h, varValue_exec_untouched o s h]
  | peq v n =>
      by_cases h : v ∈ o.modifies
      · simp [wp, eval, h, varValue_exec_modified o s h]
      · simp [wp, eval, h, varValue_exec_untouched o s h]
  | ctrue => rfl
  | cfalse => rfl
  | cunknown => rfl

/-- **LAW-012 (Predicate Transformer Soundness).**  `{WP(Op, Q)} Op {Q}`. -/
theorem law012_wp_sound (o : Op) (s : KState) (q : Pred)
    (h : eval s (wp o q) = .TRUE_KNOWN) : eval (o.exec s) q = .TRUE_KNOWN := by
  rw [eval_exec_eq_eval_wp]; exact h

/-- Полнота трансформера: если `Q` доказано после исполнения, то `WP(Op,Q)`
доказано до исполнения; вместе с `law012_wp_sound` это даёт равносильность,
то есть `WP(Op,Q)` — слабейшее предусловие в точном смысле. -/
theorem law012_wp_complete (o : Op) (s : KState) (q : Pred)
    (h : eval (o.exec s) q = .TRUE_KNOWN) : eval s (wp o q) = .TRUE_KNOWN := by
  rw [← eval_exec_eq_eval_wp]; exact h

/-- Композиция WP: `WP(A;B, Q) = WP(A, WP(B, Q))`. -/
theorem wp_comp (a b : Op) (s : KState) (q : Pred) :
    eval s (wp a (wp b q)) = eval (b.exec (a.exec s)) q := by
  rw [eval_exec_eq_eval_wp, eval_exec_eq_eval_wp]

/-- Условие живучести перед оператором: предусловия и WP-образ требований
продолжения (`LiveBefore(Op, Q) = Pre(Op) ∧ WP(Op, Q)`). -/
def liveBefore (o : Op) (q : Pred) : Pred := .pand (conj o.requires) (wp o q)

/-- Живучесть перед оператором доказана ⇔ оператор разрешён и после его
исполнения требования продолжения доказаны. -/
theorem liveBefore_true_iff (o : Op) (s : KState) (q : Pred) :
    eval s (liveBefore o q) = .TRUE_KNOWN ↔
      o.enabled s ∧ eval (o.exec s) q = .TRUE_KNOWN := by
  rw [liveBefore, eval, PT.and_eq_true_iff, eval_exec_eq_eval_wp]
  rfl

/-- **LAW-006 (Destroy / Liveness Safety).**  Если оператор уничтожает факт,
который нужен продолжению, требование продолжения перестаёт быть доказанным:
`KILL(X)` допустим только при `X ∉ LIVE_OUT`.  (Тесты T03, T11, T12.) -/
theorem law006_kill_live_fact (o : Op) (s : KState) {f : FactId}
    (hk : f ∈ o.kill) (hp : f ∉ o.produces) :
    eval (o.exec s) (.factExists f) ≠ .TRUE_KNOWN := by
  rw [eval, factStatus_exec_kill o s hk hp]
  decide

/-- Инвалидация не доказывает отрицание: после инвалидации `¬P` тоже не
доказано (LAW-017, ремарка «Invalidates(P) ≠ proves ¬P»). -/
theorem law017_invalidate_not_refute (o : Op) (s : KState) {f : FactId}
    (hk : f ∈ o.kill) (hp : f ∉ o.produces) :
    eval (o.exec s) (.pnot (.factExists f)) ≠ .TRUE_KNOWN := by
  rw [eval, eval, factStatus_exec_kill o s hk hp]
  decide

/-- Если оператор не трогает нужные продолжению факты и переменные,
требование продолжения переживает исполнение (безопасная сторона LAW-006). -/
theorem live_preserved_of_untouched (o : Op) (s : KState) {f : FactId}
    (hk : f ∉ o.kill) (hp : f ∉ o.produces)
    (h : eval s (.factExists f) = .TRUE_KNOWN) :
    eval (o.exec s) (.factExists f) = .TRUE_KNOWN := by
  rw [eval, factStatus_exec_untouched o s hk hp]
  exact h

/-! ## Цепочки операторов -/

/-- Исполнение цепочки операторов. -/
def execChain (ops : List Op) (s : KState) : KState := ops.foldl (fun st o => o.exec st) s

@[simp] theorem execChain_nil (s : KState) : execChain [] s = s := rfl

@[simp] theorem execChain_cons (o : Op) (ops : List Op) (s : KState) :
    execChain (o :: ops) s = execChain ops (o.exec s) := rfl

/-- WP для цепочки. -/
def wpChain (ops : List Op) (q : Pred) : Pred := ops.foldr (fun o acc => wp o acc) q

/-- Точная характеризация WP для цепочки операторов. -/
theorem eval_execChain_eq_eval_wpChain (ops : List Op) :
    ∀ (s : KState) (q : Pred), eval (execChain ops s) q = eval s (wpChain ops q) := by
  induction ops with
  | nil => intro s q; rfl
  | cons o t ih =>
      intro s q
      rw [execChain_cons, ih, eval_exec_eq_eval_wp]
      rfl

/-- **LAW-010 (Composition Soundness).**  Композиция `A ; B` допустима в
состоянии `s` тогда и только тогда, когда существует промежуточное состояние
`s'`, в котором выполнены предусловия `B`; при детерминированном исполнении
это в точности `s' = exec A s`. -/
theorem law010_composition_sound (a b : Op) (s : KState) :
    (a.enabled s ∧ b.enabled (a.exec s)) ↔
      ∃ s' : KState, a.enabled s ∧ s' = a.exec s ∧ b.enabled s' := by
  constructor
  · rintro ⟨h₁, h₂⟩; exact ⟨a.exec s, h₁, rfl, h₂⟩
  · rintro ⟨s', h₁, rfl, h₂⟩; exact ⟨h₁, h₂⟩

end Polymath.OSA4
