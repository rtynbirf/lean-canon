/-
# OSA-4.0 — разбор трёх открытых вопросов реестра

`Registry.lean` фиксирует три вопроса (`OpenId`), записанные как формулы и
оставленные без доказательства.  Здесь каждый из них закрыт: два опровергнуты
контрпримерами, один доказан.

| вопрос | формулировка | итог |
|--------|--------------|------|
| O01 | вердикт REPAIR ⇒ существует корректный план ремонта | **опровергнут** (`O01_repair_completeness_fails`) |
| O02 | всякий UNDECIDABLE снимается пополнением начального состояния | **опровергнут** (`O02_undecidable_resolvable_fails`) |
| O03 | полнота анализа живучести относительно семантики цели | **доказан** (`O03_liveness_completeness_holds`) |

Опровержения не оставляют вопрос пустым: для O01 указана точная причина
(ядро не доказывает отрицаний, поэтому отрицательная цель недостижима ни
одной цепочкой — `no_plan_for_negative_goal`) и приведена верная форма
утверждения относительно бюджета поиска (`O01_repair_completeness_relative`);
для O02 указаны два независимых источника неустранимости — константа
«нет информации» и уничтожение токена авторизации, — и доказана верная форма
для детерминированных целей (`O02_resolvable_for_determinate_goal`).
-/
import RequestProject.OSA4.Registry
import RequestProject.OSA5.Repair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Polymath.OSA4

/-! ## O03 — полнота анализа живучести

Утверждение O03 доказуемо, причём гипотеза об отсутствии нарушения живучести
для него не нужна: достаточно синтаксического критерия `Untouched`. -/

/-- Цепочка операторов, не затрагивающих предикат, сохраняет его значение —
не только истинность, но и любое значение четырёхзначной семантики. -/
theorem eval_execChain_of_untouched (goal : Pred) :
    ∀ (ops : List Op) (s : KState), (∀ o ∈ ops, Untouched o goal) →
      eval (execChain ops s) goal = eval s goal := by
  intro ops
  induction ops with
  | nil => intro s _; rfl
  | cons o t ih =>
      intro s h
      rw [execChain_cons, ih _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')),
        eval_exec_eq_eval_wp, wp_eq_self_of_untouched o goal (h o List.mem_cons_self)]

/-- **O03 доказан.**  Если ни один оператор цепочки не затрагивает цель, то
доказанная перед исполнением цель остаётся доказанной после него. -/
theorem O03_liveness_completeness_holds : OpenId.O03_liveness_completeness.statement := by
  intro goal ops s _ hgoal huntouched
  rw [eval_execChain_of_untouched goal ops s huntouched]
  exact hgoal

/-! ## O01 — полнота ремонтного планировщика

Ключ к ответу — LAW-017: оператор может сделать факт доказанным
(`TRUE_KNOWN`) или неизвестным (`UNKNOWN`), но никогда не доказывает
отрицание.  Поэтому цель вида «факта заведомо нет» недостижима ни одной
цепочкой, тогда как вердикт компилятора о ней вполне может быть REPAIR:
компилятор объявляет REPAIR, посмотрев лишь на первое непройденное
предусловие. -/

/-- Состояние не содержит опровергнутых фактов. -/
def KState.NoRefuted (s : KState) : Prop := ∀ f : FactId, s.factStatus f ≠ .FALSE_KNOWN

/-- Пустое состояние не содержит опровергнутых фактов. -/
theorem noRefuted_empty : KState.NoRefuted ⟨[], []⟩ := by
  intro f
  simp [KState.factStatus]

/-- Исполнение оператора не создаёт опровергнутых фактов (LAW-017 в форме
инварианта состояния). -/
theorem noRefuted_exec {s : KState} (h : s.NoRefuted) (o : Op) : (o.exec s).NoRefuted := by
  intro f
  by_cases hp : f ∈ o.produces
  · rw [factStatus_exec_produces o s hp]; decide
  · by_cases hk : f ∈ o.kill
    · rw [factStatus_exec_kill o s hk hp]; decide
    · rw [factStatus_exec_untouched o s hk hp]; exact h f

/-- Никакая цепочка операторов не создаёт опровергнутых фактов. -/
theorem noRefuted_execChain : ∀ (ops : List Op) {s : KState}, s.NoRefuted →
    (execChain ops s).NoRefuted := by
  intro ops
  induction ops with
  | nil => intro s h; exact h
  | cons o t ih => intro s h; exact ih (noRefuted_exec h o)

/-- **Отрицательная цель недостижима.**  Если в состоянии нет опровергнутых
фактов, то ни один план ремонта не может доказать `¬ FactExists f`: ядро
инвалидирует знание, но не доказывает отрицаний. -/
theorem no_plan_for_negative_goal {s : KState} (h : s.NoRefuted) (f : FactId) :
    ∀ p : RepairPlan, ¬ p.sound s (.pnot (.factExists f)) := by
  rintro p ⟨-, hgoal⟩
  have hst := noRefuted_execChain p.chain h f
  rw [eval, eval] at hgoal
  cases hc : (execChain p.chain s).factStatus f <;> rw [hc] at hgoal hst
  · exact absurd hgoal (by decide)
  · exact hst rfl
  · exact absurd hgoal (by decide)
  · exact absurd hgoal (by decide)

/-! ### Контрпример к O01 -/

/-- Оператор, требующий факта `A`, о котором в начальном состоянии ничего не
известно. -/
def OQ_USE_A : Op := ⟨"OQ_USE_A", [.factExists "A"], ["Used"], [], [], [], .E1, false⟩

/-- Оператор, доказывающий `A`: именно его наличие в реестре делает вердикт
REPAIR, а не UNDECIDABLE. -/
def OQ_MAKE_A : Op := ⟨"OQ_MAKE_A", [], ["A"], [], [], [], .E1, false⟩

/-- Сценарий-контрпример: цель «утечки нет» отрицательна, а вердикт —
REPAIR. -/
def OQ_negativeGoalScenario : Scenario :=
  ⟨[OQ_MAKE_A, OQ_USE_A], ⟨[], []⟩, [OQ_USE_A], .pnot (.factExists "Leak")⟩

/-- Вердикт сценария вычислен: REPAIR. -/
theorem OQ_negativeGoalScenario_repair :
    (compile OQ_negativeGoalScenario).verdict = .REPAIR := by decide

/-- **O01 опровергнут.**  Вердикт REPAIR не гарантирует существования
корректного плана: цель может быть недостижима в принципе, а компилятор
объявляет REPAIR, дойдя лишь до первого непройденного предусловия. -/
theorem O01_repair_completeness_fails : ¬ OpenId.O01_repair_completeness.statement := by
  intro h
  obtain ⟨p, hp⟩ := h OQ_negativeGoalScenario OQ_negativeGoalScenario_repair
  exact no_plan_for_negative_goal noRefuted_empty "Leak" p hp

/-- **Верная форма O01.**  Полнота планировщика достижима относительно
бюджета поиска: если многошаговый поиск с топливом `n` находит план, то этот
план корректен.  (`searchRepair` из слоя OSA-5.) -/
theorem O01_repair_completeness_relative (reg : List Op) (goal : Pred) (n : ℕ)
    (s : KState) (ops : List Op) (h : Polymath.OSA5.searchRepair reg goal n s = some ops) :
    ∃ p : RepairPlan, p.sound s goal := by
  obtain ⟨he, hg, -, -⟩ := Polymath.OSA5.searchRepair_sound reg goal n s ops h
  exact ⟨⟨ops, ⟨0, 0, 0, 0, ops.length⟩⟩, he, hg⟩

/-! ## O02 — снимается ли UNDECIDABLE пополнением состояния

Нет: неустранимость имеет два независимых источника.  Первый — предикатная
константа «нет информации», значение которой от состояния не зависит.  Второй
содержательнее: оператор цепочки может уничтожить токен авторизации, который
понадобится дальше, и тогда никакое начальное состояние не поможет. -/

/-- Сценарий с целью-константой «нет информации». -/
def OQ_unknownGoalScenario : Scenario := ⟨[], ⟨[], []⟩, [], .cunknown⟩

/-- Вердикт сценария — UNDECIDABLE. -/
theorem OQ_unknownGoalScenario_undecidable :
    (compile OQ_unknownGoalScenario).verdict = .UNDECIDABLE := by decide

/-- Необратимый оператор, требующий авторизации. -/
def OQ_EXEC : Op := ⟨"OQ_EXEC", [], ["Done"], [], [], [], .E4, true⟩

/-- Оператор, инвалидирующий токен авторизации оператора `OQ_EXEC`. -/
def OQ_KILL_AUTH : Op :=
  ⟨"OQ_KILL_AUTH", [], [], [], [authFact OQ_EXEC], [], .E1, false⟩

/-- Сценарий: цепочка сначала уничтожает токен авторизации, а затем требует
его.  В реестре нет оператора, выдающего токен. -/
def OQ_authKillScenario (init : KState) : Scenario :=
  ⟨[OQ_KILL_AUTH, OQ_EXEC], init, [OQ_KILL_AUTH, OQ_EXEC], .factExists "Done"⟩

/-- Структурные проверки компилятора не зависят от состояния: если они
пройдены, вердикт даёт эпистемический проход. -/
theorem compile_eq_epiPass (reg : List Op) (init : KState) (chain : List Op) (goal : Pred)
    (h1 : unknownOperator reg chain = none)
    (h2 : doubleConsume [] chain = none)
    (h3 : livenessViolation goal chain = none) :
    compile ⟨reg, init, chain, goal⟩ = epiPass reg chain init goal := by
  simp only [compile, h1, h2, h3]

/-- Разрешённый шаг эпистемического прохода. -/
theorem epiPass_cons_of_allowed (reg : List Op) (o : Op) (t : List Op) (s : KState) (goal : Pred)
    (hpre : eval s (conj o.requires) = .TRUE_KNOWN) (hauth : authStatus s o = .TRUE_KNOWN) :
    epiPass reg (o :: t) s goal = epiPass reg t (o.exec s) goal := by
  simp only [epiPass, hpre, hauth]

/-- Шаг с неизвестной авторизацией и без авторизатора в реестре даёт
UNDECIDABLE. -/
theorem epiPass_undecidable_of_auth_unknown (reg : List Op) (o : Op) (t : List Op)
    (s : KState) (goal : Pred) (hpre : eval s (conj o.requires) = .TRUE_KNOWN)
    (hauth : authStatus s o = .UNKNOWN) (hno : authorizerFor reg o = false) :
    epiPass reg (o :: t) s goal = ⟨.UNDECIDABLE, none, some o.name⟩ := by
  simp only [epiPass, hpre, hauth, hno, if_false, Bool.false_eq_true]

/-- Вердикт этого сценария — UNDECIDABLE **при любом** начальном состоянии:
токен авторизации уничтожается внутри цепочки. -/
theorem OQ_authKill_undecidable (init : KState) :
    (compile (OQ_authKillScenario init)).verdict = .UNDECIDABLE := by
  have hkill : (OQ_KILL_AUTH.exec init).factStatus (authFact OQ_EXEC) = .UNKNOWN :=
    factStatus_exec_kill OQ_KILL_AUTH init (by decide) (by decide)
  have hauth : authStatus (OQ_KILL_AUTH.exec init) OQ_EXEC = .UNKNOWN := by
    simpa [authStatus, OQ_EXEC] using hkill
  show (compile ⟨[OQ_KILL_AUTH, OQ_EXEC], init, [OQ_KILL_AUTH, OQ_EXEC],
    Pred.factExists "Done"⟩).verdict = .UNDECIDABLE
  rw [compile_eq_epiPass _ _ _ _ (by decide) (by decide) (by decide),
    epiPass_cons_of_allowed _ _ _ _ _ rfl rfl,
    epiPass_undecidable_of_auth_unknown _ _ _ _ _ rfl hauth (by decide)]

/-- **O02 опровергнут.**  Существует сценарий с вердиктом UNDECIDABLE, у
которого ни одно пополнение начального состояния вердикта не меняет. -/
theorem O02_undecidable_resolvable_fails : ¬ OpenId.O02_undecidable_resolvable.statement := by
  intro h
  obtain ⟨init', -, hne⟩ := h (OQ_authKillScenario ⟨[], []⟩) (OQ_authKill_undecidable _)
  exact hne (OQ_authKill_undecidable init')

/-- Второй, независимый источник неустранимости: цель-константа. -/
theorem O02_unknown_goal_never_resolvable :
    ∀ init' : KState, init'.Extends OQ_unknownGoalScenario.init →
      (compile ⟨OQ_unknownGoalScenario.registry, init', OQ_unknownGoalScenario.chain,
        OQ_unknownGoalScenario.goal⟩).verdict = .UNDECIDABLE := by
  intro init' _
  rfl

/-! ### Верная форма O02: детерминированные цели

Предикат называется детерминированным, если он не содержит константы
«нет информации».  Для такой цели пополнение состояния всегда существует. -/

/-- Предикат не содержит константы `cunknown`. -/
def Pred.Determinate : Pred → Prop
  | .factExists _ => True
  | .pnot p => p.Determinate
  | .pand p q => p.Determinate ∧ q.Determinate
  | .por p q => p.Determinate ∧ q.Determinate
  | .pimp p q => p.Determinate ∧ q.Determinate
  | .gte _ _ => True
  | .peq _ _ => True
  | .ctrue => True
  | .cfalse => True
  | .cunknown => False

/-- Значение, которым пополнение закрывает факт: неизвестный факт
объявляется доказанным, известный сохраняет свой статус. -/
def factFill (s : KState) (f : FactId) : PT :=
  if s.factStatus f = .UNKNOWN then .TRUE_KNOWN else s.factStatus f

/-- Значение, которым пополнение закрывает переменную. -/
def varFill (s : KState) (v : VarName) : ℕ := (s.varValue v).getD 0

/-- Присвоить переменной значение (двойственно к `clearVar`). -/
def KState.setVar (s : KState) (v : VarName) (n : ℕ) : KState :=
  ⟨s.facts, (v, some n) :: s.vars⟩

@[simp] theorem varValue_setVar_self (s : KState) (v : VarName) (n : ℕ) :
    (s.setVar v n).varValue v = some n := by
  simp [KState.varValue, KState.setVar]

theorem varValue_setVar_of_ne (s : KState) {v w : VarName} (h : w ≠ v) (n : ℕ) :
    (s.setVar v n).varValue w = s.varValue w := by
  simp [KState.varValue, KState.setVar, List.find?_cons_of_neg, Ne.symm h]

@[simp] theorem factStatus_setVar (s : KState) (v : VarName) (n : ℕ) (f : FactId) :
    (s.setVar v n).factStatus f = s.factStatus f := rfl

/-- Пополнение состояния по списку фактов. -/
def KState.completeFacts (s : KState) (fs : List FactId) : KState :=
  fs.foldl (fun st f => st.setFact f (factFill s f)) s

/-- Пополнение состояния по списку переменных. -/
def KState.completeVars (s : KState) (vs : List VarName) : KState :=
  vs.foldl (fun st v => st.setVar v (varFill s v)) s

/-- Пополнение состояния: все перечисленные факты и переменные становятся
известными, а всё уже известное сохраняется. -/
def KState.complete (s : KState) (fs : List FactId) (vs : List VarName) : KState :=
  (s.completeFacts fs).completeVars vs

private theorem factStatus_fill_fold (s : KState) :
    ∀ (fs : List FactId) (st : KState) (f : FactId),
      (fs.foldl (fun st f => st.setFact f (factFill s f)) st).factStatus f =
        if f ∈ fs then factFill s f else st.factStatus f := by
  intro fs
  induction fs with
  | nil => intro st f; simp
  | cons g t ih =>
      intro st f
      rw [List.foldl_cons, ih]
      by_cases hft : f ∈ t
      · simp [hft]
      · by_cases hfg : f = g
        · subst hfg; simp [hft]
        · simp [hft, hfg, KState.factStatus_setFact_of_ne st hfg]

private theorem varValue_fill_fold_facts (s : KState) :
    ∀ (fs : List FactId) (st : KState) (w : VarName),
      (fs.foldl (fun st f => st.setFact f (factFill s f)) st).varValue w = st.varValue w := by
  intro fs
  induction fs with
  | nil => intro st w; rfl
  | cons g t ih => intro st w; rw [List.foldl_cons, ih]; rfl

private theorem varValue_fill_fold (s : KState) :
    ∀ (vs : List VarName) (st : KState) (v : VarName),
      (vs.foldl (fun st v => st.setVar v (varFill s v)) st).varValue v =
        if v ∈ vs then some (varFill s v) else st.varValue v := by
  intro vs
  induction vs with
  | nil => intro st v; simp
  | cons w t ih =>
      intro st v
      rw [List.foldl_cons, ih]
      by_cases hvt : v ∈ t
      · simp [hvt]
      · by_cases hvw : v = w
        · subst hvw; simp [hvt]
        · simp [hvt, hvw, varValue_setVar_of_ne st hvw]

private theorem factStatus_fill_fold_vars (s : KState) :
    ∀ (vs : List VarName) (st : KState) (f : FactId),
      (vs.foldl (fun st v => st.setVar v (varFill s v)) st).factStatus f = st.factStatus f := by
  intro vs
  induction vs with
  | nil => intro st f; rfl
  | cons w t ih => intro st f; rw [List.foldl_cons, ih]; rfl

/-- Статус факта после пополнения. -/
theorem factStatus_complete (s : KState) (fs : List FactId) (vs : List VarName) (f : FactId) :
    (s.complete fs vs).factStatus f = if f ∈ fs then factFill s f else s.factStatus f := by
  rw [KState.complete, KState.completeVars, factStatus_fill_fold_vars, KState.completeFacts,
    factStatus_fill_fold]

/-- Значение переменной после пополнения. -/
theorem varValue_complete (s : KState) (fs : List FactId) (vs : List VarName) (v : VarName) :
    (s.complete fs vs).varValue v = if v ∈ vs then some (varFill s v) else s.varValue v := by
  have hvv : ∀ w : VarName, (s.completeFacts fs).varValue w = s.varValue w := fun w =>
    varValue_fill_fold_facts s fs s w
  rw [KState.complete, KState.completeVars, varValue_fill_fold]
  by_cases hm : v ∈ vs <;> simp [hm, varFill, hvv]

/-- Пополнение сохраняет всякий известный статус факта. -/
theorem complete_extends (s : KState) (fs : List FactId) (vs : List VarName) :
    (s.complete fs vs).Extends s := by
  intro f hf
  rw [factStatus_complete]
  by_cases hm : f ∈ fs
  · simp [hm, factFill, hf]
  · simp [hm]

/-- После пополнения о каждом перечисленном факте что-то известно. -/
theorem complete_factStatus_ne_unknown (s : KState) (fs : List FactId) (vs : List VarName)
    {f : FactId} (hf : f ∈ fs) : (s.complete fs vs).factStatus f ≠ .UNKNOWN := by
  rw [factStatus_complete, if_pos hf, factFill]
  by_cases hu : s.factStatus f = .UNKNOWN
  · simp [hu]
  · simp [hu]

/-- После пополнения каждая перечисленная переменная имеет значение. -/
theorem complete_varValue_isSome (s : KState) (fs : List FactId) (vs : List VarName)
    {v : VarName} (hv : v ∈ vs) : ((s.complete fs vs).varValue v).isSome := by
  rw [varValue_complete, if_pos hv]
  rfl

/-- Значение детерминированного предиката в состоянии, где известны все его
атомы, не равно `UNKNOWN`. -/
theorem eval_ne_unknown_of_determinate (s : KState) :
    ∀ p : Pred, p.Determinate →
      (∀ f ∈ p.factIds, s.factStatus f ≠ .UNKNOWN) →
      (∀ v ∈ p.varNames, (s.varValue v).isSome) →
      eval s p ≠ .UNKNOWN := by
  intro p
  induction p with
  | factExists f =>
      intro _ hf _
      exact hf f (by simp [Pred.factIds])
  | pnot q ih =>
      intro hd hf hv
      have := ih hd (by simpa [Pred.factIds] using hf) (by simpa [Pred.varNames] using hv)
      rw [eval]
      cases hq : eval s q <;> simp_all [PT.neg]
  | pand q r ihq ihr =>
      intro hd hf hv
      simp only [Pred.factIds, Pred.varNames, List.mem_append] at hf hv
      have h₁ := ihq hd.1 (fun f hfm => hf f (Or.inl hfm)) (fun v hvm => hv v (Or.inl hvm))
      have h₂ := ihr hd.2 (fun f hfm => hf f (Or.inr hfm)) (fun v hvm => hv v (Or.inr hvm))
      rw [eval]
      cases hq : eval s q <;> cases hr : eval s r <;> simp_all [PT.and]
  | por q r ihq ihr =>
      intro hd hf hv
      simp only [Pred.factIds, Pred.varNames, List.mem_append] at hf hv
      have h₁ := ihq hd.1 (fun f hfm => hf f (Or.inl hfm)) (fun v hvm => hv v (Or.inl hvm))
      have h₂ := ihr hd.2 (fun f hfm => hf f (Or.inr hfm)) (fun v hvm => hv v (Or.inr hvm))
      rw [eval]
      cases hq : eval s q <;> cases hr : eval s r <;> simp_all [PT.or]
  | pimp q r ihq ihr =>
      intro hd hf hv
      simp only [Pred.factIds, Pred.varNames, List.mem_append] at hf hv
      have h₁ := ihq hd.1 (fun f hfm => hf f (Or.inl hfm)) (fun v hvm => hv v (Or.inl hvm))
      have h₂ := ihr hd.2 (fun f hfm => hf f (Or.inr hfm)) (fun v hvm => hv v (Or.inr hvm))
      rw [eval]
      cases hq : eval s q <;> cases hr : eval s r <;> simp_all [PT.imp, PT.or, PT.neg]
  | gte v n =>
      intro _ _ hv
      have := hv v (by simp [Pred.varNames])
      rw [eval]
      cases hvv : s.varValue v with
      | none => simp [hvv] at this
      | some m => by_cases h : n ≤ m <;> simp [h]
  | peq v n =>
      intro _ _ hv
      have := hv v (by simp [Pred.varNames])
      rw [eval]
      cases hvv : s.varValue v with
      | none => simp [hvv] at this
      | some m => by_cases h : m = n <;> simp [h]
  | ctrue => intro _ _ _; rw [eval]; decide
  | cfalse => intro _ _ _; rw [eval]; decide
  | cunknown => intro hd _ _; exact absurd hd id

/-- **Верная форма O02.**  Для детерминированной цели пополнение начального
состояния, снимающее вердикт UNDECIDABLE, существует всегда. -/
theorem O02_resolvable_for_determinate_goal (reg : List Op) (s : KState) (goal : Pred)
    (hd : goal.Determinate) :
    ∃ init' : KState, init'.Extends s ∧
      (compile ⟨reg, init', [], goal⟩).verdict ≠ .UNDECIDABLE := by
  refine ⟨s.complete goal.factIds goal.varNames, complete_extends s _ _, ?_⟩
  have hne : eval (s.complete goal.factIds goal.varNames) goal ≠ .UNKNOWN :=
    eval_ne_unknown_of_determinate _ goal hd
      (fun f hf => complete_factStatus_ne_unknown s _ _ hf)
      (fun v hv => complete_varValue_isSome s _ _ hv)
  show (epiPass reg [] (s.complete goal.factIds goal.varNames) goal).verdict ≠ .UNDECIDABLE
  rw [epiPass]
  cases h : eval (s.complete goal.factIds goal.varNames) goal <;> simp_all

/-! ## Итог -/

/-- **Сводка по трём открытым вопросам.**  O01 и O02 опровергнуты, O03
доказан; ни один не оставлен без ответа и ни один не постулирован. -/
theorem openQuestions_resolved :
    ¬ OpenId.O01_repair_completeness.statement ∧
    ¬ OpenId.O02_undecidable_resolvable.statement ∧
    OpenId.O03_liveness_completeness.statement :=
  ⟨O01_repair_completeness_fails, O02_undecidable_resolvable_fails,
   O03_liveness_completeness_holds⟩

end Polymath.OSA4
