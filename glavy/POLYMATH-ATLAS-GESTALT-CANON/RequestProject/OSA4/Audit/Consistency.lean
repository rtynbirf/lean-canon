/-
# OSA-4.0 — аудит законов: непротиворечивость, зависимости, критические вопросы

Запрос аудита: «проверь непротиворечивость LAW-001 – LAW-018, найди
циклические зависимости», плюс пять критических вопросов.

**Непротиворечивость.**  Все 18 законов доказаны об одном и том же
формальном ядре (`lawbook_holds`), то есть выполнены **одновременно**: у
конъюнкции законов есть модель, и из неё нельзя вывести противоречие
(`lawbook_consistent`, `lawbook_pairwise_consistent`).  Дополнительно
доказано, что законы не пусты: посылки, при которых они что-то запрещают,
выполнимы (`lawbook_hypotheses_satisfiable`) — то есть непротиворечивость не
достигнута ценой вырождения.

**Зависимости.**  Граф обоснований законов (`LawId.dependsOn`) снабжён слоем
(`LawId.layer`), строго возрастающим вдоль зависимости; отсюда
`lawDeps_acyclic`: **циклических зависимостей нет** — ни один закон не
участвует в собственном обосновании.

**Критические вопросы** — `q1` … `q5`; два из них дают отрицательный ответ и
зафиксированы как находки аудита: односторонность LAW-011 (`q3`) и
неполнота поиска починки (`q4`).
-/
import RequestProject.OSA4.Audit.Witness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Polymath.OSA4

/-! ## Непротиворечивость свода законов -/

/-- **Непротиворечивость.**  Все 18 законов выполняются одновременно в одном
формальном ядре, поэтому их конъюнкция не влечёт противоречия. -/
theorem lawbook_consistent : (∀ l : LawId, l.holds) ∧ ¬ ((∀ l : LawId, l.holds) → False) :=
  ⟨lawbook_holds, fun h => h lawbook_holds⟩

/-- Любая пара законов совместна: контрпримеров «закон против закона» нет. -/
theorem lawbook_pairwise_consistent (l₁ l₂ : LawId) : l₁.holds ∧ l₂.holds :=
  ⟨lawbook_holds l₁, lawbook_holds l₂⟩

/-- Любое подмножество законов выполнимо. -/
theorem lawbook_subset_consistent (S : LawId → Prop) : ∀ l, S l → l.holds :=
  fun l _ => lawbook_holds l

/-- **Законы не вырождены**: посылки, при которых они что-то запрещают,
выполнимы.  Для LAW-004, LAW-005, LAW-006/LAW-017, LAW-011, LAW-012 и LAW-016
приведены конкретные свидетели. -/
theorem lawbook_hypotheses_satisfiable :
    (∃ (w : World) (st : Step) (i : ObjId),
      Step.legal w st = true ∧ w.phaseOf i = some .Destroyed) ∧
    (∃ (w : World) (i : ObjId), Step.legal w (.consume i) = true) ∧
    (∃ (o : Op) (f : FactId), f ∈ o.kill ∧ f ∉ o.produces) ∧
    (∃ (s : KState) (o : Op), execAllowed s o) ∧
    (∃ (o : Op) (s : KState) (q : Pred), eval s (wp o q) = .TRUE_KNOWN) ∧
    (∃ (w : World) (old new : ObjId), Step.legal w (.recreate old new) = true) := by
  refine ⟨⟨⟨[⟨1, .Destroyed, []⟩]⟩, .recreate 1 2, 1, by decide, by decide⟩,
    ⟨⟨[⟨1, .Available, []⟩]⟩, 1, by decide⟩,
    ⟨CONSUME_X, "X", by decide, by decide⟩,
    ⟨⟨[("X", .TRUE_KNOWN)], []⟩, ANALYZE_X, by decide, by decide⟩,
    ⟨CREATE_X, s0, .factExists "X", by decide⟩,
    ⟨⟨[⟨1, .Destroyed, []⟩]⟩, 1, 2, by decide⟩⟩

/-! ## Граф зависимостей законов -/

/-- Слой закона в графе обоснований. -/
def LawId.layer : LawId → ℕ
  | .LAW_001 => 0 | .LAW_002 => 0 | .LAW_003 => 0 | .LAW_004 => 0
  | .LAW_005 => 0 | .LAW_006 => 0 | .LAW_007 => 1 | .LAW_008 => 0
  | .LAW_009 => 0 | .LAW_010 => 1 | .LAW_011 => 1 | .LAW_012 => 0
  | .LAW_013 => 0 | .LAW_014 => 0 | .LAW_015 => 0 | .LAW_016 => 1
  | .LAW_017 => 1 | .LAW_018 => 2

/-- Записанный аудитом граф обоснований: на какие законы опирается содержание
данного закона.  (Проверка того, что перечисленные законы действительно
раньше по слою, — `lawDeps_layer_lt`.) -/
def LawId.dependsOn : LawId → List LawId
  | .LAW_007 => [.LAW_006]
  | .LAW_010 => [.LAW_012]
  | .LAW_011 => [.LAW_008]
  | .LAW_016 => [.LAW_004]
  | .LAW_017 => [.LAW_006]
  | .LAW_018 => [.LAW_010, .LAW_012]
  | _ => []

/-- Вдоль зависимости слой строго возрастает. -/
theorem lawDeps_layer_lt : ∀ (l : LawId) (d : LawId), d ∈ l.dependsOn → d.layer < l.layer := by
  decide

/-- Отношение «закон `a` опирается на закон `b`». -/
def LawDepends (a b : LawId) : Prop := b ∈ a.dependsOn

/-- Вдоль цепочки зависимостей слой строго убывает. -/
theorem layer_lt_of_transGen {a b : LawId} (h : Relation.TransGen LawDepends a b) :
    b.layer < a.layer := by
  induction h with
  | single hab => exact lawDeps_layer_lt _ _ hab
  | tail _ hbc ih => exact lt_trans (lawDeps_layer_lt _ _ hbc) ih

/-- **Циклических зависимостей между законами нет.** -/
theorem lawDeps_acyclic (l : LawId) : ¬ Relation.TransGen LawDepends l l := by
  intro h
  have := layer_lt_of_transGen h
  omega

/-- В частности, ни один закон не ссылается на себя напрямую. -/
theorem lawDeps_irrefl : ∀ l : LawId, l ∉ l.dependsOn := by decide

/-! ## Критический вопрос 1 — LAW-003 против LAW-004 -/

/-- Объект, которого касается шаг. -/
def Step.touches : Step → ObjId
  | .create i => i
  | .consume i => i
  | .destroy i => i
  | .resurrect i => i
  | .recreate _ new => new

/-- **Сохранение состояния в пространстве идентичностей.**  Шаг не меняет фазу
ни одного объекта, кроме того, которого он касается: это LAW-003 для оси E. -/
theorem step_frame (w : World) (st : Step) {j : ObjId} (h : j ≠ st.touches) :
    (Step.apply w st).phaseOf j = w.phaseOf j := by
  cases st with
  | create i => exact World.phaseOf_add_of_ne _ _ (Ne.symm h)
  | consume i => exact World.phaseOf_setPhase_of_ne w h .Consumed
  | destroy i => exact World.phaseOf_setPhase_of_ne w h .Destroyed
  | resurrect i => exact World.phaseOf_setPhase_of_ne w h .Available
  | recreate old new => exact World.phaseOf_add_of_ne _ _ (Ne.symm h)

/-- **Ответ на вопрос 1: противоречия между LAW-003 и LAW-004 нет.**
Законы говорят о разных компонентах состояния: LAW-003 фиксирует статус
компонент, которых оператор *не касается*, LAW-004 запрещает переход
`Destroyed → Available` для объекта, которого шаг *касается*.  Оба выполнены
в одной модели, оба непусты, и «рамочный» аналог LAW-003 для оси E
(`step_frame`) с LAW-004 совместим: он применим ровно к объектам, отличным от
затронутого. -/
theorem q1_law003_law004_consistent :
    LawId.LAW_003.holds ∧ LawId.LAW_004.holds ∧
    (∀ (w : World) (st : Step) (j : ObjId), j ≠ st.touches →
      (Step.apply w st).phaseOf j = w.phaseOf j) ∧
    (∃ (w : World) (st : Step) (i : ObjId),
      Step.legal w st = true ∧ w.phaseOf i = some .Destroyed ∧
        (Step.apply w st).phaseOf i = some .Destroyed ∧ i ≠ st.touches) :=
  ⟨lawbook_holds .LAW_003, lawbook_holds .LAW_004,
    fun w st _ h => step_frame w st h,
    ⟨⟨[⟨1, .Destroyed, []⟩]⟩, .recreate 1 2, 1, by decide, by decide, by decide, by decide⟩⟩

/-! ## Критический вопрос 2 — LAW-006 против LAW-017 -/

/-- Утверждение «ни `P`, ни `¬P` не доказаны» выполнимо ровно в четырёхзначной
семантике: значение предиката при этом — `UNKNOWN` или `CONFLICT`.  В
двузначной логике такая пара требований была бы противоречивой. -/
theorem both_unprovable_iff (a : PT) :
    (a ≠ .TRUE_KNOWN ∧ a.neg ≠ .TRUE_KNOWN) ↔ (a = .UNKNOWN ∨ a = .CONFLICT) := by
  revert a; decide

/-- **Ответ на вопрос 2: противоречия между LAW-006 и LAW-017 нет.**
Вместе они означают ровно одно: после уничтожения факта его статус —
`UNKNOWN`.  Совместимость обеспечена четырёхзначной семантикой: пара
«не доказано `P`» и «не доказано `¬P`» выполнима именно потому, что кроме
`TRUE_KNOWN`/`FALSE_KNOWN` есть `UNKNOWN`. -/
theorem q2_law006_law017_consistent :
    LawId.LAW_006.holds ∧ LawId.LAW_017.holds ∧
    (∀ (o : Op) (s : KState) (f : FactId), f ∈ o.kill → f ∉ o.produces →
      (o.exec s).factStatus f = .UNKNOWN) ∧
    (∀ a : PT, (a ≠ .TRUE_KNOWN ∧ a.neg ≠ .TRUE_KNOWN) ↔ (a = .UNKNOWN ∨ a = .CONFLICT)) :=
  ⟨lawbook_holds .LAW_006, lawbook_holds .LAW_017,
    fun o s _ hk hp => factStatus_exec_kill o s hk hp, both_unprovable_iff⟩

/-! ## Критический вопрос 3 — двусторонность LAW-011 -/

/-- Обратная импликация LAW-011 **ложна**: доказанная авторизация не влечёт
исполнимости — предусловия оператора остаются независимым требованием. -/
theorem law011_converse_fails :
    ¬ ∀ (s : KState) (o : Op), authStatus s o = .TRUE_KNOWN → execAllowed s o := by
  intro h
  have hauth : authStatus s0 MODEL = .TRUE_KNOWN := by decide
  have := (h s0 MODEL hauth).1
  revert this
  decide

/-- Верная двусторонняя форма: исполнимость равносильна конъюнкции
«предусловия доказаны» и «авторизация доказана». -/
theorem execAllowed_iff (s : KState) (o : Op) :
    execAllowed s o ↔ (o.enabled s ∧ authStatus s o = .TRUE_KNOWN) := Iff.rfl

/-- **Ответ на вопрос 3: двусторонность LAW-011 некорректна.**  В форме
`Exec ⇒ Authorized` закон верен, обратная импликация опровергнута
контрпримером, а корректная равносильность — только конъюнктивная. -/
theorem q3_law011_one_directional :
    LawId.LAW_011.holds ∧
    (¬ ∀ (s : KState) (o : Op), authStatus s o = .TRUE_KNOWN → execAllowed s o) ∧
    (∀ (s : KState) (o : Op),
      execAllowed s o ↔ (o.enabled s ∧ authStatus s o = .TRUE_KNOWN)) :=
  ⟨lawbook_holds .LAW_011, law011_converse_fails, execAllowed_iff⟩

/-! ## Критический вопрос 4 — полнота «завершающих» сценариев (починки) -/

/-- Исправленный критерий починки: оператор ремонта должен быть **исполним** в
текущем состоянии, а не только производить нужный факт. -/
def repairForSound (reg : List Op) (s : KState) (q : Pred) : Bool :=
  reg.any (fun r => decide (r.enabled s) && (eval (r.exec s) q == .TRUE_KNOWN))

/-- Исправленный критерий сильнее исходного. -/
theorem repairForSound_le (reg : List Op) (s : KState) (q : Pred) :
    repairForSound reg s q = true → repairFor reg s q = true := by
  intro h
  rw [repairForSound, List.any_eq_true] at h
  obtain ⟨r, hr, hcond⟩ := h
  rw [repairFor, List.any_eq_true]
  exact ⟨r, hr, (Bool.and_eq_true _ _ |>.mp hcond).2⟩

/-- Исправленный критерий действительно даёт исполнимый шаг починки. -/
theorem repairForSound_gives_enabled (reg : List Op) (s : KState) (q : Pred)
    (h : repairForSound reg s q = true) :
    ∃ r ∈ reg, r.enabled s ∧ eval (r.exec s) q = .TRUE_KNOWN := by
  rw [repairForSound, List.any_eq_true] at h
  obtain ⟨r, hr, hcond⟩ := h
  obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ |>.mp hcond
  exact ⟨r, hr, of_decide_eq_true h₁, by simpa using h₂⟩

/-- **Находка аудита.**  Исходный критерий починки не проверяет предусловия
самого оператора ремонта, поэтому вердикт `REPAIR` не гарантирует, что
одношаговая вставка чинит цепочку: для `MODEL` из пустого состояния вердикт —
`REPAIR`, предлагаемый ремонт `CHECK_SUFFICIENCY` в этом состоянии
неисполним, вставка его одного снова даёт `REPAIR`, и лишь двухшаговое
завершение `MEASURE → CHECK_SUFFICIENCY` доводит цепочку до `PASS`. -/
theorem repair_not_one_step_complete :
    compile ⟨registry, s0, MODEL :: [], .factExists "Model"⟩ = ⟨.REPAIR, none, some "MODEL"⟩ ∧
    repairFor registry s0 (conj MODEL.requires) = true ∧
    repairForSound registry s0 (conj MODEL.requires) = false ∧
    ¬ CHECK_SUFFICIENCY.enabled s0 ∧
    compile ⟨registry, s0, [CHECK_SUFFICIENCY, MODEL], .factExists "Model"⟩ =
      ⟨.REPAIR, none, some "CHECK_SUFFICIENCY"⟩ ∧
    compile ⟨registry, s0, [MEASURE, CHECK_SUFFICIENCY, MODEL], .factExists "Model"⟩ =
      ⟨.PASS, none, none⟩ := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **Ответ на вопрос 4: завершающие сценарии завершены не полностью.**
Вердикт `REPAIR` означает лишь существование оператора, производящего
недостающий факт; он не означает существования *исполнимой* одношаговой
починки.  Исправленный критерий `repairForSound` (доказанно более сильный)
эту гарантию даёт, а исходный на конкретном сценарии её не даёт. -/
theorem q4_completing_scenarios_incomplete :
    (∀ (reg : List Op) (s : KState) (q : Pred),
      repairForSound reg s q = true → repairFor reg s q = true) ∧
    (∀ (reg : List Op) (s : KState) (q : Pred), repairForSound reg s q = true →
      ∃ r ∈ reg, r.enabled s ∧ eval (r.exec s) q = .TRUE_KNOWN) ∧
    (repairFor registry s0 (conj MODEL.requires) = true ∧
      repairForSound registry s0 (conj MODEL.requires) = false) :=
  ⟨repairForSound_le, repairForSound_gives_enabled,
    ⟨repair_not_one_step_complete.2.1, repair_not_one_step_complete.2.2.1⟩⟩

/-! ## Критический вопрос 5 — порог достаточности -/

/-- Оператор моделирования с произвольным порогом достаточности `t`
(в сотых долях). -/
def strictModelAt (t : ℕ) : Op :=
  ⟨"STRICT_MODEL", [.gte "sufficiency" t], ["Model"], [], [], [], .E1, false⟩

/-- Состояние с измеренной достаточностью `m` (в сотых долях). -/
def sufficiencyState (m : ℕ) : KState := ⟨[], [("sufficiency", some m)]⟩

/-- Семантика порога: предусловие доказано ровно при `m ≥ t`, доказанно ложно
при `m < t`. -/
theorem strictModel_precondition (t m : ℕ) :
    eval (sufficiencyState m) (conj (strictModelAt t).requires) =
      if t ≤ m then .TRUE_KNOWN else .FALSE_KNOWN := by
  by_cases h : t ≤ m <;>
    simp [conj, eval, strictModelAt, sufficiencyState, KState.varValue, PT.and, h]

/-- При неизвестном значении достаточности предусловие не ложно, а неизвестно:
вердикт будет `UNDECIDABLE`, а не `REJECT` (LAW-«UNKNOWN ≠ FALSE», тест T05). -/
theorem strictModel_precondition_unknown (t : ℕ) :
    eval s0 (conj (strictModelAt t).requires) = .UNKNOWN := by
  simp [conj, eval, strictModelAt, s0, KState.varValue, PT.and]

/-- **Порог не определяется ядром.**  Для любого порога `t` существует
измерение, которое проходит проверку при пороге `t` и не проходит при
`t + 1`: значение порога — объявляемый параметр конфигурации, а не следствие
законов. -/
theorem threshold_is_a_parameter (t : ℕ) :
    eval (sufficiencyState t) (conj (strictModelAt t).requires) = .TRUE_KNOWN ∧
    eval (sufficiencyState t) (conj (strictModelAt (t + 1)).requires) = .FALSE_KNOWN := by
  refine ⟨?_, ?_⟩
  · rw [strictModel_precondition, if_pos le_rfl]
  · rw [strictModel_precondition, if_neg (by omega)]

/-- Проверка достаточности монотонна: чем больше измеренное значение, тем
не хуже вердикт. -/
theorem threshold_monotone (t m₁ m₂ : ℕ) (h : m₁ ≤ m₂)
    (h₁ : eval (sufficiencyState m₁) (conj (strictModelAt t).requires) = .TRUE_KNOWN) :
    eval (sufficiencyState m₂) (conj (strictModelAt t).requires) = .TRUE_KNOWN := by
  rw [strictModel_precondition] at h₁ ⊢
  by_cases ht : t ≤ m₁
  · rw [if_pos (by omega)]
  · rw [if_neg ht] at h₁; exact absurd h₁ (by decide)

/-- Вердикт компилятора на рабочем пороге 0.80: доказанная недостаточность —
`REJECT`, доказанная достаточность — `PASS`, неизвестность — `UNDECIDABLE`. -/
theorem threshold_verdicts :
    compile ⟨registry, sLowSufficiency, STRICT_MODEL :: [], .factExists "Model"⟩ =
      ⟨.REJECT, some .E_PRECONDITION_FALSE, some "STRICT_MODEL"⟩ ∧
    compile ⟨registry, sHighSufficiency, STRICT_MODEL :: [], .factExists "Model"⟩ =
      ⟨.PASS, none, none⟩ ∧
    (compile ⟨registryNoCheck, s0, [MEASURE, MODEL], .factExists "Model"⟩).verdict =
      .UNDECIDABLE := by
  refine ⟨T06_reject, T06_pass_when_sufficient, by rw [T05_undecidable]⟩

/-- **Ответ на вопрос 5: порог корректен как параметр, но не выводим.**
Семантика порога точна и монотонна, граница `UNKNOWN`/`FALSE_KNOWN`
соблюдена, но само значение 0.80 законами ядра не определяется: для любого
порога существует измерение, различающее его и соседний. -/
theorem q5_threshold_is_declared_parameter :
    (∀ t m : ℕ, eval (sufficiencyState m) (conj (strictModelAt t).requires) =
      if t ≤ m then .TRUE_KNOWN else .FALSE_KNOWN) ∧
    (∀ t : ℕ, eval s0 (conj (strictModelAt t).requires) = .UNKNOWN) ∧
    (∀ t : ℕ, eval (sufficiencyState t) (conj (strictModelAt t).requires) = .TRUE_KNOWN ∧
      eval (sufficiencyState t) (conj (strictModelAt (t + 1)).requires) = .FALSE_KNOWN) :=
  ⟨strictModel_precondition, strictModel_precondition_unknown, threshold_is_a_parameter⟩

end Polymath.OSA4
