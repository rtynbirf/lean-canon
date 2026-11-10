/-
# OSA-4.0 — свидетели минимального базисного набора (§13)

Кодекс требует для каждого закона минимальный набор проверок:
positive / negative / boundary / branch / repair.  Здесь собраны недостающие
конкретные свидетели — маленькие, но полностью доказанные утверждения,
закрывающие позиции базиса, которых не покрывали Semantic Torture Set и общие
теоремы ядра.  Учёт покрытия ведётся в `Basis.lean`.
-/
import RequestProject.OSA4.Lawbook

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace Polymath.OSA4

/-! ## LAW-001 / LAW-002 — решётка типов -/

/-- Демонстрационная решётка типов: `CalibratedValue ⊑ MeasuredValue ⊑ Datum`. -/
def demoLattice : TypeLattice :=
  ⟨[("CalibratedValue", "MeasuredValue"), ("MeasuredValue", "Datum")]⟩

/-- Positive LAW-002: цепочка подтипов замыкается транзитивно. -/
theorem basis_law002_positive : demoLattice.IsSubtype "CalibratedValue" "Datum" := by
  have h₁ : demoLattice.IsSubtype "CalibratedValue" "MeasuredValue" :=
    TypeLattice.isSubtype_of_edge _ (by simp [TypeLattice.Edge, demoLattice])
  have h₂ : demoLattice.IsSubtype "MeasuredValue" "Datum" :=
    TypeLattice.isSubtype_of_edge _ (by simp [TypeLattice.Edge, demoLattice])
  exact TypeLattice.isSubtype_trans _ h₁ h₂

/-- Negative LAW-002: в пустой решётке ничего, кроме равенства, не выводится —
подтипизация не «додумывается». -/
theorem basis_law002_negative : ¬ (TypeLattice.mk []).IsSubtype "A" "B" := by
  intro h
  have := TypeLattice.isSubtype_empty_iff.mp h
  exact absurd this (by decide)

/-- Boundary LAW-001: рефлексивность работает и для метки, которой нет ни в
одном объявлении. -/
theorem basis_law001_boundary : demoLattice.IsSubtype "Unheard" "Unheard" :=
  demoLattice.isSubtype_refl _

/-! ## LAW-003 — сохранение состояния -/

/-- Оператор, производящий факт `A`. -/
def opProduceA : Op := ⟨"PRODUCE_A", [], ["A"], [], [], [], .E1, false⟩

/-- Состояние, в котором доказан факт `B`. -/
def stateB : KState := ⟨[("B", .TRUE_KNOWN)], []⟩

/-- Positive LAW-003: нетронутый факт сохраняет статус. -/
theorem basis_law003_positive : (opProduceA.exec stateB).factStatus "B" = .TRUE_KNOWN := by
  decide

/-- Negative LAW-003: затронутый факт статус меняет — закон говорит именно о
*нетронутых* компонентах. -/
theorem basis_law003_negative :
    stateB.factStatus "A" = .UNKNOWN ∧ (opProduceA.exec stateB).factStatus "A" = .TRUE_KNOWN := by
  refine ⟨by decide, by decide⟩

/-- Boundary LAW-003: переменные оператора без `modifies` не меняются. -/
theorem basis_law003_boundary (s : KState) (v : VarName) :
    (opProduceA.exec s).varValue v = s.varValue v :=
  varValue_exec_untouched opProduceA s (by simp [opProduceA])

/-! ## LAW-007 — живучесть проверенного графа -/

/-- Negative LAW-007: цепочка, уничтожающая нужный продолжению факт, не
проходит проверку живучести. -/
theorem basis_law007_negative :
    livenessViolation (.factExists "AnalysisX") [CREATE_X, DELETE_X, ANALYZE_X]
      = some "DELETE_X" := by
  decide

/-- Repair LAW-007: без удаления та же цель достигается. -/
theorem basis_law007_repair :
    compile ⟨registry, s0, [CREATE_X, ANALYZE_X], .factExists "AnalysisX"⟩ =
      ⟨.PASS, none, none⟩ := by
  decide

/-! ## LAW-008 — агрегация эффектов и политика -/

/-- Positive LAW-008: агрегация не зависит от порядка операторов. -/
theorem basis_law008_positive :
    EffectLevel.aggregate [.E1, .E4, .E0] = EffectLevel.aggregate [.E0, .E1, .E4] := by
  decide

/-- Negative LAW-008: цепочка с необратимым эффектом не проходит политику
уровня E2. -/
theorem basis_law008_negative :
    EffectPolicy.allows ⟨.E2⟩ [.E1, .E4] = false := by decide

/-- Boundary LAW-008: ровно на границе политика пропускает. -/
theorem basis_law008_boundary :
    EffectPolicy.allows ⟨.E2⟩ [.E1, .E2] = true := by decide

/-- Branch LAW-008: перестановка ветвей графа не меняет вердикт политики. -/
theorem basis_law008_branch (p : EffectPolicy) (l₁ l₂ : List EffectLevel) :
    p.allows (l₁ ++ l₂) = p.allows (l₂ ++ l₁) :=
  EffectPolicy.allows_append_comm p l₁ l₂

/-! ## LAW-009 — эпистемическая честность -/

/-- Positive LAW-009: шаг со свидетельством вправе уменьшить неопределённость. -/
theorem basis_law009_positive : UStep.honest ⟨30, 10, true⟩ := by decide

/-- Boundary LAW-009: без свидетельства допустимо только сохранение уровня. -/
theorem basis_law009_boundary : UStep.honest ⟨30, 30, false⟩ := by decide

/-! ## LAW-010 — композиция -/

/-- Positive LAW-010: `CREATE_X ; ANALYZE_X` — корректная композиция. -/
theorem basis_law010_positive :
    CREATE_X.enabled s0 ∧ ANALYZE_X.enabled (CREATE_X.exec s0) := by
  refine ⟨by decide, by decide⟩

/-- Negative LAW-010: `ANALYZE_X` без создания X не разрешён. -/
theorem basis_law010_negative : ¬ ANALYZE_X.enabled s0 := by decide

/-! ## LAW-012 — WP-трансформер -/

/-- Negative LAW-012: для уничтоженного факта WP выдаёт «нет информации», и
требование продолжения не может быть доказано. -/
theorem basis_law012_negative :
    wp DELETE_X (.factExists "X") = .cunknown := by decide

/-- Boundary LAW-012: WP факта, которого оператор не касается, — он сам. -/
theorem basis_law012_boundary :
    wp DELETE_X (.factExists "Y") = .factExists "Y" := by decide

/-- Repair LAW-012: после повторного создания X требование снова доказуемо. -/
theorem basis_law012_repair :
    eval (CREATE_X.exec s0) (.factExists "X") = .TRUE_KNOWN := by decide

/-! ## LAW-013 / LAW-014 / LAW-015 — слияние ветвей -/

/-- Positive LAW-013: слияние с «нет информации» ничего не меняет. -/
theorem basis_law013_positive (a : Belief) : Belief.join a Belief.bot = a :=
  Belief.join_bot a

/-- Negative LAW-014: напечатанная в кодексе таблица ассоциативной не является
(именно этот контрпример и потребовал исправления ядра). -/
theorem basis_law014_negative :
    joinSpec (joinSpec .TRUE_KNOWN .FALSE_KNOWN) .UNKNOWN ≠
      joinSpec .TRUE_KNOWN (joinSpec .FALSE_KNOWN .UNKNOWN) := by
  decide

/-- Boundary LAW-014: в исправленной алгебре тот же случай ассоциативен. -/
theorem basis_law014_boundary :
    Belief.join (Belief.join (EV.TRUE_KNOWN).toBelief (EV.FALSE_KNOWN).toBelief)
        (EV.UNKNOWN).toBelief =
      Belief.join (EV.TRUE_KNOWN).toBelief
        (Belief.join (EV.FALSE_KNOWN).toBelief (EV.UNKNOWN).toBelief) :=
  Belief.join_assoc _ _ _

/-- Positive LAW-015: повторное слияние одной ветви ничего не добавляет. -/
theorem basis_law015_positive (a : Belief) : Belief.join a a = a := Belief.join_idem a

/-! ## LAW-016 — идентичность при воссоздании -/

/-- Negative LAW-016: воссоздание под тем же идентификатором недопустимо. -/
theorem basis_law016_negative :
    Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 1) = false := by decide

/-- Boundary LAW-016: недопустимо и воссоздание под занятым идентификатором. -/
theorem basis_law016_boundary :
    Step.legal ⟨[⟨1, .Destroyed, []⟩, ⟨2, .Available, []⟩]⟩ (.recreate 1 2) = false := by
  decide

/-! ## LAW-017 — инвалидация -/

/-- Positive LAW-017: после инвалидации факт получает статус `UNKNOWN`
(а не `FALSE_KNOWN`). -/
theorem basis_law017_positive (s : KState) :
    (MODIFY_X.exec s).factStatus "Calibrated" = .UNKNOWN :=
  factStatus_exec_kill MODIFY_X s (by decide) (by decide)

/-! ## LAW-011 / LAW-018 — граничные случаи -/

/-- Boundary LAW-011: неизвестный токен авторизации даёт UNDECIDABLE, а не
REJECT. -/
theorem basis_law011_boundary :
    authVerdict s0 EXECUTE = .UNDECIDABLE := by decide

/-- Negative LAW-018: дешёвый небезопасный план проигрывает — безопасность
доминирует. -/
theorem basis_law018_negative : ¬ RVec.lt ⟨1, 0, 0, 0, 1⟩ ⟨0, 0, 0, 0, 3⟩ := by
  intro h
  exact absurd (RVec.lt_trans h RVec.torture_T15_safe_beats_cheap)
    (RVec.lt_irrefl _)

/-- Boundary LAW-018: при равенстве всех критериев решает стоимость. -/
theorem basis_law018_boundary : RVec.lt ⟨0, 0, 0, 0, 1⟩ ⟨0, 0, 0, 0, 2⟩ :=
  RVec.cost_last rfl rfl rfl rfl (by norm_num)

/-! ## Дополнение: позиции базиса, остававшиеся незакрытыми

Ниже — свидетели для всех позиций §13, которых не хватало предыдущей
ревизии.  Вместе с приведёнными выше они закрывают все 90 позиций
(учёт — в `Basis.lean`, теорема `coverage_complete`). -/

/-! ### LAW-001 / LAW-002 — решётка типов: negative, boundary, branch, repair -/

/-- Метка без объявленных надтипов не приобретает их из рефлексивности. -/
theorem isSubtype_eq_of_no_outgoing {L : TypeLattice} {a : TypeTag}
    (h : ∀ b, ¬ L.Edge a b) {b : TypeTag} (hab : L.IsSubtype a b) : b = a := by
  induction hab with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) (h _)

/-- Negative LAW-001: рефлексивность не «додумывает» надтипов — из `Datum`
не выводится ничего, кроме него самого. -/
theorem basis_law001_negative : ¬ demoLattice.IsSubtype "Datum" "MeasuredValue" := by
  intro h
  have : ("MeasuredValue" : TypeTag) = "Datum" :=
    isSubtype_eq_of_no_outgoing (L := demoLattice)
      (by intro b hb; simp [TypeLattice.Edge, demoLattice] at hb) h
  exact absurd this (by decide)

/-- Слияние двух ветвей объявлений типов: объединение объявленных рёбер. -/
def latticeMerge (L₁ L₂ : TypeLattice) : TypeLattice := ⟨L₁.edges ++ L₂.edges⟩

/-- Branch LAW-001: рефлексивность переживает слияние ветвей. -/
theorem basis_law001_branch (L₁ L₂ : TypeLattice) (a : TypeTag) :
    (latticeMerge L₁ L₂).IsSubtype a a :=
  (latticeMerge L₁ L₂).isSubtype_refl a

/-- Repair LAW-001: починка решётки (добавление объявления) не отменяет уже
выведенных отношений — в частности старой цепочки `CalibratedValue ⊑ Datum`. -/
theorem basis_law001_repair :
    (TypeLattice.mk (("Datum", "Entity") :: demoLattice.edges)).IsSubtype
      "CalibratedValue" "Datum" :=
  TypeLattice.isSubtype_mono (L₁ := demoLattice) (by intro e he; simp [he]) basis_law002_positive

/-- Boundary LAW-002: транзитивное замыкание останавливается на вершине
цепочки — `Datum` не получает надтипов «по инерции». -/
theorem basis_law002_boundary (b : TypeTag) (h : demoLattice.IsSubtype "Datum" b) :
    b = "Datum" :=
  isSubtype_eq_of_no_outgoing (L := demoLattice)
    (by intro c hc; simp [TypeLattice.Edge, demoLattice] at hc) h

/-- Branch LAW-002: транзитивность работает и через границу ветвей — ребро
из одной ветви склеивается с ребром из другой. -/
theorem basis_law002_branch :
    (latticeMerge ⟨[("A", "B")]⟩ ⟨[("B", "C")]⟩).IsSubtype "A" "C" := by
  refine TypeLattice.isSubtype_trans (b := "B") _ ?_ ?_
  · exact TypeLattice.isSubtype_of_edge _ (by simp [TypeLattice.Edge, latticeMerge])
  · exact TypeLattice.isSubtype_of_edge _ (by simp [TypeLattice.Edge, latticeMerge])

/-- Repair LAW-002: разорванная цепочка чинится объявлением недостающего
ребра — после починки `CalibratedValue ⊑ Entity` выводится. -/
theorem basis_law002_repair :
    (TypeLattice.mk (("Datum", "Entity") :: demoLattice.edges)).IsSubtype
      "CalibratedValue" "Entity" := by
  refine TypeLattice.isSubtype_trans _ basis_law001_repair ?_
  exact TypeLattice.isSubtype_of_edge _ (by simp [TypeLattice.Edge])

/-! ### LAW-003 — сохранение состояния: branch, repair -/

/-- Branch LAW-003: независимые ветви не мешают друг другу — порядок
исполнения `CREATE_X` и `CREATE_Y` не влияет на итоговые статусы. -/
theorem basis_law003_branch :
    ((CREATE_Y.exec (CREATE_X.exec s0)).factStatus "X" = .TRUE_KNOWN ∧
     (CREATE_Y.exec (CREATE_X.exec s0)).factStatus "Y" = .TRUE_KNOWN ∧
     (CREATE_Y.exec (CREATE_X.exec s0)).factStatus "Z" = .UNKNOWN) ∧
    ((CREATE_X.exec (CREATE_Y.exec s0)).factStatus "X" = .TRUE_KNOWN ∧
     (CREATE_X.exec (CREATE_Y.exec s0)).factStatus "Y" = .TRUE_KNOWN ∧
     (CREATE_X.exec (CREATE_Y.exec s0)).factStatus "Z" = .UNKNOWN) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

/-- Repair LAW-003: потерянный при удалении факт возвращается повторным
созданием — состояние восстановимо, хотя закон сохранения его не защищал. -/
theorem basis_law003_repair :
    (DELETE_X.exec (CREATE_X.exec s0)).factStatus "X" = .UNKNOWN ∧
    (CREATE_X.exec (DELETE_X.exec (CREATE_X.exec s0))).factStatus "X" = .TRUE_KNOWN := by
  refine ⟨by decide, by decide⟩

/-! ### LAW-004 — No Resurrection: boundary, branch, repair -/

/-- Boundary LAW-004: уничтожение уже уничтоженного объекта недопустимо —
граница фазы не проходится дважды. -/
theorem basis_law004_boundary :
    Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.destroy 1) = false := by decide

/-- Branch LAW-004: уничтожение объекта одной ветви не затрагивает объект
другой. -/
theorem basis_law004_branch :
    (Step.apply ⟨[⟨1, .Available, []⟩, ⟨2, .Available, []⟩]⟩ (.destroy 1)).phaseOf 2
      = some .Available := by decide

/-- Repair LAW-004: законный способ «вернуть» уничтоженный объект — не
воскрешение, а воссоздание под новым ID; оригинал остаётся уничтоженным. -/
theorem basis_law004_repair :
    Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2) = true ∧
    (Step.apply ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2)).phaseOf 2 = some .Available ∧
    (Step.apply ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2)).phaseOf 1 = some .Destroyed := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### LAW-005 — Consume Safety: boundary, branch, repair -/

/-- Boundary LAW-005: объект в фазе `Created` ещё не доступен — потребление
недопустимо ровно до границы `Available`. -/
theorem basis_law005_boundary :
    Step.legal ⟨[⟨1, .Created, []⟩]⟩ (.consume 1) = false := by decide

/-- Branch LAW-005: потребление ресурса одной ветви не потребляет ресурс
другой. -/
theorem basis_law005_branch :
    (Step.apply ⟨[⟨1, .Available, []⟩, ⟨2, .Available, []⟩]⟩ (.consume 1)).phaseOf 2
      = some .Available := by decide

/-- Repair LAW-005: недоступный ресурс чинится воссозданием — после
`recreate` потребление снова допустимо. -/
theorem basis_law005_repair :
    Step.legal (Step.apply ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2)) (.consume 2) = true := by
  decide

/-! ### LAW-006 — живучесть: branch, repair -/

/-- Branch LAW-006: уничтожение факта в одной ветви не обесценивает знание
другой ветви. -/
theorem basis_law006_branch :
    (DELETE_X.exec (CREATE_Y.exec (CREATE_X.exec s0))).factStatus "X" = .UNKNOWN ∧
    (DELETE_X.exec (CREATE_Y.exec (CREATE_X.exec s0))).factStatus "Y" = .TRUE_KNOWN := by
  refine ⟨by decide, by decide⟩

/-- Repair LAW-006: нарушение живучести чинится перестановкой — если анализ
идёт до удаления, композиция проходит. -/
theorem basis_law006_repair :
    compile ⟨registry, s0, [CREATE_X, ANALYZE_X, DELETE_X], .factExists "AnalysisX"⟩
      = ⟨.PASS, none, none⟩ := by decide

/-! ### LAW-007 — Liveness Soundness: branch -/

/-- Branch LAW-007: добавление параллельной ветви не маскирует нарушения
живучести — виновный оператор тот же. -/
theorem basis_law007_branch :
    livenessViolation (.factExists "AnalysisX")
        [CREATE_X, CREATE_Y, DELETE_X, ANALYZE_X] = some "DELETE_X" ∧
    livenessViolation (.factExists "AnalysisX")
        [CREATE_X, DELETE_X, ANALYZE_X] = some "DELETE_X" := by
  refine ⟨by decide, by decide⟩

/-! ### LAW-008 — политика эффектов: repair -/

/-- Repair LAW-008: нарушение политики чинится либо снятием необратимого
шага, либо явным поднятием границы политики; агрегат при этом не меняется. -/
theorem basis_law008_repair :
    EffectPolicy.allows ⟨.E2⟩ [.E1, .E4] = false ∧
    EffectPolicy.allows ⟨.E4⟩ [.E1, .E4] = true ∧
    EffectPolicy.allows ⟨.E2⟩ [.E1, .E2] = true := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### LAW-009 — эпистемическая честность: branch, repair -/

/-- Branch LAW-009: склейка двух честных участков без свидетельств тоже не
уменьшает неопределённости — «отмыть» уверенность соединением ветвей нельзя. -/
theorem basis_law009_branch (l₁ l₂ : List UStep) (a : UStep)
    (hchain : UChain (a :: (l₁ ++ l₂)))
    (hh : ∀ s ∈ a :: (l₁ ++ l₂), s.honest)
    (he : ∀ s ∈ a :: (l₁ ++ l₂), s.evidence = false) :
    a.uIn ≤ (List.getLast (a :: (l₁ ++ l₂)) (by simp)).uOut :=
  law009_no_overclaim (l₁ ++ l₂) a hchain hh he

/-- Repair LAW-009: починка — вставка шага, порождающего свидетельство;
только тогда цепочка вправе завершиться меньшей неопределённостью. -/
theorem basis_law009_repair :
    UStep.honest ⟨30, 40, false⟩ ∧ UStep.honest ⟨40, 10, true⟩ ∧
    ¬ UStep.honest ⟨40, 10, false⟩ := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### LAW-010 — композиция: boundary, branch, repair -/

/-- Boundary LAW-010: оператор с пустым контрактом разрешён в любом
состоянии — граничный случай композиции. -/
theorem basis_law010_boundary (s : KState) : CREATE_X.enabled s := rfl

/-- Branch LAW-010: независимые ветви композируются в любом порядке. -/
theorem basis_law010_branch :
    (ANALYZE_X.enabled (CREATE_Y.exec (CREATE_X.exec s0)) ∧
      ANALYZE_Y.enabled (CREATE_Y.exec (CREATE_X.exec s0))) ∧
    (ANALYZE_X.enabled (CREATE_X.exec (CREATE_Y.exec s0)) ∧
      ANALYZE_Y.enabled (CREATE_X.exec (CREATE_Y.exec s0))) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- Repair LAW-010: недопустимая композиция `CALIBRATE ; MODEL` чинится
вставкой явной проверки достаточности данных. -/
theorem basis_law010_repair :
    ¬ MODEL.enabled (CALIBRATE.exec (MEASURE.exec s0)) ∧
    MODEL.enabled (CHECK_SUFFICIENCY.exec (CALIBRATE.exec (MEASURE.exec s0))) := by
  refine ⟨by decide, by decide⟩

/-! ### LAW-011 — авторизация: branch -/

/-- Branch LAW-011: токен, выданный в ветви авторизации, действует в
объединённом состоянии; без этой ветви авторизация неизвестна. -/
theorem basis_law011_branch :
    authStatus (DECIDE.exec s0) EXECUTE = .UNKNOWN ∧
    authStatus (AUTHORIZE.exec (DECIDE.exec s0)) EXECUTE = .TRUE_KNOWN := by
  refine ⟨by decide, by decide⟩

/-! ### LAW-012 — WP: branch -/

/-- Branch LAW-012: WP покомпонентно проходит через ветвление предиката
(дизъюнкцию и конъюнкцию ветвей). -/
theorem basis_law012_branch (o : Op) (p q : Pred) :
    wp o (.por p q) = .por (wp o p) (wp o q) ∧
    wp o (.pand p q) = .pand (wp o p) (wp o q) :=
  ⟨rfl, rfl⟩

/-! ### LAW-013 — коммутативность слияния: negative, boundary, repair -/

/-- Negative LAW-013: коммутативность не даёт сокращения — по результату
слияния ветвь не восстанавливается. -/
theorem basis_law013_negative :
    Belief.join ⟨true, true, true, true⟩ ⟨false, false, false, false⟩ =
      Belief.join ⟨true, true, true, true⟩ ⟨true, false, false, false⟩ ∧
    (⟨false, false, false, false⟩ : Belief) ≠ ⟨true, false, false, false⟩ := by
  refine ⟨by decide, by decide⟩

/-- Boundary LAW-013: границы полурешётки — нейтральный `bot` и поглощающий
`top` — коммутируют с любой ветвью. -/
theorem basis_law013_boundary (a : Belief) :
    Belief.join Belief.bot a = a ∧ Belief.join Belief.top a = Belief.top := by
  refine ⟨?_, ?_⟩
  · rw [Belief.join_comm]; exact Belief.join_bot a
  · rw [Belief.join_comm]; exact Belief.join_top a

/-- Repair LAW-013: противоречие ветвей не «чинится» повторным слиянием —
починка возможна только отбрасыванием ветви-источника. -/
theorem basis_law013_repair :
    (Belief.join (EV.TRUE_KNOWN).toBelief (EV.FALSE_KNOWN).toBelief).collapse
        = EV.CONFLICT ∧
    Belief.join (Belief.join (EV.TRUE_KNOWN).toBelief (EV.FALSE_KNOWN).toBelief)
        (EV.TRUE_KNOWN).toBelief =
      Belief.join (EV.TRUE_KNOWN).toBelief (EV.FALSE_KNOWN).toBelief ∧
    ((EV.TRUE_KNOWN).toBelief).collapse = EV.TRUE_KNOWN := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### LAW-014 — ассоциативность слияния: positive, repair -/

/-- Positive LAW-014: конкретная тройка различных ветвей ассоциативна в
исправленной алгебре. -/
theorem basis_law014_positive :
    Belief.join (Belief.join ⟨true, false, true, false⟩ ⟨false, true, false, false⟩)
        ⟨false, false, false, true⟩ =
      Belief.join ⟨true, false, true, false⟩
        (Belief.join ⟨false, true, false, false⟩ ⟨false, false, false, true⟩) := by
  decide

/-- Repair LAW-014: у напечатанной таблицы ровно восемь неассоциативных
троек, а у исправленной алгебры их нет ни одной — починка полная. -/
theorem basis_law014_repair :
    specAssocFailures.card = 8 ∧
    ∀ a b c : Belief,
      Belief.join (Belief.join a b) c = Belief.join a (Belief.join b c) :=
  ⟨joinSpec_assoc_failures_card, Belief.join_assoc⟩

/-! ### LAW-015 — идемпотентность: negative, boundary, repair -/

/-- Negative LAW-015: идемпотентность — только про повтор одной ветви;
слияние двух разных ветвей строго информативнее каждой из них. -/
theorem basis_law015_negative :
    Belief.join ⟨true, false, true, false⟩ ⟨false, true, false, false⟩ ≠
      ⟨true, false, true, false⟩ ∧
    Belief.join ⟨true, false, true, false⟩ ⟨false, true, false, false⟩ ≠
      ⟨false, true, false, false⟩ := by
  refine ⟨by decide, by decide⟩

/-- Boundary LAW-015: границы списочного слияния — пустой список даёт `bot`,
одноэлементный — саму ветвь. -/
theorem basis_law015_boundary (a : Belief) :
    Belief.joinList [] = Belief.bot ∧ Belief.joinList [a] = a := by
  refine ⟨rfl, ?_⟩
  rw [Belief.joinList_cons, Belief.joinList_nil, Belief.join_bot]

/-- Repair LAW-015: починка добавлением недостающего свидетельства
одноразова — повторное добавление той же ветви ничего не меняет. -/
theorem basis_law015_repair (a b : Belief) :
    Belief.join (Belief.join a b) b = Belief.join a b := by
  rw [Belief.join_assoc, Belief.join_idem]

/-! ### LAW-016 — воссоздание: branch, repair -/

/-- Branch LAW-016: воссоздание в одной ветви не трогает объекты другой. -/
theorem basis_law016_branch :
    Step.legal ⟨[⟨1, .Destroyed, []⟩, ⟨2, .Available, []⟩]⟩ (.recreate 1 3) = true ∧
    (Step.apply ⟨[⟨1, .Destroyed, []⟩, ⟨2, .Available, []⟩]⟩ (.recreate 1 3)).phaseOf 2
      = some .Available := by
  refine ⟨by decide, by decide⟩

/-- Repair LAW-016: отвергнутое воссоздание чинится выбором свободного
идентификатора, и провенанс сохраняется. -/
theorem basis_law016_repair :
    Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 1) = false ∧
    Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2) = true ∧
    (Step.apply ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2)).find 2
      = some ⟨2, .Available, [1]⟩ := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### LAW-017 — инвалидация: boundary, branch, repair -/

/-- Boundary LAW-017: на границе инвалидации не доказаны ни `P`, ни `¬P`. -/
theorem basis_law017_boundary :
    eval (MODIFY_X.exec (CALIBRATE_X.exec (CREATE_X.exec s0))) (.factExists "Calibrated")
        = .UNKNOWN ∧
    eval (MODIFY_X.exec (CALIBRATE_X.exec (CREATE_X.exec s0)))
        (.pnot (.factExists "Calibrated")) = .UNKNOWN := by
  refine ⟨by decide, by decide⟩

/-- Branch LAW-017: инвалидация одного предиката не задевает остальных. -/
theorem basis_law017_branch :
    (MODIFY_X.exec (CALIBRATE_X.exec (CREATE_X.exec s0))).factStatus "X"
      = .TRUE_KNOWN := by decide

/-- Repair LAW-017: обесцененное знание восстанавливается повторной
калибровкой. -/
theorem basis_law017_repair :
    (CALIBRATE_X.exec (MODIFY_X.exec (CALIBRATE_X.exec (CREATE_X.exec s0)))).factStatus
      "Calibrated" = .TRUE_KNOWN := by decide

/-! ### LAW-018 — оптимизатор ремонта: branch -/

/-- Branch LAW-018: оптимум по объединению ветвей кандидатов не хуже любого
кандидата любой ветви — слияние ветвей планирования не портит выбор. -/
theorem basis_law018_branch (l₁ l₂ : List RVec) {v : RVec}
    (h : RVec.best (l₁ ++ l₂) = some v) :
    (∀ a ∈ l₁, RVec.le v a) ∧ (∀ b ∈ l₂, RVec.le v b) :=
  ⟨fun a ha => RVec.best_le h a (List.mem_append_left _ ha),
   fun b hb => RVec.best_le h b (List.mem_append_right _ hb)⟩

end Polymath.OSA4
