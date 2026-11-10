/-
# OSA-3.2 — визуализация (§18)

Отрисовка цепочки операторов в ASCII-арте и в формате Graphviz (DOT),
а также матрица совместимости типов: какой тип во что может быть
преобразован без оператора-посредника.

Визуализация здесь — не косметика: доказано, что она согласована
с компилятором.

* `chainTokens_mem` — в ASCII-цепочке присутствует каждый оператор
  композиции (ничего не теряется при отрисовке);
* `dotEdges_length` — число рёбер DOT-графа ровно на единицу меньше
  числа операторов (цепочка отрисовывается как цепочка, без разрывов);
* `dotEdges_sound` — все концы рёбер — операторы самой композиции;
* `compatMatrix_sound` — строка матрицы совместимости содержит ровно те
  типы, которые признаёт `typeCompatible`;
* `compat_same_level` — совместимость типов никогда не пересекает границу
  уровня L0–L4 (§3: переход между уровнями возможен только оператором);
* `pass_edges_typeCompatible` — у композиции с вердиктом `PASS` каждое
  нарисованное ребро является допустимым переходом типов.
-/
import RequestProject.OSA.Versioning
import RequestProject.OSA.Properties

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

/-! ## ASCII-арт цепочки -/

/-- Блок оператора. -/
def opBox (o : Operator) : String := "[" ++ o.id ++ "]"

/-- Стрелка, подписанная передаваемым типом. -/
def typeArrow (t : OSAType) : String := " --" ++ typeStr t ++ "--> "

/-- Токены ASCII-отрисовки цепочки. -/
def chainTokens : List Operator → List String
  | [] => ["(empty composition)"]
  | [o] => [opBox o, " ⇒ " ++ typeStr o.outputType]
  | o :: rest => opBox o :: typeArrow o.outputType :: chainTokens rest

/-- ASCII-отрисовка цепочки операторов (§18). -/
def renderChain (ops : List Operator) : String :=
  String.intercalate "" (chainTokens ops)

/-- Отрисовка цепочки вместе с вердиктом компилятора. -/
def renderCompiled (reg : List Operator) (c : Composition) : String :=
  let r := compile reg c
  "── " ++ c.caseId ++ " ──\n" ++
  "  " ++ typeStr c.initialType ++ " ⇒ " ++ renderChain c.ops ++ "\n" ++
  "  verdict: " ++ r.status.toStatusString ++ " / " ++ r.code.toCodeString ++
  (if r.suggestion == "" then "" else "\n  repair: " ++ r.suggestion)

/-- Отрисовка не теряет операторов: блок каждого оператора цепочки
присутствует среди токенов. -/
theorem chainTokens_mem :
    ∀ (ops : List Operator), ∀ o ∈ ops, opBox o ∈ chainTokens ops := by
  intro ops
  induction ops with
  | nil => intro o ho; exact absurd ho (by simp)
  | cons a rest ih =>
      intro o ho
      cases rest with
      | nil =>
          have : o = a := by simpa using ho
          subst this
          simp [chainTokens]
      | cons b rest' =>
          rcases List.mem_cons.mp ho with h | h
          · subst h; simp [chainTokens]
          · have := ih o h
            simp only [chainTokens, List.mem_cons]
            exact Or.inr (Or.inr this)

/-! ## Graphviz (DOT) -/

/-- Ребро DOT-графа: два оператора и передаваемый между ними тип. -/
structure DotEdge where
  src : String
  tgt : String
  label : String
  deriving Repr, DecidableEq, Inhabited

/-- Последовательные пары операторов цепочки. -/
def opPairs : List Operator → List (Operator × Operator)
  | a :: b :: rest => (a, b) :: opPairs (b :: rest)
  | _ => []

/-- Рёбра DOT-графа композиции. -/
def dotEdges (ops : List Operator) : List DotEdge :=
  (opPairs ops).map (fun p =>
    { src := p.1.id, tgt := p.2.id, label := typeStr p.1.outputType })

/-- Полный DOT-документ (§18). -/
def renderDot (title : String) (ops : List Operator) : String :=
  "digraph \"" ++ title ++ "\" {\n  rankdir=LR;\n" ++
  String.intercalate "\n"
    (ops.map (fun o =>
      "  \"" ++ o.id ++ "\" [label=\"" ++ o.id ++ "\\n" ++
        typeStr o.inputType ++ " → " ++ typeStr o.outputType ++ "\"];")) ++
  (if ops.isEmpty then "" else "\n") ++
  String.intercalate "\n"
    ((dotEdges ops).map (fun e =>
      "  \"" ++ e.src ++ "\" -> \"" ++ e.tgt ++ "\" [label=\"" ++ e.label ++ "\"];")) ++
  "\n}"

/-- Число последовательных пар на единицу меньше числа операторов. -/
theorem opPairs_length :
    ∀ ops : List Operator, (opPairs ops).length + 1 = ops.length ∨ ops = [] := by
  intro ops
  induction ops with
  | nil => exact Or.inr rfl
  | cons a rest ih =>
      cases rest with
      | nil => exact Or.inl rfl
      | cons b rest' =>
          rcases ih with h | h
          · exact Or.inl (by simp only [opPairs, List.length_cons] at *; omega)
          · exact absurd h (by simp)

/-- Цепочка отрисовывается как цепочка: рёбер ровно на одно меньше,
чем операторов. -/
theorem dotEdges_length (ops : List Operator) (h : ops ≠ []) :
    (dotEdges ops).length + 1 = ops.length := by
  rcases opPairs_length ops with hp | hp
  · simpa [dotEdges] using hp
  · exact absurd hp h

/-- Оба конца каждой пары — операторы самой цепочки. -/
theorem opPairs_sound :
    ∀ (ops : List Operator), ∀ p ∈ opPairs ops, p.1 ∈ ops ∧ p.2 ∈ ops := by
  intro ops
  induction ops with
  | nil => intro p hp; exact absurd hp (by simp [opPairs])
  | cons a rest ih =>
      intro p hp
      cases rest with
      | nil => exact absurd hp (by simp [opPairs])
      | cons b rest' =>
          rcases List.mem_cons.mp hp with h | h
          · subst h; exact ⟨by simp, by simp⟩
          · obtain ⟨h1, h2⟩ := ih p h
            exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- Граф не изобретает узлов: каждое ребро соединяет операторы цепочки. -/
theorem dotEdges_sound (ops : List Operator) (e : DotEdge) (he : e ∈ dotEdges ops) :
    e.src ∈ ops.map (·.id) ∧ e.tgt ∈ ops.map (·.id) := by
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp he
  obtain ⟨h1, h2⟩ := opPairs_sound ops p hp
  subst hpe
  exact ⟨List.mem_map_of_mem h1, List.mem_map_of_mem h2⟩

/-! ## Согласованность визуализации с компилятором -/

/-- Если типовая диагностика молчит, первый стык уже совместим. -/
theorem typeDiag_head (reg : List Operator) (t : OSAType) (o : Operator)
    (rest : List Operator) (h : typeDiag reg t (o :: rest) = none) :
    typeCompatible t o.inputType = true := by
  by_cases hc : typeCompatible t o.inputType
  · exact hc
  · exfalso
    simp only [typeDiag, hc, Bool.false_eq_true, if_false] at h
    by_cases hg : 2 ≤ levelGap t o.inputType
    · simp [hg] at h
    · simp only [hg, if_false] at h
      cases hf : reg.find? (fun c => typeCompatible t c.inputType &&
                                     typeCompatible c.outputType o.inputType) with
      | some c => rw [hf] at h; exact absurd h (by simp)
      | none =>
          rw [hf] at h
          cases hf2 : findPath2 reg t o.inputType with
          | some q => rw [hf2] at h; exact absurd h (by simp)
          | none => rw [hf2] at h; exact absurd h (by simp)

/-- Если типовая диагностика молчит, то каждое ребро отрисованного графа —
допустимый переход типов. -/
theorem typeDiag_none_pairs (reg : List Operator) :
    ∀ (ops : List Operator) (t : OSAType), typeDiag reg t ops = none →
      ∀ p ∈ opPairs ops, typeCompatible p.1.outputType p.2.inputType = true := by
  intro ops
  induction ops with
  | nil => intro t _ p hp; exact absurd hp (by simp [opPairs])
  | cons a rest ih =>
      intro t h p hp
      have hc : typeCompatible t a.inputType = true := typeDiag_head reg t a rest h
      have hrest : typeDiag reg a.outputType rest = none := by
        simp only [typeDiag, hc, if_true] at h; exact h
      cases rest with
      | nil => exact absurd hp (by simp [opPairs])
      | cons b rest' =>
          rcases List.mem_cons.mp hp with hq | hq
          · subst hq
            exact typeDiag_head reg a.outputType b rest' hrest
          · exact ih a.outputType hrest p hq

/-- **Согласованность §18 с §7.** У композиции с вердиктом `PASS` каждое
ребро DOT-графа соединяет операторы с совместимыми типами. -/
theorem pass_edges_typeCompatible (reg : List Operator) (c : Composition)
    (h : (compile reg c).status = Status.PASS) :
    ∀ p ∈ opPairs c.ops, typeCompatible p.1.outputType p.2.inputType = true := by
  have h1 : (diagL1 reg c).isNone = true := (pass_implies_four_levels reg c h).1
  have hnone : typeDiag reg c.initialType c.ops = none := by
    simpa [diagL1] using Option.isNone_iff_eq_none.mp h1
  exact typeDiag_none_pairs reg c.ops c.initialType hnone

/-! ## Матрица совместимости типов -/

/-- Полный перечень типов OSA-3.2 (§3). -/
def allTypes : List OSAType :=
  [ .ObjectState, .PhysicalMeasurement, .EnvironmentState, .RawSignal
  , .MeasuredValue, .RegisteredEvent, .CalibratedValue, .SensorReading
  , .Observation, .DetectedEvent, .RecognitionResult, .IndexEntry, .Dataset
  , .DeletionRecord
  , .Model, .Specification, .FormalDescription, .EnergyModel, .SimulationResult
  , .ValidationResult, .VerificationResult, .SourceCode, .CompiledBinary
  , .Algorithm, .Hypothesis, .ExperimentalResult, .ClusterModel, .AnalysisResult
  , .ComparisonResult, .EvaluationResult, .Requirements, .Design, .Representation
  , .FormalAxiom
  , .Plan, .Decision, .PolicyChoice, .AuthorizationToken, .DiagnosticResult
  , .SystemStateChange, .Deployment, .PhysicalActuation, .IrreversibleChange ]

/-- Перечень типов полон. -/
theorem allTypes_complete : ∀ t : OSAType, t ∈ allTypes := by decide

/-- Перечень типов не содержит повторов. -/
theorem allTypes_nodup : allTypes.Nodup := by decide

/-- Строка матрицы совместимости: тип и всё, во что он приводится
без оператора-посредника. -/
structure CompatRow where
  source : OSAType
  targets : List OSAType
  deriving Repr, Inhabited

/-- Строка матрицы для данного типа. -/
def compatRow (t : OSAType) : CompatRow :=
  { source := t, targets := allTypes.filter (fun u => typeCompatible t u) }

/-- Матрица совместимости типов (§18). -/
def compatMatrix : List CompatRow := allTypes.map compatRow

/-- Строка матрицы содержит ровно те типы, которые признаёт `typeCompatible`. -/
theorem compatMatrix_sound (t u : OSAType) :
    u ∈ (compatRow t).targets ↔ typeCompatible t u = true := by
  constructor
  · intro h
    exact (List.mem_filter.mp h).2
  · intro h
    exact List.mem_filter.mpr ⟨allTypes_complete u, h⟩

/-- В матрице ровно одна строка на каждый тип. -/
theorem compatMatrix_length : compatMatrix.length = allTypes.length :=
  List.length_map _

/-- Матрица рефлексивна: любой тип совместим сам с собой. -/
theorem compat_refl (t : OSAType) : t ∈ (compatRow t).targets :=
  (compatMatrix_sound t t).mpr (by simp [typeCompatible])

/-- **§3.** Совместимость типов никогда не пересекает границу уровня:
переход на другой уровень возможен только через оператор. -/
theorem compat_same_level :
    ∀ a b : OSAType, typeCompatible a b = true → a.level = b.level := by decide

/-- Отрисовка матрицы совместимости. -/
def renderCompatMatrix : String :=
  String.intercalate "\n"
    (compatMatrix.filter (fun r => 1 < r.targets.length) |>.map (fun r =>
      "  " ++ typeStr r.source ++ " → " ++
        String.intercalate ", " (r.targets.map OSAType.name)))

/-! ## Демонстрация -/

/-- Демонстрационная цепочка: полная траектория §3. -/
def visualDemo : Composition :=
  { goldBase with
    caseId := "visual demo"
    ops := [MEASURE, CALIBRATE, MODEL, VALIDATE, DECIDE, AUTHORIZE, EXECUTE] }

#eval IO.println (renderCompiled goldRegistry visualDemo)

#eval IO.println (renderDot "visual demo" visualDemo.ops)

#eval IO.println renderCompatMatrix

end Polymath.OSA
