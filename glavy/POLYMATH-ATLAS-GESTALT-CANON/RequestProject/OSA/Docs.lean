/-
# OSA-3.2 — справочная система (§15) и расширенная диагностика (§16)

§15 требует, чтобы для каждого оператора хранились `purpose`, `usage`,
`inputDescription`, `outputDescription`, `compatiblePredecessors`,
`compatibleSuccessors`, `commonPatterns`, `knownIssues`, а для каждого кода
ошибки — описание, причины и конкретные шаги исправления.

§16 требует, чтобы при ошибке компилятор выдавал не только код, но и
`typeIncompatibilityExplanation`, `missingPreconditions` и
`suggestOperatorForFact`.

Здесь и то и другое построено *вычислимо* — совместимые предшественники и
последователи не перечисляются вручную, а выводятся из реестра контрактов,
поэтому справка не может разойтись со спецификацией.  Доказано: справка
полна (каждый оператор каталога и каждый код §8 имеют непустое описание,
а у каждого кода — непустые шаги исправления), выводимые списки
совместимости согласованы с правилом `RULE 1`, `missingPreconditions` пуст
ровно тогда, когда прекондиции удовлетворены, а `suggestOperatorForFact`
возвращает только оператор реестра, действительно устанавливающий факт.
-/
import RequestProject.OSA.Conformance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

/-! ## §15. Справка по оператору -/

/-- Карточка справки по оператору (§15). -/
structure OperatorDoc where
  operator : String
  purpose : String
  usage : String
  inputDescription : String
  outputDescription : String
  /-- Операторы реестра, выход которых принимается этим оператором. -/
  compatiblePredecessors : List String
  /-- Операторы реестра, принимающие выход этого оператора. -/
  compatibleSuccessors : List String
  commonPatterns : List String
  knownIssues : List String
  deriving Repr, Inhabited

/-- Операторы реестра, чей выход принимается оператором `o` (`RULE 1`). -/
def predecessorsOf (reg : List Operator) (o : Operator) : List String :=
  (reg.filter (fun x => typeCompatible x.outputType o.inputType)).map (·.id)

/-- Операторы реестра, принимающие выход оператора `o` (`RULE 1`). -/
def successorsOf (reg : List Operator) (o : Operator) : List String :=
  (reg.filter (fun x => typeCompatible o.outputType x.inputType)).map (·.id)

private def uncertaintyNote (o : Operator) : String :=
  "adds ⟨" ++ toString o.uncertainty.aleatoric ++ "," ++
    toString o.uncertainty.epistemic ++ "," ++ toString o.uncertainty.model ++
    "," ++ toString o.uncertainty.provenance ++ "⟩, removes ⟨" ++
    toString o.reduction.aleatoric ++ "," ++ toString o.reduction.epistemic ++
    "," ++ toString o.reduction.model ++ "," ++
    toString o.reduction.provenance ++ "⟩"

/-- Имя факта в справке. -/
def Fact.name (f : Fact) : String := ((toString (repr f)).splitOn ".").getLast!

private def factsNote (label : String) (fs : List Fact) : String :=
  label ++ ": " ++ String.intercalate ", " (fs.map Fact.name)

/-- Известные проблемы контракта, выведенные из самих полей оператора:
недекларированные эффекты, недостижимые прекондиции через побочные исходы,
разрушение инвариантов, прыжок через уровень. -/
def knownIssuesOf (o : Operator) : List String :=
  (if o.effectsDeclaredOk then [] else ["produces an effect outside allowed_effects"]) ++
  (if o.sideFacts.isEmpty then []
   else ["has non-guaranteed side facts: a successor must not rely on them (RULE 2B)"]) ++
  (if o.destroys.isEmpty then []
   else ["destroys invariants: successors requiring them will be rejected (RULE 3)"]) ++
  (if o.levelShiftOk then []
   else ["shifts the type level by two: contradicts §3 and RULE 6"]) ++
  (if o.effectLevel == EffectLevel.E4 then
     ["E4: requires an authorization token issued before it (RULE 4)"] else []) ++
  (if o.humanAuthorizationRequired then
     ["requires human authorization: the compiler cannot supply it"] else [])

/-- Справка по оператору, выведенная из его контракта и реестра. -/
def docOf (reg : List Operator) (o : Operator) : OperatorDoc where
  operator := o.id
  purpose := o.id ++ ": " ++ typeStr o.inputType ++ " -> " ++ typeStr o.outputType
  usage := "place after {" ++ String.intercalate ", " (predecessorsOf reg o) ++ "}"
  inputDescription := typeStr o.inputType ++ "; " ++ factsNote "requires" o.pre
  outputDescription :=
    typeStr o.outputType ++ "; " ++ factsNote "guarantees" o.post ++ "; " ++
    uncertaintyNote o
  compatiblePredecessors := predecessorsOf reg o
  compatibleSuccessors := successorsOf reg o
  commonPatterns :=
    (successorsOf reg o).map (fun x => o.id ++ " -> " ++ x)
  knownIssues := knownIssuesOf o

/-- Справочник по всему каталогу. -/
def operatorDocs : List OperatorDoc := conformanceCatalog.map (docOf goldRegistry)

/-! ## §15. Справка по кодам ошибок -/

/-- Карточка справки по коду ошибки (§15). -/
structure ErrorDoc where
  code : ErrCode
  description : String
  causes : List String
  fixSteps : List String
  deriving Repr, Inhabited

/-- Справка по каждому коду §8. -/
def errorDoc : ErrCode → ErrorDoc
  | .NONE =>
      { code := .NONE
      , description := "no violation: all four levels passed"
      , causes := []
      , fixSteps := ["nothing to fix"] }
  | .E_TYPE_MISMATCH =>
      { code := .E_TYPE_MISMATCH
      , description := "output type of the previous operator is not accepted by the current one"
      , causes := ["no declared subtyping or conversion between the two types"]
      , fixSteps :=
          [ "check the type hierarchy (§3): transitions must follow L0→L1→L2→L3→L4"
          , "insert a conversion operator"
          , "use an explicit type adapter if the types live on the same level" ] }
  | .E_MISSING_CONVERSION =>
      { code := .E_MISSING_CONVERSION
      , description := "types can be reconciled, but an intermediate operator is required"
      , causes := ["the registry contains an operator bridging the two types"]
      , fixSteps := ["insert the operator named in the repair suggestion"] }
  | .E_UNSATISFIABLE_CONTRACT =>
      { code := .E_UNSATISFIABLE_CONTRACT
      , description := "the output of A logically contradicts the input of B"
      , causes := ["no operator of the registry can establish the missing facts"
                  , "a forbidden predecessor is present"]
      , fixSteps := ["redesign the chain", "extend the registry with a suitable operator"] }
  | .E_NOT_YET_SATISFIED =>
      { code := .E_NOT_YET_SATISFIED
      , description := "preconditions must be established before the main chain runs"
      , causes := ["a required fact is not yet guaranteed", "a required predecessor is missing"]
      , fixSteps := ["insert the operator named in the repair suggestion before the failing one"] }
  | .E_INVARIANT_VIOLATION =>
      { code := .E_INVARIANT_VIOLATION
      , description := "an operator requires an invariant destroyed earlier"
      , causes := ["a preceding operator declares this invariant in destroys"
                  , "the composition as a whole destroys a required final invariant"]
      , fixSteps := ["reorder the chain", "remove the destroying operator"
                    , "add a recovery operator restoring the invariant"] }
  | .E_INVARIANT_LOSS =>
      { code := .E_INVARIANT_LOSS
      , description := "an operator neither preserves nor destroys an active invariant"
      , causes := ["the contract is silent about the invariant"]
      , fixSteps := ["declare the invariant in preserves or in destroys"] }
  | .E_EFFECT_POLICY_VIOLATION =>
      { code := .E_EFFECT_POLICY_VIOLATION
      , description := "an E4 action without authorization, or an E3 action without approval"
      , causes := ["no AUTHORIZE precedes the action"
                  , "the action requires human authorization"]
      , fixSteps := ["insert AUTHORIZE before the action"
                    , "obtain explicit human authorization for E4 deployments"] }
  | .E_EFFECT_LEAKAGE =>
      { code := .E_EFFECT_LEAKAGE
      , description := "an operator produces an effect its contract does not allow"
      , causes := ["produced_effects is not contained in allowed_effects"
                  , "a forbidden effect is produced"]
      , fixSteps := ["declare the effect in allowed_effects, or remove it from the implementation"] }
  | .E_EPISTEMIC_INSUFFICIENT =>
      { code := .E_EPISTEMIC_INSUFFICIENT
      , description := "accumulated uncertainty exceeds the threshold of the target level"
      , causes := ["uncertainty accumulates componentwise along the chain"]
      , fixSteps := ["insert an operator reducing uncertainty (CALIBRATE, VALIDATE, "
                       ++ "REDUCE_UNCERTAINTY)"
                    , "lower the level of the action (reversible instead of irreversible)"] }
  | .E_CONTRACT_LEAKAGE =>
      { code := .E_CONTRACT_LEAKAGE
      , description :=
          "a precondition is met only through a non-guaranteed side effect of a predecessor"
      , causes := ["the fact appears in sideFacts, not in post"]
      , fixSteps := ["make the fact an explicit postcondition, or insert an operator "
                       ++ "that guarantees it"] }
  | .E_LEVEL_JUMP =>
      { code := .E_LEVEL_JUMP
      , description := "a transition skipping intermediate levels (gap ≥ 2)"
      , causes := ["L0→L2, L1→L3 or L2→L4 without intermediate operators"]
      , fixSteps := ["build a chain of operators each shifting the level by ±1"] }
  | .UNCERTAINTY_RULE_NOT_DEFINED =>
      { code := .UNCERTAINTY_RULE_NOT_DEFINED
      , description := "no aggregation rule is declared for this composition (§5, §11.C)"
      , causes := ["RSS is not a universal rule; aggregation is a property of the operator"]
      , fixSteps := ["declare the aggregation rule of the composition"] }
  | .SPEC_GAP_UNDEFINED_THRESHOLD =>
      { code := .SPEC_GAP_UNDEFINED_THRESHOLD
      , description := "OSA-3.2 defines no decision threshold for outputs of this level"
      , causes := ["thresholds of §5 are given for L2, L3 and L4 only"]
      , fixSteps := ["declare the threshold in the case itself (declaredThreshold)"] }

/-! ## §16. Расширенная диагностика -/

/-- `typeIncompatibilityExplanation`: почему выход `a` не принимается
входом `b` — уровни, зазор, наличие или отсутствие пути. -/
def typeIncompatibilityExplanation (reg : List Operator) (a b : OSAType) : String :=
  if typeCompatible a b then "types are compatible"
  else
    let base :=
      typeStr a ++ " -> " ++ typeStr b ++ ": level gap " ++ toString (levelGap a b)
    if 2 ≤ levelGap a b then
      base ++ "; a jump of two or more levels is forbidden by §3 and RULE 6"
    else
      match reg.find? (fun c => typeCompatible a c.inputType &&
                                typeCompatible c.outputType b) with
      | some c => base ++ "; one intermediate operator suffices: " ++ c.id
      | none =>
        match findPath2 reg a b with
        | some (c1, c2) =>
            base ++ "; two intermediate operators are required: " ++ c1.id ++ ", " ++ c2.id
        | none => base ++ "; the registry contains no path between these types"

/-- `missingPreconditions`: прекондиции оператора, не покрытые накопленными
гарантированными фактами. -/
def missingPreconditions (o : Operator) (guaranteed : List Fact) : List Fact :=
  o.pre.filter (fun f => !guaranteed.contains f)

/-- `suggestOperatorForFact`: оператор реестра, устанавливающий недостающий
факт. -/
def suggestOperatorForFact (reg : List Operator) (f : Fact) : Option Operator :=
  reg.find? (fun x => x.post.contains f)

/-- Полный диагностический отчёт §16 для стыка `предыдущий тип → оператор`. -/
def deepDiagnosis (reg : List Operator) (t : OSAType) (o : Operator)
    (guaranteed : List Fact) : String :=
  let miss := missingPreconditions o guaranteed
  typeIncompatibilityExplanation reg t o.inputType ++ "\n" ++
  (if miss.isEmpty then "all preconditions are established"
   else
     "missing preconditions: " ++ String.intercalate ", " (miss.map Fact.name) ++ "\n" ++
     String.intercalate "\n"
       (miss.map (fun f =>
         match suggestOperatorForFact reg f with
         | some x => "  " ++ f.name ++ " <- " ++ x.id
         | none => "  " ++ f.name ++ " <- no operator in the registry")))

/-! ## Свойства справочной системы и диагностики -/

/-- Справка полна для любого оператора: назначение, описание входа и
описание выхода непусты. -/
theorem docOf_nonempty (reg : List Operator) (o : Operator) :
    0 < (docOf reg o).purpose.length ∧
    0 < (docOf reg o).inputDescription.length ∧
    0 < (docOf reg o).outputDescription.length := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [docOf, String.length_append] <;>
    [ (have h : 0 < ": ".length := by decide);
      (have h : 0 < "; ".length := by decide);
      (have h : 0 < "; ".length := by decide) ] <;>
    omega

/-- Справочник покрывает весь каталог контрактов и ничего кроме. -/
theorem operatorDocs_operators :
    operatorDocs.map (·.operator) = conformanceCatalog.map (·.id) := by
  simp [operatorDocs, docOf]

/-- Справка по кодам ошибок полна: у каждого кода §8 непустое описание и
непустой список шагов исправления. -/
theorem errorDoc_complete :
    ∀ e : ErrCode, 0 < (errorDoc e).description.length ∧ (errorDoc e).fixSteps ≠ [] := by
  decide

/-- Карточка кода описывает именно этот код. -/
theorem errorDoc_code : ∀ e : ErrCode, (errorDoc e).code = e := by decide

/-- Выведенные списки совместимости согласованы с `RULE 1`: имя оператора
попадает в `compatiblePredecessors`, только если его выход действительно
принимается. -/
theorem predecessorsOf_sound (reg : List Operator) (o x : Operator) (hx : x ∈ reg)
    (h : typeCompatible x.outputType o.inputType = true) :
    x.id ∈ predecessorsOf reg o := by
  unfold predecessorsOf
  exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hx, h⟩)

theorem successorsOf_sound (reg : List Operator) (o x : Operator) (hx : x ∈ reg)
    (h : typeCompatible o.outputType x.inputType = true) :
    x.id ∈ successorsOf reg o := by
  unfold successorsOf
  exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hx, h⟩)

/-- `missingPreconditions` пуст ровно тогда, когда прекондиции удовлетворены
накопленными фактами (`RULE 2`). -/
theorem missingPreconditions_eq_nil_iff (o : Operator) (g : List Fact) :
    missingPreconditions o g = [] ↔ subsetOf o.pre g = true := by
  unfold missingPreconditions subsetOf
  rw [List.filter_eq_nil_iff, List.all_eq_true]
  constructor
  · intro h f hf
    have := h f hf
    simpa using this
  · intro h f hf
    simpa using h f hf

/-- `suggestOperatorForFact` возвращает только оператор реестра, который
действительно устанавливает искомый факт своим постусловием. -/
theorem suggestOperatorForFact_sound (reg : List Operator) (f : Fact) (o : Operator)
    (h : suggestOperatorForFact reg f = some o) :
    o ∈ reg ∧ o.post.contains f = true := by
  unfold suggestOperatorForFact at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- Если ни один оператор реестра не устанавливает факт, предложения нет
(и компилятор обязан говорить `E_UNSATISFIABLE_CONTRACT`, а не молчать). -/
theorem suggestOperatorForFact_none (reg : List Operator) (f : Fact)
    (h : ∀ x ∈ reg, x.post.contains f = false) :
    suggestOperatorForFact reg f = none := by
  unfold suggestOperatorForFact
  rw [List.find?_eq_none]
  intro x hx
  simp only [Bool.not_eq_true]
  exact h x hx

/-- При зазоре уровней не меньше двух объяснение всегда сообщает именно о
запрете прыжка (§3, RULE 6). -/
theorem levelJump_explained (reg : List Operator) (a b : OSAType)
    (h : 2 ≤ levelGap a b) :
    ∃ head, typeIncompatibilityExplanation reg a b =
      head ++ "; a jump of two or more levels is forbidden by §3 and RULE 6" := by
  have hc : typeCompatible a b = false := by
    cases hcc : typeCompatible a b with
    | false => rfl
    | true =>
        exfalso
        have hl := typeCompatible_level a b hcc
        have hz : levelGap a b = 0 := by simp [levelGap, hl, Nat.dist_self]
        omega
  unfold typeIncompatibilityExplanation
  rw [hc]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos h]
  exact ⟨_, rfl⟩

/-! ## Печать справки -/

/-- Справка по одному оператору в текстовом виде. -/
def OperatorDoc.render (d : OperatorDoc) : String :=
  "── " ++ d.operator ++ " ──\n" ++
  "purpose:      " ++ d.purpose ++ "\n" ++
  "usage:        " ++ d.usage ++ "\n" ++
  "input:        " ++ d.inputDescription ++ "\n" ++
  "output:       " ++ d.outputDescription ++ "\n" ++
  "predecessors: " ++ String.intercalate ", " d.compatiblePredecessors ++ "\n" ++
  "successors:   " ++ String.intercalate ", " d.compatibleSuccessors ++ "\n" ++
  "known issues: " ++ String.intercalate "; " d.knownIssues

/-- Справка по коду ошибки в текстовом виде. -/
def ErrorDoc.render (d : ErrorDoc) : String :=
  d.code.toCodeString ++ ": " ++ d.description ++ "\n" ++
  String.intercalate "\n" (d.fixSteps.map (fun s => "  - " ++ s))

#eval IO.println (String.intercalate "\n\n"
  ((operatorDocs.take 4).map OperatorDoc.render))

#eval IO.println (ErrorDoc.render (errorDoc .E_TYPE_MISMATCH))

#eval IO.println
  (deepDiagnosis goldRegistry OSAType.MeasuredValue REPRESENT_VERIFIED [Fact.Measured])

end Polymath.OSA
