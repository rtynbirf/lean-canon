/-
# OSA-3.2 — Conformance Matrix (§13)

Матрица соответствия: строка на оператор, тринадцать столбцов схемы §2
(`operator × input_type × output_type × preconditions × postconditions ×
preserves × destroys × effect_level × allowed_effects × forbidden_effects ×
uncertainty_model × reversibility × requires_authorization`).

Матрица нужна не для украшения, а для **механической проверки
непротиворечивости**: каждый контракт проверяется набором предикатов, а
каждый кейс Gold Dataset — на то, что все его операторы имеют строку в
матрице.  Результаты проверки доказаны вычислением.

Две находки аудита зафиксированы явно: контракты DEPLOY и DIAGNOSE из §6
нарушают правило §3 «переход на другой уровень — только на ±1»
(L2 → L4 и L1 → L3 внутри одного оператора).  Для обоих приведены
исправленные варианты, проходящие проверку.
-/
import RequestProject.OSA.Gold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

/-! ## Предикаты непротиворечивости контракта -/

/-- Объявленный уровень оператора совпадает с уровнем его выходного типа. -/
def Operator.levelDeclaredOk (o : Operator) : Bool :=
  o.outputType.level == o.level

/-- Порождаемые эффекты разрешены контрактом и не входят в число
запрещённых; разрешённое и запрещённое не пересекаются (§7 RULE 4C). -/
def Operator.effectsDeclaredOk (o : Operator) : Bool :=
  subsetOf o.producedEffects o.allowedEffects &&
  !o.producedEffects.any (fun e => o.forbiddenEffects.contains e) &&
  !o.allowedEffects.any (fun e => o.forbiddenEffects.contains e)

/-- Оператор не может одновременно сохранять и уничтожать инвариант. -/
def Operator.invariantsDeclaredOk (o : Operator) : Bool :=
  !o.preserves.any (fun i => o.destroys.contains i)

/-- Любое E4-действие требует авторизации (§4, политика авторизации). -/
def Operator.authorizationDeclaredOk (o : Operator) : Bool :=
  !(o.effectLevel == EffectLevel.E4) || o.requiresAuthorization

/-- Необратимый оператор обязан быть объявлен E4. -/
def Operator.reversibilityDeclaredOk (o : Operator) : Bool :=
  !(o.reversibility == Reversibility.irreversible) || o.effectLevel == EffectLevel.E4

/-- Оператор сдвигает уровень типа не более чем на единицу (§3, §7 RULE 6). -/
def Operator.levelShiftOk (o : Operator) : Bool :=
  levelGap o.inputType o.outputType ≤ 1

/-- Оператор, снижающий неопределённость, не должен одновременно её
добавлять по той же компоненте. -/
def Operator.uncertaintyDeclaredOk (o : Operator) : Bool :=
  !(o.uncertainty.aleatoric > 0 && o.reduction.aleatoric > 0) &&
  !(o.uncertainty.epistemic > 0 && o.reduction.epistemic > 0) &&
  !(o.uncertainty.model > 0 && o.reduction.model > 0) &&
  !(o.uncertainty.provenance > 0 && o.reduction.provenance > 0)

/-- Полная проверка строки матрицы. -/
def Operator.conformant (o : Operator) : Bool :=
  o.levelDeclaredOk && o.effectsDeclaredOk && o.invariantsDeclaredOk &&
  o.authorizationDeclaredOk && o.reversibilityDeclaredOk &&
  o.uncertaintyDeclaredOk && o.levelShiftOk

/-! ## Строка и матрица -/

/-- Строка Conformance Matrix — все тринадцать столбцов §13 плюс результат
проверки. -/
structure ConformanceRow where
  operator : String
  inputType : OSAType
  outputType : OSAType
  preconditions : List Fact
  postconditions : List Fact
  preserves : List Invariant
  destroys : List Invariant
  effectLevel : EffectLevel
  allowedEffects : List Effect
  forbiddenEffects : List Effect
  uncertainty : Uncert
  reversibility : Reversibility
  requiresAuthorization : Bool
  conformant : Bool
  deriving Repr, Inhabited

/-- Строка матрицы, порождённая контрактом оператора. -/
def Operator.row (o : Operator) : ConformanceRow where
  operator := o.id
  inputType := o.inputType
  outputType := o.outputType
  preconditions := o.pre
  postconditions := o.post
  preserves := o.preserves
  destroys := o.destroys
  effectLevel := o.effectLevel
  allowedEffects := o.allowedEffects
  forbiddenEffects := o.forbiddenEffects
  uncertainty := o.uncertainty
  reversibility := o.reversibility
  requiresAuthorization := o.requiresAuthorization
  conformant := o.conformant

/-- Полный каталог контрактов, покрывающий все операторы, встречающиеся
в Gold Dataset (включая доменные варианты). -/
def conformanceCatalog : List Operator :=
  goldRegistry ++
    [ MODEL_STRICT, MODEL_UNCERTAIN, EXECUTE_PLAN, DELETE, INDEX_EXTERNAL
    , AUTHORIZE_HUMAN, EXECUTE_IRREVERSIBLE, CERTIFY ]

/-- Conformance Matrix: строка на каждый контракт каталога. -/
def conformanceMatrix : List ConformanceRow := conformanceCatalog.map Operator.row

/-! ## Исправленные контракты для двух находок §6 -/

/-- DEPLOY, приведённый к правилу ±1: развёртывание принимает токен
авторизации (L3), а не бинарь (L2). -/
def DEPLOY_TOKEN : Operator :=
  { DEPLOY with
    id := "DEPLOY_TOKEN"
    inputType := .AuthorizationToken
    pre := [.Compiled, .Authorized] }

/-- DIAGNOSE, приведённый к правилу ±1: диагностика события даёт результат
анализа (L2), из которого решение уровня L3 выводится отдельным
оператором. -/
def DIAGNOSE_L2 : Operator :=
  { DIAGNOSE with
    id := "DIAGNOSE_L2"
    level := .L2
    outputType := .AnalysisResult }

/-! ## Результаты механической проверки -/

/-- Все контракты каталога непротиворечивы по объявлению уровня, эффектов,
инвариантов, авторизации, обратимости и неопределённости. -/
theorem catalog_local_checks :
    conformanceCatalog.all (fun o =>
      o.levelDeclaredOk && o.effectsDeclaredOk && o.invariantsDeclaredOk &&
      o.authorizationDeclaredOk && o.reversibilityDeclaredOk &&
      o.uncertaintyDeclaredOk) = true := by decide

/-- **Находка §13.1**: контракты DEPLOY и DIAGNOSE из §6 нарушают правило
±1 из §3 — и только они. -/
theorem catalog_level_shift_findings :
    (conformanceCatalog.filter (fun o => !o.levelShiftOk)).map (·.id) =
      ["DEPLOY", "DIAGNOSE"] := by decide

/-- Исправленные варианты обеих находок проходят полную проверку. -/
theorem repaired_contracts_conformant :
    DEPLOY_TOKEN.conformant = true ∧ DIAGNOSE_L2.conformant = true := by decide

/-- Все остальные контракты каталога полностью непротиворечивы. -/
theorem catalog_conformant_except_findings :
    (conformanceCatalog.filter (fun o => !o.conformant)).map (·.id) =
      ["DEPLOY", "DIAGNOSE"] := by decide

/-- Матрица улавливает утечку эффекта статически, ещё до всякой композиции:
контракт SILENT_WRITE не проходит проверку. -/
theorem silentWrite_not_conformant : SILENT_WRITE.conformant = false := by decide

/-- Идентификаторы контрактов каталога попарно различны: строка матрицы
однозначно определяется именем оператора. -/
theorem catalog_ids_nodup : (conformanceCatalog.map (·.id)).Nodup := by decide

/-- **§13**: каждый кейс Gold Dataset механически проверяем через
матрицу — каждый оператор каждого предложенного графа имеет строку. -/
theorem goldDataset_covered_by_matrix :
    goldDataset.all (fun g => g.composition.ops.all
      (fun o => (conformanceMatrix.map (·.operator)).contains o.id)) = true := by
  decide

/-! ## Отрисовка матрицы -/

private def effStr : EffectLevel → String
  | .E0 => "E0" | .E1 => "E1" | .E2 => "E2" | .E3 => "E3" | .E4 => "E4"

private def revStr : Reversibility → String
  | .reversible => "reversible"
  | .partiallyReversible => "partially_reversible"
  | .irreversible => "irreversible"

/-- Одна строка матрицы в текстовом виде. -/
def ConformanceRow.render (r : ConformanceRow) : String :=
  r.operator ++ " | " ++ typeStr r.inputType ++ " -> " ++ typeStr r.outputType ++
  " | eff " ++ effStr r.effectLevel ++
  " | " ++ revStr r.reversibility ++
  " | auth " ++ (if r.requiresAuthorization then "yes" else "no") ++
  " | unc " ++ toString r.uncertainty.total ++
  " | " ++ (if r.conformant then "OK" else "FINDING")

/-- Вся матрица в текстовом виде. -/
def conformanceMatrixRender : String :=
  String.intercalate "\n" (conformanceMatrix.map ConformanceRow.render)

#eval IO.println conformanceMatrixRender

end Polymath.OSA
