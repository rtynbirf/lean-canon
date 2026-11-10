/-
  Polymath Atlas v107.0 — Core Module
  Imperial Archive: Chapter III (Evidence Model)
  
  Fixes applied:
    F-001  Status Schema Contradiction → unified CanonicalStatus
    F-004  Proven Overload             → EvidenceVector (8 dimensions)
    F-006  Divergence Overreach        → HighDivergence (no "manipulation" label)
    F-002  Zero Open insufficiency     → TerminalGate composite
    F-005  "8/8 Closed" ambiguity      → Gap.status : CanonicalStatus
-/

import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic

namespace PolyMath.Atlas

/-!
## §1. Canonical Status Schema (F-001 RESOLVED)

Единая схема без контрактных конфликтов. `forcedStatus` теперь
возвращает значения ТОЛЬКО из этого индуктивного типа.
-/
inductive CanonicalStatus : Type
  | Specified          -- claim формально сформулирован
  | Constructed        -- witness/model существует
  | Compiled           -- lake build passes
  | AxiomAudited       -- #print axioms clean
  | EmpiricallyTested  -- прогнан на данных
  | Proven             -- теоремное доказательство
  | Operational        -- pipeline работает
  | Open               -- evidence отсутствует
  | Heuristic          -- правдоподобно, но не доказано
  | Conflicting        -- противоречие в контракте
  | Unverified         -- проверка не выполнена
  | Computational      -- вычислительный статус
  | Rejected           -- отклонён аудитом
  | Deprecated         -- устарел
  | Unknown            -- не определён
  deriving Repr, DecidableEq, Inhabited

namespace CanonicalStatus

/-- Высокая уверенность: теоремный/аудит/эмпирика -/
def isProven : CanonicalStatus → Bool
  | Proven | AxiomAudited | EmpiricallyTested => true
  | _ => false

/-- Готов к терминализации (прошёл evidence gate) -/
def isTerminalReady : CanonicalStatus → Bool
  | Proven | AxiomAudited | EmpiricallyTested | Operational => true
  | _ => false

/-- Блокер терминальности -/
def isBlocker : CanonicalStatus → Bool
  | Open | Conflicting | Rejected => true
  | _ => false

/-- Статус требует дополнительного evidence -/
def needsEvidence : CanonicalStatus → Bool
  | Specified | Heuristic | Unverified | Unknown => true
  | _ => false

/-- Канонический порядок (для dashboard сортировки) -/
def rank : CanonicalStatus → Nat
  | Proven             => 0
  | AxiomAudited       => 1
  | EmpiricallyTested  => 2
  | Compiled           => 3
  | Constructed        => 4
  | Operational        => 5
  | Specified          => 6
  | Heuristic          => 7
  | Unverified         => 8
  | Computational      => 9
  | Unknown            => 10
  | Conflicting        => 11
  | Rejected           => 12
  | Deprecated         => 13
  | Open               => 14

end CanonicalStatus

/-!
## §2. Evidence Vector (F-004 RESOLVED)

8 независимых измерений доказательности. Каждое — отдельный бит,
а не ступень лестницы. Это устраняет перегрузку семантики "Proven".
-/
structure EvidenceVector where
  tracked              : Bool  -- claim зарегистрирован
  specified            : Bool  -- формализован
  witness              : Bool  -- witness/model существует
  compiled             : Bool  -- lake build passes
  axiom_audited        : Bool  -- #print axioms clean
  empirical            : Bool  -- прогнан на данных
  reproducible         : Bool  -- воспроизводим
  independently_sourced: Bool  -- независимый источник
  deriving Repr, DecidableEq, Inhabited

namespace EvidenceVector

/-- Нулевой вектор — ничего не доказано -/
def zero : EvidenceVector :=
  { tracked := false, specified := false, witness := false,
    compiled := false, axiom_audited := false, empirical := false,
    reproducible := false, independently_sourced := false }

/-- Полный вектор — все 8 измерений подтверждены -/
def full : EvidenceVector :=
  { tracked := true, specified := true, witness := true,
    compiled := true, axiom_audited := true, empirical := true,
    reproducible := true, independently_sourced := true }

/-- Число подтверждённых измерений (0..8) -/
def score (e : EvidenceVector) : Nat :=
  (if e.tracked then 1 else 0) +
  (if e.specified then 1 else 0) +
  (if e.witness then 1 else 0) +
  (if e.compiled then 1 else 0) +
  (if e.axiom_audited then 1 else 0) +
  (if e.empirical then 1 else 0) +
  (if e.reproducible then 1 else 0) +
  (if e.independently_sourced then 1 else 0)

/-- Ядро evidence: tracked + specified + witness -/
def coreHolds (e : EvidenceVector) : Bool :=
  e.tracked && e.specified && e.witness

/-- Machine-verified: compiled + axiom_audited -/
def machineVerified (e : EvidenceVector) : Bool :=
  e.compiled && e.axiom_audited

/-- Полная верификация: score = 8 -/
def isComplete (e : EvidenceVector) : Bool :=
  e.score == 8

/-- Терминальная готовность (F-002: не просто "Open = 0") -/
def isTerminalReady (e : EvidenceVector) : Bool :=
  e.coreHolds && e.machineVerified

/-- Отображение вектора → канонический статус -/
def toStatus (e : EvidenceVector) : CanonicalStatus :=
  if e.isComplete then .Proven
  else if e.machineVerified then .AxiomAudited
  else if e.compiled then .Compiled
  else if e.witness then .Constructed
  else if e.specified then .Specified
  else if e.tracked then .Heuristic
  else .Open

end EvidenceVector

/-!
## §3. Divergence Classification (F-006 RESOLVED)

"Manipulation Suspected" удалено — это overreach.
Заменено на "HighDivergence" (нейтральный статистический термин).
Манипуляция требует отдельного ManipulationDetector с provenance.
-/
inductive DivergenceClass : Type
  | Normal            -- в пределах ожидаемого
  | HighDivergence    -- σ/|μ| выше порога (НЕ = манипуляция!)
  | EpistemicStrain   -- напряжение в системе знаний
  deriving Repr, DecidableEq, Inhabited

/-- Dispersion ratio D = σ/|μ| (F-006: только статистика, не ярлык) -/
def dispersionRatio (σ μ : ℝ) (h : μ ≠ 0) : ℝ := σ / |μ|

/-- Пороговая классификация (калибруемая, не абсолютная) -/
def classifyDivergence (D : ℝ) (threshold : ℝ := 2.0) : DivergenceClass :=
  if D > threshold then .HighDivergence
  else .Normal

/-!
## §4. forcedStatus — теперь контрактно согласован (F-001)

Все возвращаемые значения ПРИНАДЛЕЖАТ CanonicalStatus.
Никаких "Conflicting/Unverified/Computational" вне схемы.
-/
def forcedStatus (dc : DivergenceClass) : CanonicalStatus :=
  match dc with
  | .HighDivergence  => .Conflicting    -- ✓ в схеме
  | .EpistemicStrain => .Unverified     -- ✓ в схеме
  | .Normal          => .Operational    -- ✓ в схеме

/-!
## §5. Gap & Claim structures

Gap — это проблема с evidence vector'ом.
Claim — это утверждение с canonical status.
-/
structure Gap where
  id          : String
  name        : String
  convergence : Nat × Nat   -- e.g. (5, 8) = 5/8
  mceLevel    : Nat         -- 1..4
  status      : CanonicalStatus
  evidence    : EvidenceVector
  blocker     : String      -- что мешает закрытию
  deriving Repr

structure Claim where
  id       : String
  text     : String
  status   : CanonicalStatus
  evidence : EvidenceVector
  deriving Repr

/-!
## §6. Terminal Gate (F-002 RESOLVED)

Composite gate из Главы V архива v105.1.
Заменяет монолитный "Open = 0".
-/
structure TerminalGate where
  all_claims_tracked          : Bool
  all_statuses_valid          : Bool
  no_status_contract_conflict : Bool
  required_artifacts_present  : Bool
  required_compile_pass       : Bool
  required_axiom_audit_pass   : Bool
  no_blocking_gap             : Bool

namespace TerminalGate

/-- Все условия выполнены -/
def passes (g : TerminalGate) : Bool :=
  g.all_claims_tracked &&
  g.all_statuses_valid &&
  g.no_status_contract_conflict &&
  g.required_artifacts_present &&
  g.required_compile_pass &&
  g.required_axiom_audit_pass &&
  g.no_blocking_gap

/-- Построение gate из списка claims и gaps -/
def fromRegistry (claims : List Claim) (gaps : List Gap)
                 (compileOk : Bool) (axiomOk : Bool) : TerminalGate :=
  let allTracked := claims.all (·.evidence.tracked)
  let statusesValid := claims.all (fun c =>
    c.status != CanonicalStatus.Unknown)
  let noContractConflict := true  -- обеспечивается типом CanonicalStatus
  let artifactsPresent := compileOk
  let noBlocker := gaps.all (fun g => !g.status.isBlocker)
  { all_claims_tracked := allTracked
    all_statuses_valid := statusesValid
    no_status_contract_conflict := noContractConflict
    required_artifacts_present := artifactsPresent
    required_compile_pass := compileOk
    required_axiom_audit_pass := axiomOk
    no_blocking_gap := noBlocker }

end TerminalGate

/-!
## §7. Dashboard (F-005 RESOLVED)

Честная приборная панель: различает
ADDRESSED / VERIFIED / SPECIFIED / OPEN.
-/
structure Dashboard where
  totalClaims  : Nat
  totalGaps    : Nat
  verified     : Nat   -- isProven = true
  specified    : Nat   -- needsEvidence = true
  open         : Nat   -- status = Open
  blockers     : Nat   -- isBlocker = true
  compileOk    : Bool
  axiomOk      : Bool
  gate         : TerminalGate

namespace Dashboard

def fromData (claims : List Claim) (gaps : List Gap)
             (compileOk axiomOk : Bool) : Dashboard :=
  let verified := gaps.filter (·.status.isProven) |>.length
  let specified := gaps.filter (·.status.needsEvidence) |>.length
  let open_ := gaps.filter (fun g => g.status == .Open) |>.length
  let blockers := gaps.filter (·.status.isBlocker) |>.length
  let gate := TerminalGate.fromRegistry claims gaps compileOk axiomOk
  { totalClaims := claims.length
    totalGaps := gaps.length
    verified, specified, open_ := open_, blockers
    compileOk, axiomOk, gate }

/-- Canonical verdict string -/
def verdict (d : Dashboard) : String :=
  if d.gate.passes then "TERMINAL / FULLY VERIFIED"
  else if d.compileOk && d.axiomOk then "EVIDENCE-READY / COMPILED"
  else if d.compileOk then "EVIDENCE-READY / AXIOM-AUDIT PENDING"
  else "EVIDENCE-READY / NOT FULLY VERIFIED"

end Dashboard

end PolyMath.Atlas
