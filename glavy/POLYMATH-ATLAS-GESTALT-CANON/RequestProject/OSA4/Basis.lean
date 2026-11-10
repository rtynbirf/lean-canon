/-
# OSA-4.0 — минимальный базисный набор проверок (§13)

Кодекс требует: «для каждого закона нужен минимальный набор контрпримеров:
positive, negative, boundary, branch и repair… при 18 законах это
потенциально 90 проверочных позиций».  Этот модуль ведёт **машинно
проверяемый учёт покрытия**: какие позиции закрыты доказанными кейсами
проекта, а какие ещё нет.

Все записи ссылаются на реально существующие доказанные утверждения
(`TortureSet.lean`, `Identity.lean`, `Epistemic.lean`, `Repair.lean`,
`BasisWitnesses.lean`).  Итоговая теорема `coverage_complete` показывает
вычислением, что закрыты все 90 позиций: у каждого из 18 законов есть
свидетель каждого из пяти видов.
-/
import RequestProject.OSA4.Lawbook
import RequestProject.OSA4.BasisWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace Polymath.OSA4

/-- Вид проверочной позиции базисного набора. -/
inductive BasisKind
  /-- Сценарий, который должен пройти. -/
  | Positive
  /-- Сценарий, который должен быть отвергнут. -/
  | Negative
  /-- Граничный случай (UNKNOWN, пороги). -/
  | Boundary
  /-- Слияние ветвей. -/
  | Branch
  /-- Проверка ремонта. -/
  | Repair
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Закрытая позиция базисного набора: закон, вид проверки и имя доказанного
утверждения-свидетеля. -/
structure Coverage where
  /-- Проверяемый закон. -/
  law : LawId
  /-- Вид проверки. -/
  kind : BasisKind
  /-- Имя доказанного утверждения проекта. -/
  witness : String
  deriving DecidableEq, Repr, Inhabited

/-- Закрытые позиции базисного набора. -/
def coverage : List Coverage :=
  [ ⟨.LAW_004, .Negative, "torture_T04a_resurrection_rejected"⟩,
    ⟨.LAW_004, .Positive, "torture_T04b_recreation_legal"⟩,
    ⟨.LAW_005, .Positive, "law005_consume_iff_available"⟩,
    ⟨.LAW_005, .Negative, "T12_double_consume"⟩,
    ⟨.LAW_006, .Positive, "T02_pass"⟩,
    ⟨.LAW_006, .Negative, "T03_liveness_violation"⟩,
    ⟨.LAW_006, .Boundary, "T11_invalidate_live"⟩,
    ⟨.LAW_007, .Positive, "T01_fixed_pass"⟩,
    ⟨.LAW_007, .Boundary, "T05_undecidable"⟩,
    ⟨.LAW_009, .Negative, "uncertainty_drop_needs_evidence"⟩,
    ⟨.LAW_011, .Positive, "T13_repaired_pass"⟩,
    ⟨.LAW_011, .Negative, "T13_auth_denied_reject"⟩,
    ⟨.LAW_011, .Repair, "T13_missing_authorization"⟩,
    ⟨.LAW_012, .Positive, "law012_wp_sound"⟩,
    ⟨.LAW_013, .Branch, "torture_T09_conflict"⟩,
    ⟨.LAW_014, .Branch, "torture_T08_presence_vs_truth"⟩,
    ⟨.LAW_015, .Branch, "joinList_duplicate"⟩,
    ⟨.LAW_016, .Positive, "recreate_provenance"⟩,
    ⟨.LAW_017, .Negative, "law017_invalidate_not_refute"⟩,
    ⟨.LAW_018, .Repair, "torture_T15_safe_beats_cheap"⟩,
    ⟨.LAW_001, .Positive, "TypeLattice.isSubtype_refl"⟩,
    ⟨.LAW_001, .Boundary, "basis_law001_boundary"⟩,
    ⟨.LAW_002, .Positive, "basis_law002_positive"⟩,
    ⟨.LAW_002, .Negative, "basis_law002_negative"⟩,
    ⟨.LAW_003, .Positive, "basis_law003_positive"⟩,
    ⟨.LAW_003, .Negative, "basis_law003_negative"⟩,
    ⟨.LAW_003, .Boundary, "basis_law003_boundary"⟩,
    ⟨.LAW_007, .Negative, "basis_law007_negative"⟩,
    ⟨.LAW_007, .Repair, "basis_law007_repair"⟩,
    ⟨.LAW_008, .Positive, "basis_law008_positive"⟩,
    ⟨.LAW_008, .Negative, "basis_law008_negative"⟩,
    ⟨.LAW_008, .Boundary, "basis_law008_boundary"⟩,
    ⟨.LAW_008, .Branch, "basis_law008_branch"⟩,
    ⟨.LAW_009, .Positive, "basis_law009_positive"⟩,
    ⟨.LAW_009, .Boundary, "basis_law009_boundary"⟩,
    ⟨.LAW_010, .Positive, "basis_law010_positive"⟩,
    ⟨.LAW_010, .Negative, "basis_law010_negative"⟩,
    ⟨.LAW_011, .Boundary, "basis_law011_boundary"⟩,
    ⟨.LAW_012, .Negative, "basis_law012_negative"⟩,
    ⟨.LAW_012, .Boundary, "basis_law012_boundary"⟩,
    ⟨.LAW_012, .Repair, "basis_law012_repair"⟩,
    ⟨.LAW_013, .Positive, "basis_law013_positive"⟩,
    ⟨.LAW_014, .Negative, "basis_law014_negative"⟩,
    ⟨.LAW_014, .Boundary, "basis_law014_boundary"⟩,
    ⟨.LAW_015, .Positive, "basis_law015_positive"⟩,
    ⟨.LAW_016, .Negative, "basis_law016_negative"⟩,
    ⟨.LAW_016, .Boundary, "basis_law016_boundary"⟩,
    ⟨.LAW_017, .Positive, "basis_law017_positive"⟩,
    ⟨.LAW_018, .Negative, "basis_law018_negative"⟩,
    ⟨.LAW_018, .Boundary, "basis_law018_boundary"⟩,
    ⟨.LAW_018, .Positive, "law018_repair_sound"⟩,
    ⟨.LAW_001, .Negative, "basis_law001_negative"⟩,
    ⟨.LAW_001, .Branch, "basis_law001_branch"⟩,
    ⟨.LAW_001, .Repair, "basis_law001_repair"⟩,
    ⟨.LAW_002, .Boundary, "basis_law002_boundary"⟩,
    ⟨.LAW_002, .Branch, "basis_law002_branch"⟩,
    ⟨.LAW_002, .Repair, "basis_law002_repair"⟩,
    ⟨.LAW_003, .Branch, "basis_law003_branch"⟩,
    ⟨.LAW_003, .Repair, "basis_law003_repair"⟩,
    ⟨.LAW_004, .Boundary, "basis_law004_boundary"⟩,
    ⟨.LAW_004, .Branch, "basis_law004_branch"⟩,
    ⟨.LAW_004, .Repair, "basis_law004_repair"⟩,
    ⟨.LAW_005, .Boundary, "basis_law005_boundary"⟩,
    ⟨.LAW_005, .Branch, "basis_law005_branch"⟩,
    ⟨.LAW_005, .Repair, "basis_law005_repair"⟩,
    ⟨.LAW_006, .Branch, "basis_law006_branch"⟩,
    ⟨.LAW_006, .Repair, "basis_law006_repair"⟩,
    ⟨.LAW_007, .Branch, "basis_law007_branch"⟩,
    ⟨.LAW_008, .Repair, "basis_law008_repair"⟩,
    ⟨.LAW_009, .Branch, "basis_law009_branch"⟩,
    ⟨.LAW_009, .Repair, "basis_law009_repair"⟩,
    ⟨.LAW_010, .Boundary, "basis_law010_boundary"⟩,
    ⟨.LAW_010, .Branch, "basis_law010_branch"⟩,
    ⟨.LAW_010, .Repair, "basis_law010_repair"⟩,
    ⟨.LAW_011, .Branch, "basis_law011_branch"⟩,
    ⟨.LAW_012, .Branch, "basis_law012_branch"⟩,
    ⟨.LAW_013, .Negative, "basis_law013_negative"⟩,
    ⟨.LAW_013, .Boundary, "basis_law013_boundary"⟩,
    ⟨.LAW_013, .Repair, "basis_law013_repair"⟩,
    ⟨.LAW_014, .Positive, "basis_law014_positive"⟩,
    ⟨.LAW_014, .Repair, "basis_law014_repair"⟩,
    ⟨.LAW_015, .Negative, "basis_law015_negative"⟩,
    ⟨.LAW_015, .Boundary, "basis_law015_boundary"⟩,
    ⟨.LAW_015, .Repair, "basis_law015_repair"⟩,
    ⟨.LAW_016, .Branch, "basis_law016_branch"⟩,
    ⟨.LAW_016, .Repair, "basis_law016_repair"⟩,
    ⟨.LAW_017, .Boundary, "basis_law017_boundary"⟩,
    ⟨.LAW_017, .Branch, "basis_law017_branch"⟩,
    ⟨.LAW_017, .Repair, "basis_law017_repair"⟩,
    ⟨.LAW_018, .Branch, "basis_law018_branch"⟩ ]

/-- Полное число проверочных позиций, которых требует §13: 18 законов × 5
видов проверки. -/
def requiredPositions : ℕ := Fintype.card LawId * Fintype.card BasisKind

theorem requiredPositions_eq : requiredPositions = 90 := by decide

/-- Закрыты все 90 позиций. -/
theorem coverage_card : coverage.length = 90 := by decide

/-- Записи покрытия не дублируются. -/
theorem coverage_nodup : coverage.Nodup := by decide

/-- Позиция закрыта. -/
def covered (l : LawId) (k : BasisKind) : Bool :=
  coverage.any (fun c => c.law == l && c.kind == k)

/-- Все законы списком. -/
def allLaws : List LawId :=
  [.LAW_001, .LAW_002, .LAW_003, .LAW_004, .LAW_005, .LAW_006, .LAW_007,
   .LAW_008, .LAW_009, .LAW_010, .LAW_011, .LAW_012, .LAW_013, .LAW_014,
   .LAW_015, .LAW_016, .LAW_017, .LAW_018]

/-- Законы, у которых есть и положительный, и отрицательный свидетель. -/
def fullyProbed : List LawId :=
  allLaws.filter (fun l => covered l .Positive && covered l .Negative)

/-- Теперь и положительный, и отрицательный свидетель есть у всех
восемнадцати законов. -/
theorem fullyProbed_eq : fullyProbed = allLaws := by decide

/-- Каждый из восемнадцати законов имеет хотя бы одного свидетеля. -/
theorem every_law_probed :
    ∀ l ∈ allLaws, coverage.any (fun c => c.law == l) = true := by decide

/-- **Базисный набор §13 полон.**  Для каждого закона закрыты все пять видов
проверки: positive, negative, boundary, branch, repair. -/
theorem coverage_complete : ∀ (l : LawId) (k : BasisKind), covered l k = true := by
  decide

/-- Число закрытых позиций равно требуемому: 90 из 90. -/
theorem coverage_card_eq_required : coverage.length = requiredPositions := by decide

/-- Незакрытых позиций не осталось. -/
theorem coverage_remaining : requiredPositions - coverage.length = 0 := by decide

/-- Таблица покрытия непуста. -/
theorem coverage_nonempty : coverage ≠ [] := by decide

end Polymath.OSA4
