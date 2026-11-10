/-
# OSA-3.2 — версионирование композиций (§17)

`CompositionVersion = {version, timestamp, ops, report, notes}`; архив
поддерживает откат к предыдущей версии, сравнение версий (diff по вердиктам
и операторам) и полный журнал изменений.

Доказано: номера версий в архиве строго убывают от свежей к старой (то есть
журнал упорядочен и не теряет шагов), `commit` увеличивает номер ровно на
единицу, откат к существующей версии возвращает именно её, diff версии с
самой собой пуст, а непустой diff означает реальное различие в цепочке
операторов или в вердикте.
-/
import RequestProject.OSA.Interactive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

/-! ## Версия и архив -/

/-- Версия композиции (§17). -/
structure CompositionVersion where
  version : ℕ
  timestamp : ℕ
  ops : List Operator
  report : Report
  notes : String
  deriving Inhabited

/-- Архив версий: реестр, контекст композиции и журнал версий (свежие
впереди). -/
structure CompositionArchive where
  registry : List Operator
  base : Composition
  versions : List CompositionVersion
  deriving Inhabited

/-- Пустой архив. -/
def CompositionArchive.empty (reg : List Operator) (base : Composition) :
    CompositionArchive :=
  { registry := reg, base := base, versions := [] }

/-- Номер следующей версии. -/
def CompositionArchive.nextVersion (a : CompositionArchive) : ℕ :=
  match a.versions with
  | [] => 1
  | v :: _ => v.version + 1

/-- Фиксация новой версии: цепочка компилируется, отчёт сохраняется. -/
def CompositionArchive.commit (a : CompositionArchive) (ops : List Operator)
    (timestamp : ℕ) (notes : String) : CompositionArchive :=
  { a with
    versions :=
      { version := a.nextVersion
      , timestamp := timestamp
      , ops := ops
      , report := compile a.registry { a.base with ops := ops }
      , notes := notes } :: a.versions }

/-- Версия с данным номером. -/
def CompositionArchive.find (a : CompositionArchive) (n : ℕ) :
    Option CompositionVersion :=
  a.versions.find? (fun v => v.version == n)

/-- Текущая (последняя зафиксированная) версия. -/
def CompositionArchive.current (a : CompositionArchive) : Option CompositionVersion :=
  a.versions.head?

/-- Откат: журнал усекается до версии `n` включительно. -/
def CompositionArchive.rollbackTo (a : CompositionArchive) (n : ℕ) :
    CompositionArchive :=
  { a with versions := a.versions.dropWhile (fun v => !(v.version == n)) }

/-! ## Сравнение версий -/

/-- Различие между двумя версиями: операторы и вердикт. -/
structure VersionDiff where
  fromVersion : ℕ
  toVersion : ℕ
  removedOps : List String
  addedOps : List String
  statusChanged : Option (Status × Status)
  codeChanged : Option (ErrCode × ErrCode)
  deriving Repr, Inhabited

/-- Diff двух версий (§17). -/
def diffVersions (v w : CompositionVersion) : VersionDiff where
  fromVersion := v.version
  toVersion := w.version
  removedOps :=
    (v.ops.map (·.id)).filter (fun x => !(w.ops.map (·.id)).contains x)
  addedOps :=
    (w.ops.map (·.id)).filter (fun x => !(v.ops.map (·.id)).contains x)
  statusChanged :=
    if v.report.status == w.report.status then none
    else some (v.report.status, w.report.status)
  codeChanged :=
    if v.report.code == w.report.code then none else some (v.report.code, w.report.code)

/-- Diff пуст: ни операторы, ни вердикт не изменились. -/
def VersionDiff.isEmpty (d : VersionDiff) : Bool :=
  d.removedOps.isEmpty && d.addedOps.isEmpty &&
  d.statusChanged.isNone && d.codeChanged.isNone

/-! ## Свойства архива -/

/-- `commit` увеличивает номер версии ровно на единицу относительно
предыдущей вершины журнала. -/
theorem commit_version (a : CompositionArchive) (ops : List Operator)
    (t : ℕ) (notes : String) :
    ((a.commit ops t notes).versions.head?.map (·.version)) = some a.nextVersion := rfl

/-- `commit` удлиняет журнал ровно на одну запись. -/
theorem commit_length (a : CompositionArchive) (ops : List Operator)
    (t : ℕ) (notes : String) :
    (a.commit ops t notes).versions.length = a.versions.length + 1 := rfl

/-- Сохранённый в версии отчёт — это в точности вердикт компилятора для
зафиксированной цепочки: журнал не может «разойтись» с компилятором. -/
theorem commit_report (a : CompositionArchive) (ops : List Operator)
    (t : ℕ) (notes : String) (v : CompositionVersion)
    (h : (a.commit ops t notes).current = some v) :
    v.report = compile a.registry { a.base with ops := v.ops } := by
  simp only [CompositionArchive.current, CompositionArchive.commit,
    List.head?_cons, Option.some.injEq] at h
  subst h
  rfl

/-- Журнал упорядочен: номера версий строго убывают от свежих к старым. -/
def CompositionArchive.ordered (a : CompositionArchive) : Prop :=
  a.versions.IsChain (fun v w => w.version < v.version)

/-- Пустой архив упорядочен. -/
theorem empty_ordered (reg : List Operator) (base : Composition) :
    (CompositionArchive.empty reg base).ordered := List.isChain_nil

/-- `commit` сохраняет упорядоченность журнала. -/
theorem commit_ordered (a : CompositionArchive) (ops : List Operator)
    (t : ℕ) (notes : String) (h : a.ordered) : (a.commit ops t notes).ordered := by
  unfold CompositionArchive.ordered CompositionArchive.commit at *
  refine List.isChain_cons.mpr ⟨?_, h⟩
  intro y hy
  cases hv : a.versions with
  | nil => rw [hv] at hy; simp at hy
  | cons w rest =>
      rw [hv] at hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      simp [CompositionArchive.nextVersion, hv]

/-- Откат возвращает именно запрошенную версию, если она есть в журнале. -/
theorem rollbackTo_current (a : CompositionArchive) (n : ℕ)
    (v : CompositionVersion) (hv : (a.rollbackTo n).current = some v) :
    v.version = n := by
  unfold CompositionArchive.rollbackTo CompositionArchive.current at hv
  have hmem : v ∈ a.versions.dropWhile (fun x => !(x.version == n)) :=
    List.mem_of_mem_head? hv
  have hhead : (a.versions.dropWhile (fun x => !(x.version == n))).head? = some v := hv
  have := List.head?_dropWhile_not (p := fun x => !(x.version == n)) (l := a.versions)
  rw [hhead] at this
  simpa using this

/-- Откат не изобретает версий: журнал после отката — суффикс исходного. -/
theorem rollbackTo_suffix (a : CompositionArchive) (n : ℕ) :
    (a.rollbackTo n).versions.IsSuffix a.versions :=
  List.dropWhile_suffix _

/-! ## Свойства сравнения -/

/-- Diff версии с самой собой пуст. -/
theorem diff_self (v : CompositionVersion) : (diffVersions v v).isEmpty = true := by
  simp [diffVersions, VersionDiff.isEmpty, List.filter_eq_nil_iff]

/-- Непустой diff означает содержательное изменение: набор операторов или
вердикт действительно отличаются. -/
theorem diff_nonempty_means_change (v w : CompositionVersion)
    (h : (diffVersions v w).isEmpty = false) :
    (v.ops.map (·.id)) ≠ (w.ops.map (·.id)) ∨
    v.report.status ≠ w.report.status ∨ v.report.code ≠ w.report.code := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hops, hst, hcode⟩ := hcon
  have : (diffVersions v w).isEmpty = true := by
    simp [diffVersions, VersionDiff.isEmpty, hops, hst, hcode, List.filter_eq_nil_iff]
  rw [this] at h
  exact absurd h (by simp)

/-! ## Журнал изменений в текстовом виде -/

/-- Строка журнала. -/
def CompositionVersion.render (v : CompositionVersion) : String :=
  "v" ++ toString v.version ++ " @" ++ toString v.timestamp ++ "  " ++
  String.intercalate " → " (v.ops.map (·.id)) ++ "  [" ++
  v.report.status.toStatusString ++ " / " ++ v.report.code.toCodeString ++ "]" ++
  (if v.notes == "" then "" else "  — " ++ v.notes)

/-- Полный журнал изменений. -/
def CompositionArchive.log (a : CompositionArchive) : String :=
  String.intercalate "\n" (a.versions.map CompositionVersion.render)

/-- Diff в текстовом виде. -/
def VersionDiff.render (d : VersionDiff) : String :=
  "v" ++ toString d.fromVersion ++ " → v" ++ toString d.toVersion ++ ": " ++
  "-[" ++ String.intercalate ", " d.removedOps ++ "] " ++
  "+[" ++ String.intercalate ", " d.addedOps ++ "]" ++
  (match d.statusChanged with
   | none => ""
   | some (s1, s2) => "  verdict " ++ s1.toStatusString ++ " → " ++ s2.toStatusString)

/-! ## Демонстрация: три версии одной композиции -/

/-- Архив с историей починки: сначала цепочка без AUTHORIZE, затем с ним. -/
def demoArchive : CompositionArchive :=
  (((CompositionArchive.empty goldRegistry { goldBase with caseId := "versioning demo" }).commit
      [MEASURE, CALIBRATE, MODEL, VALIDATE, DECIDE] 1 "первая композиция").commit
      [MEASURE, CALIBRATE, MODEL, VALIDATE, DECIDE, EXECUTE_PLAN] 2
        "добавлено исполнение").commit
      [MEASURE, CALIBRATE, MODEL, VALIDATE, DECIDE, AUTHORIZE, EXECUTE] 3
        "починка: вставлен AUTHORIZE"

/-- Версия 2 не проходит политику эффектов, версия 3 — проходит полностью. -/
theorem demoArchive_verdicts :
    ((demoArchive.find 2).map (·.report.status)) = some Status.REPAIR ∧
    ((demoArchive.find 3).map (·.report.status)) = some Status.PASS := by decide

/-- Diff между версиями 2 и 3 непуст и фиксирует и вставку операторов, и
смену вердикта. -/
theorem demoArchive_diff :
    (match demoArchive.find 2, demoArchive.find 3 with
     | some v, some w => (diffVersions v w).addedOps
     | _, _ => []) = ["AUTHORIZE", "EXECUTE"] := by decide

/-- Откат к версии 1 оставляет в журнале ровно одну запись. -/
theorem demoArchive_rollback :
    (demoArchive.rollbackTo 1).versions.length = 1 ∧
    ((demoArchive.rollbackTo 1).current.map (·.version)) = some 1 := by decide

#eval IO.println demoArchive.log

#eval IO.println
  (match demoArchive.find 2, demoArchive.find 3 with
   | some v, some w => (diffVersions v w).render
   | _, _ => "")

end Polymath.OSA
