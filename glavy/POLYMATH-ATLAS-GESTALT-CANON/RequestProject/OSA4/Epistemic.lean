/-
# OSA-4.0 — эпистемическая алгебра слияния ветвей

Формализация §6 «EPISTEMIC JOIN-SEMILATTICE» кодекса OSA-4.0 (и §9/§11
полного кодекса): пятизначная таблица слияния ветвей
`TRUE_KNOWN / FALSE_KNOWN / UNKNOWN / ABSENT / CONFLICT`, законы
LAW-013 (коммутативность), LAW-014 (ассоциативность), LAW-015
(идемпотентность), а также разделение `Presence ≠ Truth`.

**Результат аудита.**  Кодекс утверждает, что для напечатанной таблицы
«доказаны идемпотентность, коммутативность и ассоциативность».  Первые два
свойства действительно выполняются (`joinSpec_comm`, `joinSpec_idem`), а
**ассоциативность — нет**: `joinSpec_not_assoc` даёт явный контрпример

    (TRUE ⊔ FALSE) ⊔ UNKNOWN = CONFLICT,   TRUE ⊔ (FALSE ⊔ UNKNOWN) = UNKNOWN,

и всего таких троек ровно 8 (`joinSpec_assoc_failures_card`).  Причина
структурная: строка `UNKNOWN` делает `UNKNOWN` поглощающим (значит,
`TRUE ≤ UNKNOWN`), но одновременно `TRUE ⊔ FALSE = CONFLICT` требует, чтобы
наименьшей верхней гранью `TRUE` и `FALSE` был `CONFLICT`, а не `UNKNOWN`.
Одно значение не может быть одновременно «нет информации» и «верхняя
грань».

**Исправление** (оно же — то, что кодекс сам постулирует лозунгом
«Presence ≠ Truth»): свидетельства о присутствии ресурса и свидетельства об
истинности предиката разводятся в два независимых пространства, а слияние
ветвей — покомпонентное объединение свидетельств (`Belief`).  Получается
настоящая полурешётка (`Belief.join_assoc` и др.), в которой сохраняются
ключевые вердикты Semantic Torture Set: T09 (`TRUE ⊔ FALSE = CONFLICT`),
T08 (`TRUE ⊔ ABSENT = UNKNOWN`), T05 (`UNKNOWN ≠ FALSE_KNOWN`).  Исправленная
таблица совпадает с напечатанной ровно вне строки/столбца `UNKNOWN`
(`collapse_join_eq_spec_of_ne_unknown`, `spec_disagreement_eq`).
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace Polymath.OSA4

/-! ## Пятизначная эпистемическая шкала кодекса -/

/-- Эпистемическое значение предиката в ветви графа (§6 кодекса OSA-4.0). -/
inductive EV
  /-- Доказано, что предикат истинен. -/
  | TRUE_KNOWN
  /-- Доказано, что предикат ложен. -/
  | FALSE_KNOWN
  /-- Информации недостаточно. -/
  | UNKNOWN
  /-- Объекта нет в ветви (это *не* «предикат ложен»). -/
  | ABSENT
  /-- Ветви противоречат друг другу. -/
  | CONFLICT
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace EV

/-- Печатное имя значения. -/
def name : EV → String
  | .TRUE_KNOWN => "TRUE_KNOWN"
  | .FALSE_KNOWN => "FALSE_KNOWN"
  | .UNKNOWN => "UNKNOWN"
  | .ABSENT => "ABSENT"
  | .CONFLICT => "CONFLICT"

end EV

/-- Таблица слияния ветвей **в точности как она напечатана** в кодексе
OSA-4.0 (§6 Unified Codex, §11 Full Unified Codex). -/
def joinSpec : EV → EV → EV
  | .CONFLICT, _ => .CONFLICT
  | _, .CONFLICT => .CONFLICT
  | .TRUE_KNOWN, .TRUE_KNOWN => .TRUE_KNOWN
  | .TRUE_KNOWN, .FALSE_KNOWN => .CONFLICT
  | .TRUE_KNOWN, .UNKNOWN => .UNKNOWN
  | .TRUE_KNOWN, .ABSENT => .UNKNOWN
  | .FALSE_KNOWN, .TRUE_KNOWN => .CONFLICT
  | .FALSE_KNOWN, .FALSE_KNOWN => .FALSE_KNOWN
  | .FALSE_KNOWN, .UNKNOWN => .UNKNOWN
  | .FALSE_KNOWN, .ABSENT => .UNKNOWN
  | .UNKNOWN, _ => .UNKNOWN
  | .ABSENT, .TRUE_KNOWN => .UNKNOWN
  | .ABSENT, .FALSE_KNOWN => .UNKNOWN
  | .ABSENT, .UNKNOWN => .UNKNOWN
  | .ABSENT, .ABSENT => .ABSENT

/-- LAW-015 (Join Idempotence) для напечатанной таблицы: выполняется. -/
theorem joinSpec_idem (x : EV) : joinSpec x x = x := by
  cases x <;> rfl

/-- LAW-013 (Join Commutativity) для напечатанной таблицы: выполняется. -/
theorem joinSpec_comm (x y : EV) : joinSpec x y = joinSpec y x := by
  revert x y; decide

/-- `CONFLICT` — верхний элемент напечатанной таблицы. -/
theorem joinSpec_conflict_top (x : EV) : joinSpec x .CONFLICT = .CONFLICT := by
  cases x <;> rfl

/-- `ABSENT` ≠ `FALSE_KNOWN` как эпистемические значения: слияние с `TRUE_KNOWN`
различает их (`UNKNOWN` против `CONFLICT`).  Это ремарка кодекса
«ABSENT (объекта нет в ветви) ≠ FALSE (доказано, что предикат ложен)». -/
theorem absent_ne_false_semantically :
    joinSpec .TRUE_KNOWN .ABSENT ≠ joinSpec .TRUE_KNOWN .FALSE_KNOWN := by
  decide

/-- **Дефект спецификации.**  LAW-014 (Join Associativity) для напечатанной
таблицы **не выполняется**. -/
theorem joinSpec_not_assoc :
    ¬ ∀ x y z : EV, joinSpec (joinSpec x y) z = joinSpec x (joinSpec y z) := by
  decide

/-- Минимальный контрпример к ассоциативности напечатанной таблицы. -/
theorem joinSpec_assoc_counterexample :
    joinSpec (joinSpec .TRUE_KNOWN .FALSE_KNOWN) .UNKNOWN = .CONFLICT ∧
    joinSpec .TRUE_KNOWN (joinSpec .FALSE_KNOWN .UNKNOWN) = .UNKNOWN :=
  ⟨rfl, rfl⟩

/-- Тройки значений, на которых напечатанная таблица неассоциативна. -/
def specAssocFailures : Finset (EV × EV × EV) :=
  Finset.univ.filter fun p =>
    joinSpec (joinSpec p.1 p.2.1) p.2.2 ≠ joinSpec p.1 (joinSpec p.2.1 p.2.2)

/-- Неассоциативных троек ровно восемь: дефект локален, но реален. -/
theorem joinSpec_assoc_failures_card : specAssocFailures.card = 8 := by
  decide

/-- Каждая из восьми неассоциативных троек содержит и `TRUE_KNOWN`, и
`FALSE_KNOWN` (клетка, дающая `CONFLICT`), и ещё одно значение без
свидетельств об истинности — `UNKNOWN` или `ABSENT`.  Источник дефекта
именно в том, что «нет информации» сделано поглощающим элементом, тогда как
`TRUE ⊔ FALSE` поднимается до верхнего элемента. -/
theorem specAssocFailures_shape :
    ∀ p ∈ specAssocFailures,
      (p.1 = EV.UNKNOWN ∨ p.1 = EV.ABSENT ∨ p.2.1 = EV.UNKNOWN ∨
        p.2.1 = EV.ABSENT ∨ p.2.2 = EV.UNKNOWN ∨ p.2.2 = EV.ABSENT) ∧
      (p.1 = EV.TRUE_KNOWN ∨ p.2.1 = EV.TRUE_KNOWN ∨ p.2.2 = EV.TRUE_KNOWN) ∧
      (p.1 = EV.FALSE_KNOWN ∨ p.2.1 = EV.FALSE_KNOWN ∨ p.2.2 = EV.FALSE_KNOWN) := by
  decide

/-! ## Исправленное ядро: свидетельства вместо одного значения

`Belief` — четыре независимых флага свидетельств, собранных ветвями:
присутствует ли ресурс, отсутствует ли ресурс, доказана ли истинность
предиката, доказана ли ложность.  Слияние ветвей — объединение
свидетельств; это делает полурешёточные законы теоремами по построению. -/

/-- Свидетельства одной ветви: presence-пространство (`present`, `absent`)
и truth-пространство (`isTrue`, `isFalse`), разведённые в соответствии с
принципом кодекса «Presence ≠ Truth». -/
structure Belief where
  /-- Есть свидетельство, что ресурс присутствует. -/
  present : Bool
  /-- Есть свидетельство, что ресурс отсутствует. -/
  absent : Bool
  /-- Есть доказательство истинности предиката. -/
  isTrue : Bool
  /-- Есть доказательство ложности предиката. -/
  isFalse : Bool
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace Belief

/-- Слияние ветвей: объединение свидетельств. -/
def join (a b : Belief) : Belief :=
  ⟨a.present || b.present, a.absent || b.absent,
   a.isTrue || b.isTrue, a.isFalse || b.isFalse⟩

/-- «Нет информации» — нейтральный элемент слияния. -/
def bot : Belief := ⟨false, false, false, false⟩

/-- Полное противоречие — верхний элемент. -/
def top : Belief := ⟨true, true, true, true⟩

/-- LAW-015 (Join Idempotence). -/
theorem join_idem (a : Belief) : join a a = a := by
  cases a; simp [join]

/-- LAW-013 (Join Commutativity). -/
theorem join_comm (a b : Belief) : join a b = join b a := by
  cases a; cases b; simp [join, Bool.or_comm]

/-- LAW-014 (Join Associativity) — теперь действительно выполняется. -/
theorem join_assoc (a b c : Belief) :
    join (join a b) c = join a (join b c) := by
  cases a; cases b; cases c; simp [join, Bool.or_assoc]

/-- `bot` нейтрален: «нет информации» ничего не портит. -/
theorem join_bot (a : Belief) : join a bot = a := by
  cases a; simp [join, bot]

/-- `top` поглощает. -/
theorem join_top (a : Belief) : join a top = top := by
  cases a; simp [join, top]

/-- Порядок «знать не меньше». -/
def le (a b : Belief) : Prop := join a b = b

instance decidableLe (a b : Belief) : Decidable (le a b) := by
  unfold le; infer_instance

theorem le_refl' (a : Belief) : le a a := join_idem a

theorem le_trans' {a b c : Belief} (h₁ : le a b) (h₂ : le b c) : le a c := by
  unfold le at *
  rw [← h₂, ← join_assoc, h₁]

theorem le_antisymm' {a b : Belief} (h₁ : le a b) (h₂ : le b a) : a = b := by
  unfold le at *
  rw [← h₁, join_comm, h₂]

/-- `bot` — наименьший элемент. -/
theorem bot_le (a : Belief) : le bot a := by
  unfold le; rw [join_comm]; exact join_bot a

/-- `top` — наибольший элемент. -/
theorem le_top (a : Belief) : le a top := join_top a

/-- Слияние — верхняя грань слева. -/
theorem le_join_left (a b : Belief) : le a (join a b) := by
  unfold le; rw [← join_assoc, join_idem]

/-- Слияние — верхняя грань справа. -/
theorem le_join_right (a b : Belief) : le b (join a b) := by
  unfold le; rw [join_comm a b, ← join_assoc, join_idem]

/-- Слияние — *наименьшая* верхняя грань. -/
theorem join_le {a b c : Belief} (h₁ : le a c) (h₂ : le b c) : le (join a b) c := by
  unfold le at *
  rw [join_assoc, h₂, h₁]

/-- Слияние списка ветвей. -/
def joinList (l : List Belief) : Belief := l.foldl join bot

@[simp] theorem joinList_nil : joinList [] = bot := rfl

theorem joinList_cons (a : Belief) (l : List Belief) :
    joinList (a :: l) = join a (joinList l) := by
  have aux : ∀ (l : List Belief) (x : Belief),
      l.foldl join x = join x (l.foldl join bot) := by
    intro l
    induction l with
    | nil => intro x; simp [join_bot]
    | cons b t ih =>
        intro x
        simp only [List.foldl_cons]
        rw [ih (join x b), ih (join bot b), join_comm bot b, join_bot, join_assoc]
  simpa [joinList, List.foldl_cons, join_comm bot a, join_bot] using aux l (join bot a)

/-- Слияние не зависит от порядка ветвей (следствие LAW-013/LAW-014). -/
theorem joinList_perm {l₁ l₂ : List Belief} (h : l₁.Perm l₂) :
    joinList l₁ = joinList l₂ := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [joinList_cons, joinList_cons, ih]
  | swap a b l =>
      rw [joinList_cons, joinList_cons, joinList_cons, joinList_cons,
        ← join_assoc, ← join_assoc, join_comm a b]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- Повтор одной и той же ветви ничего не меняет (следствие LAW-015). -/
theorem joinList_duplicate (a : Belief) (l : List Belief) :
    joinList (a :: a :: l) = joinList (a :: l) := by
  rw [joinList_cons, joinList_cons, ← join_assoc, join_idem]

end Belief

/-! ## Связь исправленного ядра с напечатанной таблицей -/

/-- Свидетельства, соответствующие эпистемическому значению кодекса. -/
def EV.toBelief : EV → Belief
  | .TRUE_KNOWN => ⟨true, false, true, false⟩
  | .FALSE_KNOWN => ⟨true, false, false, true⟩
  | .UNKNOWN => Belief.bot
  | .ABSENT => ⟨false, true, false, false⟩
  | .CONFLICT => ⟨true, false, true, true⟩

/-- Обратное отображение: какое из пяти значений кодекса описывает набор
свидетельств. -/
def Belief.collapse (b : Belief) : EV :=
  if b.isTrue && b.isFalse then .CONFLICT
  else if b.present && b.absent then .UNKNOWN
  else if b.isTrue then .TRUE_KNOWN
  else if b.isFalse then .FALSE_KNOWN
  else if b.absent then .ABSENT
  else .UNKNOWN

/-- Кодировка значений кодекса свидетельствами точна. -/
theorem collapse_toBelief (x : EV) : x.toBelief.collapse = x := by
  cases x <;> rfl

/-- Исправленное слияние воспроизводит напечатанную таблицу всюду, где
`UNKNOWN` не участвует, — в частности сохраняются вердикты Torture Set
T09 (`TRUE ⊔ FALSE = CONFLICT`) и T08 (`TRUE ⊔ ABSENT = UNKNOWN`). -/
theorem collapse_join_eq_spec_of_ne_unknown (x y : EV)
    (hx : x ≠ EV.UNKNOWN) (hy : y ≠ EV.UNKNOWN) :
    (Belief.join x.toBelief y.toBelief).collapse = joinSpec x y := by
  revert x y; decide

/-- Клетки, в которых исправленное ядро расходится с напечатанной таблицей. -/
def specDisagreement : Finset (EV × EV) :=
  Finset.univ.filter fun p =>
    (Belief.join p.1.toBelief p.2.toBelief).collapse ≠ joinSpec p.1 p.2

/-- Расхождение — ровно шесть клеток, и все они лежат в строке/столбце
`UNKNOWN`: именно там напечатанная таблица и теряет ассоциативность. -/
theorem spec_disagreement_eq :
    specDisagreement =
      {(EV.TRUE_KNOWN, EV.UNKNOWN), (EV.FALSE_KNOWN, EV.UNKNOWN),
       (EV.ABSENT, EV.UNKNOWN), (EV.UNKNOWN, EV.TRUE_KNOWN),
       (EV.UNKNOWN, EV.FALSE_KNOWN), (EV.UNKNOWN, EV.ABSENT)} := by
  decide

/-- T09: противоречие ветвей не понижается до `UNKNOWN`. -/
theorem torture_T09_conflict :
    (Belief.join (EV.TRUE_KNOWN).toBelief (EV.FALSE_KNOWN).toBelief).collapse
      = EV.CONFLICT := by
  decide

/-- T08: «в одной ветви объект есть, в другой отсутствует» даёт `UNKNOWN`,
а не `CONFLICT` — presence отделено от truth. -/
theorem torture_T08_presence_vs_truth :
    (Belief.join (EV.TRUE_KNOWN).toBelief (EV.ABSENT).toBelief).collapse
      = EV.UNKNOWN := by
  decide

/-- T05: `UNKNOWN` — не `FALSE_KNOWN`. -/
theorem torture_T05_unknown_ne_false : EV.UNKNOWN ≠ EV.FALSE_KNOWN := by
  decide

end Polymath.OSA4
