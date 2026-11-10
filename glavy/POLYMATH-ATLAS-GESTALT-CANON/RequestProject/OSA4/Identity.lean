/-
# OSA-4.0 — алгебра идентичности: Recreation ≠ Resurrection

Формализация §7 «АЛГЕБРА ИДЕНТИЧНОСТИ» кодекса OSA-4.0 и законов
LAW-004 (No Resurrection), LAW-005 (Consume Safety), LAW-016
(Recreation Identity).  Неоднозначный примитив `RESTORE(X)` запрещён и
разложен на два различных шага:

* **Resurrection** `Destroyed(X) → Available(X)` с тем же идентификатором —
  запрещён;
* **Reconstruction / Recreation** — порождает `X'` с новым идентификатором и
  провенансом, ссылающимся на `X`, — допустим.

Тесты Semantic Torture Set: T04a (resurrection ⇒ REJECT), T04b (recreation ⇒
допустимо), T12 (повторное `CONSUME` ⇒ REJECT).
-/
import RequestProject.OSA4.Axes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-- Идентификатор объекта. -/
abbrev ObjId := ℕ

/-- Объект с фазой жизненного цикла (ось E) и провенансом. -/
structure Obj where
  /-- Идентификатор. -/
  id : ObjId
  /-- Текущая фаза. -/
  phase : Phase
  /-- Провенанс: идентификаторы предшественников. -/
  lineage : List ObjId
  deriving DecidableEq, Repr, Inhabited

/-- Мир объектов. -/
structure World where
  /-- Объекты мира. -/
  objs : List Obj
  deriving Repr, Inhabited

namespace World

/-- Объект с данным идентификатором. -/
def find (w : World) (i : ObjId) : Option Obj := w.objs.find? (fun o => o.id == i)

/-- Фаза объекта, если он существует. -/
def phaseOf (w : World) (i : ObjId) : Option Phase := (w.find i).map Obj.phase

/-- Идентификатор занят. -/
def has (w : World) (i : ObjId) : Bool := (w.find i).isSome

/-- Заменить фазу объекта. -/
def setPhase (w : World) (i : ObjId) (p : Phase) : World :=
  ⟨w.objs.map (fun o => if o.id = i then { o with phase := p } else o)⟩

/-- Добавить новый объект. -/
def add (w : World) (o : Obj) : World := ⟨o :: w.objs⟩

/-- Найденный объект действительно имеет запрошенный идентификатор. -/
theorem find_id {w : World} {i : ObjId} {o : Obj} (h : w.find i = some o) :
    o.id = i := by
  have := List.find?_some h
  simpa using this

theorem find_setPhase (w : World) (i : ObjId) (p : Phase) (j : ObjId) :
    (w.setPhase i p).find j =
      (w.find j).map (fun o => if o.id = i then { o with phase := p } else o) := by
  have hpred :
      (fun o : Obj => (if o.id = i then { o with phase := p } else o).id == j)
        = (fun o : Obj => o.id == j) := by
    funext o; by_cases h : o.id = i <;> simp [h]
  simp only [setPhase, find, List.find?_map, Function.comp_def, hpred]

theorem phaseOf_setPhase_of_ne (w : World) {i j : ObjId} (h : j ≠ i) (p : Phase) :
    (w.setPhase i p).phaseOf j = w.phaseOf j := by
  rw [phaseOf, find_setPhase, phaseOf]
  cases hf : w.find j with
  | none => simp
  | some o => simp [find_id hf, h]

theorem phaseOf_setPhase_self (w : World) {i : ObjId} {o : Obj}
    (hf : w.find i = some o) (p : Phase) :
    (w.setPhase i p).phaseOf i = some p := by
  rw [phaseOf, find_setPhase, hf]
  simp [find_id hf]

theorem phaseOf_add_of_ne (w : World) (o : Obj) {j : ObjId} (h : o.id ≠ j) :
    (w.add o).phaseOf j = w.phaseOf j := by
  simp [add, phaseOf, find, List.find?_cons_of_neg, h]

theorem phaseOf_add_self (w : World) (o : Obj) : (w.add o).phaseOf o.id = some o.phase := by
  simp [add, phaseOf, find]

theorem has_of_phaseOf {w : World} {i : ObjId} {p : Phase} (h : w.phaseOf i = some p) :
    w.has i = true := by
  rw [phaseOf] at h
  cases hf : w.find i with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some o => simp [has, hf]

end World

/-- Шаги, меняющие фазы и идентичности. -/
inductive Step
  /-- Создать новый объект. -/
  | create (i : ObjId)
  /-- Потребить доступный объект. -/
  | consume (i : ObjId)
  /-- Уничтожить объект. -/
  | destroy (i : ObjId)
  /-- **Запрещённый** шаг: вернуть уничтоженный объект к жизни под тем же ID. -/
  | resurrect (i : ObjId)
  /-- Воссоздать объект под новым ID с провенансом. -/
  | recreate (old new : ObjId)
  deriving DecidableEq, Repr, Inhabited

namespace Step

/-- Допустимость шага (контракт ядра v0.4). -/
def legal (w : World) : Step → Bool
  | .create i => !w.has i
  | .consume i => w.phaseOf i == some .Available
  | .destroy i => (w.phaseOf i == some .Available) || (w.phaseOf i == some .Created)
  | .resurrect _ => false
  | .recreate old new =>
      (w.phaseOf old == some .Destroyed) && !w.has new && (old != new)

/-- Результат шага. -/
def apply (w : World) : Step → World
  | .create i => w.add ⟨i, .Created, []⟩
  | .consume i => w.setPhase i .Consumed
  | .destroy i => w.setPhase i .Destroyed
  | .resurrect i => w.setPhase i .Available
  | .recreate old new => w.add ⟨new, .Available, [old]⟩

end Step

/-! ## LAW-004 — No Resurrection -/

/-- Шаг «воскрешения» недопустим по контракту ядра: `legal` для него ложна
всегда. -/
theorem law004_resurrect_illegal (w : World) (i : ObjId) :
    Step.legal w (.resurrect i) = false := rfl

/-- **LAW-004 (No Resurrection).**  Ни один допустимый шаг не переводит объект
из фазы `Destroyed` в фазу `Available` под тем же идентификатором. -/
theorem law004_no_resurrection (w : World) (st : Step) (i : ObjId)
    (hleg : Step.legal w st = true) (hd : w.phaseOf i = some .Destroyed) :
    (Step.apply w st).phaseOf i ≠ some .Available := by
  have hhas : w.has i = true := World.has_of_phaseOf hd
  cases st with
  | create j =>
      have hji : j ≠ i := by
        rintro rfl
        rw [Step.legal, hhas] at hleg; exact Bool.noConfusion hleg
      rw [Step.apply, World.phaseOf_add_of_ne _ _ hji, hd]
      simp
  | consume j =>
      rcases eq_or_ne j i with rfl | hji
      · obtain ⟨o, ho⟩ : ∃ o, w.find j = some o := by
          rw [World.phaseOf] at hd
          cases hf : w.find j with
          | none => rw [hf] at hd; exact absurd hd (by simp)
          | some o => exact ⟨o, rfl⟩
        rw [Step.apply, World.phaseOf_setPhase_self w ho]
        simp
      · rw [Step.apply, World.phaseOf_setPhase_of_ne w (Ne.symm hji), hd]
        simp
  | destroy j =>
      rcases eq_or_ne j i with rfl | hji
      · obtain ⟨o, ho⟩ : ∃ o, w.find j = some o := by
          rw [World.phaseOf] at hd
          cases hf : w.find j with
          | none => rw [hf] at hd; exact absurd hd (by simp)
          | some o => exact ⟨o, rfl⟩
        rw [Step.apply, World.phaseOf_setPhase_self w ho]
        simp
      · rw [Step.apply, World.phaseOf_setPhase_of_ne w (Ne.symm hji), hd]
        simp
  | resurrect j => rw [Step.legal] at hleg; exact Bool.noConfusion hleg
  | recreate old new =>
      have hni : new ≠ i := by
        rintro rfl
        rw [Step.legal, hhas] at hleg
        simp at hleg
      rw [Step.apply, World.phaseOf_add_of_ne _ _ hni, hd]
      simp

/-! ## LAW-005 — Consume Safety -/

/-- **LAW-005 (Consume Safety).**  Потребление допустимо ровно тогда, когда
ресурс доступен. -/
theorem law005_consume_iff_available (w : World) (i : ObjId) :
    Step.legal w (.consume i) = true ↔ w.phaseOf i = some .Available := by
  simp [Step.legal]

/-- После потребления ресурс переходит в фазу `Consumed`. -/
theorem consume_phase (w : World) {i : ObjId} {o : Obj} (hf : w.find i = some o) :
    (Step.apply w (.consume i)).phaseOf i = some .Consumed :=
  World.phaseOf_setPhase_self w hf .Consumed

/-- **T12.**  Повторное потребление того же ресурса недопустимо. -/
theorem torture_T12_double_consume (w : World) (i : ObjId)
    (h : Step.legal w (.consume i) = true) :
    Step.legal (Step.apply w (.consume i)) (.consume i) = false := by
  rw [law005_consume_iff_available] at h
  obtain ⟨o, ho⟩ : ∃ o, w.find i = some o := by
    rw [World.phaseOf] at h
    cases hf : w.find i with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some o => exact ⟨o, rfl⟩
  simp [Step.legal, consume_phase w ho]

/-! ## LAW-016 — Recreation Identity -/

/-- **LAW-016 (Recreation Identity).**  Воссоздание допустимо только под
*новым* идентификатором. -/
theorem law016_recreate_new_id (w : World) (old new : ObjId)
    (h : Step.legal w (.recreate old new) = true) : new ≠ old := by
  simp only [Step.legal, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact fun hEq => h.2 (hEq ▸ rfl)

/-- Воссозданный объект доступен и несёт провенанс на предшественника. -/
theorem recreate_provenance (w : World) (old new : ObjId) :
    (Step.apply w (.recreate old new)).find new = some ⟨new, .Available, [old]⟩ := by
  simp [Step.apply, World.add, World.find]

/-- Оригинал остаётся уничтоженным: воссоздание не «оживляет» старый объект. -/
theorem recreate_keeps_old_destroyed (w : World) (old new : ObjId)
    (h : Step.legal w (.recreate old new) = true) :
    (Step.apply w (.recreate old new)).phaseOf old = some .Destroyed := by
  have hne : new ≠ old := law016_recreate_new_id w old new h
  simp only [Step.legal, Bool.and_eq_true, beq_iff_eq] at h
  rw [Step.apply, World.phaseOf_add_of_ne _ _ hne]
  exact h.1.1

/-- **T04a.**  Resurrection (тот же ID) отвергается. -/
theorem torture_T04a_resurrection_rejected (w : World) (i : ObjId) :
    Step.legal w (.resurrect i) = false := rfl

/-- **T04b.**  Recreation (новый ID + провенанс) допустима: конкретный
свидетель — мир с одним уничтоженным объектом. -/
theorem torture_T04b_recreation_legal :
    Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2) = true := by
  decide

/-- В том же мире воскрешение недопустимо — различие двух примитивов
проявляется на одном и том же состоянии. -/
theorem torture_T04_separation :
    Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2) = true ∧
    Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.resurrect 1) = false := by
  exact ⟨by decide, rfl⟩

end Polymath.OSA4
