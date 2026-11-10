/-
# OSA-4.0 — аудит операторов `.consume` и `.recreate`

Запрос аудита:

* «верифицируй `.consume`: уничтожает факт, требует `Available`»;
* «верифицируй `.recreate`: создаёт новый объект, требует `Destroyed`».

Обе спецификации доказаны — и в пространстве идентичностей (`World`/`Step`,
ось E), и в семантическом ядре (`KState`/`Op`), включая точную форму
«уничтожения факта»: знание становится `UNKNOWN`, а не `FALSE_KNOWN`
(LAW-017: потребление обесценивает доказательство, но не доказывает
отрицания).
-/
import RequestProject.OSA4.TortureSet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-! ## `.consume` -/

/-- **`.consume` требует `Available`** (необходимость).  Шаг потребления
допустим только для доступного ресурса. -/
theorem consume_requires_available {w : World} {i : ObjId}
    (h : Step.legal w (.consume i) = true) : w.phaseOf i = some .Available :=
  (law005_consume_iff_available w i).mp h

/-- **`.consume` требует `Available`** (достаточность): для доступного ресурса
шаг потребления допустим. -/
theorem consume_legal_of_available {w : World} {i : ObjId}
    (h : w.phaseOf i = some .Available) : Step.legal w (.consume i) = true :=
  (law005_consume_iff_available w i).mpr h

/-- Ресурс в любой другой фазе потребить нельзя. -/
theorem consume_illegal_of_not_available {w : World} {i : ObjId} {p : Phase}
    (hp : w.phaseOf i = some p) (hne : p ≠ .Available) :
    Step.legal w (.consume i) = false := by
  cases hl : Step.legal w (.consume i) with
  | false => rfl
  | true =>
      have := consume_requires_available hl
      rw [hp] at this
      exact absurd (Option.some.inj this) hne

/-- **`.consume` уничтожает ресурс**: после потребления фаза — `Consumed`,
и ресурс больше не доступен. -/
theorem consume_destroys {w : World} {i : ObjId} (h : Step.legal w (.consume i) = true) :
    (Step.apply w (.consume i)).phaseOf i = some .Consumed ∧
    (Step.apply w (.consume i)).phaseOf i ≠ some .Available := by
  have hav : w.phaseOf i = some .Available := consume_requires_available h
  obtain ⟨o, ho⟩ : ∃ o, w.find i = some o := by
    rw [World.phaseOf] at hav
    cases hf : w.find i with
    | none => rw [hf] at hav; exact absurd hav (by simp)
    | some o => exact ⟨o, rfl⟩
  refine ⟨consume_phase w ho, ?_⟩
  rw [consume_phase w ho]
  simp

/-- Потребление не затрагивает другие объекты (LAW-003 в пространстве
идентичностей). -/
theorem consume_frame (w : World) {i j : ObjId} (h : j ≠ i) :
    (Step.apply w (.consume i)).phaseOf j = w.phaseOf j :=
  World.phaseOf_setPhase_of_ne w h .Consumed

/-- **Повторное потребление невозможно** (T12): потреблённый ресурс больше
не потребить. -/
theorem consume_not_repeatable {w : World} {i : ObjId} (h : Step.legal w (.consume i) = true) :
    Step.legal (Step.apply w (.consume i)) (.consume i) = false :=
  torture_T12_double_consume w i h

/-- **`.consume` в семантическом ядре уничтожает факт.**  Оператор,
потребляющий факт `f` и не производящий его заново, делает `f` неизвестным:
ни `f`, ни `¬f` после исполнения не доказаны. -/
theorem consume_kills_fact (o : Op) (s : KState) {f : FactId}
    (hc : f ∈ o.consumes) (hp : f ∉ o.produces) :
    (o.exec s).factStatus f = .UNKNOWN ∧
    eval (o.exec s) (.factExists f) ≠ .TRUE_KNOWN ∧
    eval (o.exec s) (.pnot (.factExists f)) ≠ .TRUE_KNOWN := by
  have hk : f ∈ o.kill := by simp [Op.kill, hc]
  exact ⟨factStatus_exec_kill o s hk hp, law006_kill_live_fact o s hk hp,
    law017_invalidate_not_refute o s hk hp⟩

/-- Конкретный свидетель для оператора `CONSUME_X` каталога: доказанный факт
`X` после потребления становится неизвестным. -/
theorem consume_X_kills : (CONSUME_X.exec ⟨[("X", .TRUE_KNOWN)], []⟩).factStatus "X" = .UNKNOWN := by
  decide

/-! ## `.recreate` -/

/-- **`.recreate` требует `Destroyed`**: воссоздать можно только уничтоженный
объект. -/
theorem recreate_requires_destroyed {w : World} {old new : ObjId}
    (h : Step.legal w (.recreate old new) = true) : w.phaseOf old = some .Destroyed := by
  simp only [Step.legal, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

/-- **`.recreate` требует свободного идентификатора**: новый объект не может
занять уже существующий ID. -/
theorem recreate_requires_fresh {w : World} {old new : ObjId}
    (h : Step.legal w (.recreate old new) = true) : w.has new = false := by
  simp only [Step.legal, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.2

/-- Объект в любой фазе, кроме `Destroyed`, воссоздать нельзя. -/
theorem recreate_illegal_of_not_destroyed {w : World} {old new : ObjId} {p : Phase}
    (hp : w.phaseOf old = some p) (hne : p ≠ .Destroyed) :
    Step.legal w (.recreate old new) = false := by
  cases hl : Step.legal w (.recreate old new) with
  | false => rfl
  | true =>
      have := recreate_requires_destroyed hl
      rw [hp] at this
      exact absurd (Option.some.inj this) hne

/-- **`.recreate` создаёт новый объект**: он доступен, имеет новый
идентификатор и провенанс, ссылающийся на предшественника. -/
theorem recreate_creates_new {w : World} {old new : ObjId}
    (h : Step.legal w (.recreate old new) = true) :
    (Step.apply w (.recreate old new)).find new = some ⟨new, .Available, [old]⟩ ∧
    (Step.apply w (.recreate old new)).phaseOf new = some .Available ∧
    new ≠ old ∧ w.has new = false :=
  ⟨recreate_provenance w old new, by
      rw [World.phaseOf, recreate_provenance w old new]; rfl,
    law016_recreate_new_id w old new h, recreate_requires_fresh h⟩

/-- **`.recreate` — не воскрешение**: предшественник остаётся уничтоженным. -/
theorem recreate_is_not_resurrection {w : World} {old new : ObjId}
    (h : Step.legal w (.recreate old new) = true) :
    (Step.apply w (.recreate old new)).phaseOf old = some .Destroyed ∧
    Step.legal w (.resurrect old) = false :=
  ⟨recreate_keeps_old_destroyed w old new h, rfl⟩

/-- Воссоздание не затрагивает остальные объекты. -/
theorem recreate_frame (w : World) {old new j : ObjId} (h : new ≠ j) :
    (Step.apply w (.recreate old new)).phaseOf j = w.phaseOf j :=
  World.phaseOf_add_of_ne w ⟨new, .Available, [old]⟩ h

/-- Свидетель полного цикла `create → destroy → recreate`: воссоздание
допустимо ровно после уничтожения и порождает новый доступный объект. -/
theorem recreate_lifecycle_witness :
    Step.legal ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2) = true ∧
    (Step.apply ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2)).phaseOf 2 = some .Available ∧
    (Step.apply ⟨[⟨1, .Destroyed, []⟩]⟩ (.recreate 1 2)).phaseOf 1 = some .Destroyed ∧
    Step.legal ⟨[⟨1, .Available, []⟩]⟩ (.recreate 1 2) = false := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Polymath.OSA4
