import RequestProject.Atlas.ApostlePipeline
import RequestProject.Atlas.UAM_RSIA_PhaseRing
import RequestProject.Atlas.Bridges.CanonApostle

/-!
# Шов: ApostlePipeline ↔ RSIA (кольцо фаз)

Конвейер апостолов линеен: тринадцать фаз, ни одна не повторяется. Кольцо фаз
RSIA циклично: четыре фазы, возврат за четыре шага. Проекция по номеру фазы
связывает их и показывает ровно тот же мотив, что и в Каноне Горизонтов:
`13 = 4 · 3 + 1`, поэтому Павел попадает в ту же фазу кольца, что и Пётр,
оставаясь при этом другой фазой конвейера. Возврат структурный, не буквальный.

Формально доказано:

* `toRSIA` — проекция фазы конвейера в кольцо фаз по её номеру;
* `toRSIA_succ` — соседние фазы конвейера переходят в соседние фазы кольца;
* `toRSIA_surjective` — конвейер обходит всё кольцо;
* `paul_same_ring_phase_as_peter` — Павел и Пётр стоят в одной фазе кольца;
* `paul_ne_peter` — но это разные фазы конвейера;
* `pipeline_spiral_not_cycle` — итоговый шов.
-/

namespace Bridges.ApostleRSIA

open ApostlePipeline

/-- Проекция фазы конвейера в кольцо фаз RSIA по её номеру. -/
def toRSIA (ph : Phase) : UAM_RSIA.Phase :=
  (UAM_RSIA.Phase.next^[ph.index]) UAM_RSIA.Phase.construction

/-- Соседние позиции конвейера переходят в соседние фазы кольца. -/
theorem toRSIA_succ (i : Fin 12) :
    toRSIA (CanonApostle.phaseAt ⟨i.val + 1, by omega⟩) =
      (toRSIA (CanonApostle.phaseAt ⟨i.val, by omega⟩)).next := by
  fin_cases i <;> rfl

/-- Конвейер обходит всё кольцо фаз. -/
theorem toRSIA_surjective (q : UAM_RSIA.Phase) : ∃ ph : Phase, toRSIA ph = q := by
  cases q
  · exact ⟨Phase.john, rfl⟩
  · exact ⟨Phase.peter, rfl⟩
  · exact ⟨Phase.andrew, rfl⟩
  · exact ⟨Phase.jamesZebedee, rfl⟩

/-- Павел стоит в той же фазе кольца, что и Пётр: `13 ≡ 1 (mod 4)`. -/
theorem paul_same_ring_phase_as_peter : toRSIA Phase.paul = toRSIA Phase.peter := rfl

/-- Но Павел и Пётр — разные фазы конвейера. -/
theorem paul_ne_peter : Phase.paul ≠ Phase.peter := by decide

/-- **Шов.** Конвейер проецируется на кольцо фаз так, что финальная фаза
совпадает с начальной в кольце, но не совпадает с ней в самом конвейере:
возврат структурный, не буквальный — тот же мотив, что у спирали канона. -/
theorem pipeline_spiral_not_cycle :
    toRSIA Phase.paul = toRSIA Phase.peter ∧ Phase.paul ≠ Phase.peter :=
  ⟨paul_same_ring_phase_as_peter, paul_ne_peter⟩

/-- Число фаз конвейера даёт три полных оборота кольца и один шаг. -/
theorem flow_length_mod_ring : flow.length = 4 * 3 + 1 := by decide

end Bridges.ApostleRSIA
