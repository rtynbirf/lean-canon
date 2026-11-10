import RequestProject.Atlas.Canon.Core
import RequestProject.Atlas.UAM_RSIA_PhaseRing
import RequestProject.Atlas.Bridges.CanonUAM

/-!
# Шов: Канон Горизонтов ↔ RSIA (кольцо фаз)

Карта соответствия утверждала: «Канон ↔ RSIA. Нет общих элементов. Нет общей
теории.» Проверка показывает более точную картину: у обоих проектов период
равен четырём — `canonicalShiftCount = 4` и четыре фазы `UAM_RSIA.Phase`.
Различие не в отсутствии связи, а в характере возврата: кольцо фаз замыкается
буквально, спираль канона — только структурно.

Формально доказано:

* `phase_period` — четыре шага кольца фаз возвращают фазу в себя;
* `toPhase` — проекция слоя канона в кольцо фаз по номеру витка;
* `toPhase_shift` — проекция эквивариантна: сдвиг слоя переходит в шаг фазы;
* `toPhase_iterate`, `toPhase_period` — проекция переводит четыре сдвига
  в тождество кольца фаз;
* `toPhase_surjective` — каждая фаза достигается некоторым слоем;
* `spiral_projects_onto_ring` — итоговый шов: спираль не замыкается буквально,
  её образ в кольце фаз замыкается за четыре шага.
-/

namespace Bridges.CanonRSIA

open UAM_RSIA

/-- Кольцо фаз замыкается ровно за `canonicalShiftCount` шагов. -/
theorem phase_period (p : Phase) :
    (Phase.next^[canonicalShiftCount]) p = p := by
  cases p <;> rfl

/-- Проекция слоя канона в кольцо фаз RSIA: номер витка задаёт фазу. -/
def toPhase {n : Nat} (L : Layer n) : Phase :=
  (Phase.next^[L.idx]) Phase.construction

/-- Эквивариантность: сдвиг слоя соответствует шагу кольца фаз. -/
theorem toPhase_shift {n : Nat} (L : Layer n) :
    toPhase (shift L) = (toPhase L).next := by
  show (Phase.next^[L.idx + 1]) Phase.construction
    = Phase.next ((Phase.next^[L.idx]) Phase.construction)
  rw [Function.iterate_succ_apply']

/-- Итерация сдвига переходит в итерацию шага фазы. -/
theorem toPhase_iterate {n : Nat} (L : Layer n) (k : Nat) :
    toPhase ((shift^[k]) L) = (Phase.next^[k]) (toPhase L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', toPhase_shift, ih,
        Function.iterate_succ_apply']

/-- Четыре сдвига канона проецируются в тождество кольца фаз. -/
theorem toPhase_period {n : Nat} (L : Layer n) :
    toPhase ((shift^[canonicalShiftCount]) L) = toPhase L := by
  rw [toPhase_iterate, phase_period]

/-- Каждая фаза кольца достигается некоторым слоем канона. -/
theorem toPhase_surjective {n : Nat} (L : Layer n) (p : Phase) :
    ∃ k : Nat, toPhase ((shift^[k]) L) = p := by
  have hcycle : ∀ q : Phase, ∃ k : Nat, (Phase.next^[k]) q = p := by
    intro q
    cases q <;> cases p <;>
      first
        | exact ⟨0, rfl⟩
        | exact ⟨1, rfl⟩
        | exact ⟨2, rfl⟩
        | exact ⟨3, rfl⟩
  obtain ⟨k, hk⟩ := hcycle (toPhase L)
  exact ⟨k, by rw [toPhase_iterate, hk]⟩

/-- **Шов.** Спираль канона не замыкается буквально ни за какое число сдвигов,
но её проекция в кольцо фаз RSIA замыкается ровно за четыре шага, сохраняя при
этом структурную эквивалентность слоёв. -/
theorem spiral_projects_onto_ring {n : Nat} (L : Layer n) :
    ((shift^[canonicalShiftCount]) L ≠ L) ∧
    ((shift^[canonicalShiftCount]) L ≈ L) ∧
    toPhase ((shift^[canonicalShiftCount]) L) = toPhase L := by
  refine ⟨?_, shift_four_structurally_cyclic L, toPhase_period L⟩
  intro h
  have hw : (Bridges.CanonUAM.shiftAction n).act
      (List.replicate canonicalShiftCount ()) L = L := by
    simpa [Bridges.CanonUAM.shiftAction, Bridges.CanonUAM.actOn] using h
  have hnil := (Bridges.CanonUAM.act_eq_self_iff
    (List.replicate canonicalShiftCount ()) L).mp hw
  simp [canonicalShiftCount] at hnil

end Bridges.CanonRSIA
