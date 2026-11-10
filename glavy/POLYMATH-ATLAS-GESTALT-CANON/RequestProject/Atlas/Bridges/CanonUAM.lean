import RequestProject.Atlas.Canon.Core
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_MonoidAction
import RequestProject.Atlas.UAM_DFAEval

/-!
# Шов: Канон Горизонтов ↔ UAM

Карта соответствия (`Canon/Correspondence.lean`) утверждала связь
«Толчок (Слой 1) = свободный моноид» только как комментарий. Здесь эта связь
получает формальное содержание: сдвиг слоёв канона — это в точности действие
свободного моноида `UAM_Free.FreeMonoid Unit` (слов над одной буквой) на типе
слоёв `Layer n`, в смысле `UAM_MonoidAction.MonoidAction` из UAM.

Формально доказано:

* `shiftAction` — сдвиг задаёт действие свободного моноида над `Unit`;
* `shiftAction_eq_lift` — это действие есть в точности универсальное продолжение
  (`UAM_Free.FreeMonoid.lift`) отображения единственной буквы в `shift`;
* `act_structurallyEquivalent` — вся орбита структурно эквивалентна исходному
  слою («спираль замыкается структурно»);
* `act_eq_self_iff` — но буквально орбита не замыкается: никакое непустое слово
  не возвращает слой в себя («лестница не замыкается»);
* `spiral_structural_not_literal` — оба утверждения вместе;
* `orbit_infinite` — орбита бесконечна;
* `canonDFA` и `canonDFA_language` — счётчик сдвигов канона как DFA из
  `UAM_DFAEval`: автомат принимает ровно слова длины `< canonicalShiftCount`,
  то есть шаги внутри одного витка спирали.
-/

namespace Bridges.CanonUAM

open UAM_MonoidAction

/-- Буква сдвига: единственный образующий свободного моноида канона. -/
def tick : UAM_Free.FreeMonoid Unit := UAM_Free.FreeMonoid.of ()

/-- Действие слова `w` на слое: столько сдвигов, какова длина слова. -/
def actOn {n : Nat} (w : UAM_Free.FreeMonoid Unit) (L : Layer n) : Layer n :=
  (shift^[w.length]) L

/-- Сдвиг канона как действие свободного моноида над одной буквой. -/
def shiftAction (n : Nat) :
    MonoidAction (UAM_Free.FreeMonoid Unit) (Layer n) where
  act := actOn
  one_act := by
    funext L
    rfl
  mul_act := by
    intro a b
    funext L
    show (shift^[(a ++ b).length]) L = (shift^[b.length]) ((shift^[a.length]) L)
    rw [List.length_append, Nat.add_comm, Function.iterate_add_apply]

@[simp] theorem shiftAction_act {n : Nat} (w : UAM_Free.FreeMonoid Unit)
    (L : Layer n) : (shiftAction n).act w L = (shift^[w.length]) L := rfl

/-- Действие одной буквы — один сдвиг. -/
theorem shiftAction_tick {n : Nat} (L : Layer n) :
    (shiftAction n).act tick L = shift L := rfl

/-- Действие есть универсальное продолжение отображения буквы в `shift`:
связь с универсальным свойством свободного моноида из `UAM_Free`. -/
theorem shiftAction_eq_lift (n : Nat) (w : UAM_Free.FreeMonoid Unit) :
    (shiftAction n).act w =
      (@UAM_Free.FreeMonoid.lift Unit (Layer n → Layer n)
        UAM_Action.instMonoid (fun _unused => shift)).toFun w := by
  induction w with
  | nil => rfl
  | cons a ws ih =>
      funext L
      show (shift^[(a :: ws).length]) L =
        (@UAM_Free.FreeMonoid.liftFun Unit (Layer n → Layer n)
          UAM_Action.instMonoid (fun _unused => shift) (a :: ws)) L
      have hL : (shift^[(a :: ws).length]) L = (shift^[ws.length]) (shift L) := by
        simp [List.length_cons, Function.iterate_succ_apply]
      rw [hL]
      have hws := congrFun ih (shift L)
      simpa [UAM_Free.FreeMonoid.liftFun, UAM_Action.mul_apply] using hws

/-- Номер слоя растёт ровно на длину слова. -/
theorem act_idx {n : Nat} (w : UAM_Free.FreeMonoid Unit) (L : Layer n) :
    ((shiftAction n).act w L).idx = L.idx + w.length :=
  (shift_iterate_fields L w.length).1

/-- Имена сохраняются: вся орбита структурно эквивалентна исходному слою.
«Спираль замыкается структурно». -/
theorem act_structurallyEquivalent {n : Nat} (w : UAM_Free.FreeMonoid Unit)
    (L : Layer n) : (shiftAction n).act w L ≈ L :=
  shift_iterate_structurally_equivalent L w.length

/-- Буквального возврата нет: только пустое слово оставляет слой на месте.
«Лестница не замыкается». -/
theorem act_eq_self_iff {n : Nat} (w : UAM_Free.FreeMonoid Unit) (L : Layer n) :
    (shiftAction n).act w L = L ↔ w = [] := by
  constructor
  · intro h
    have hidx : L.idx + w.length = L.idx := by
      rw [← act_idx w L, h]
    have hlen : w.length = 0 := by omega
    exact List.length_eq_zero_iff.mp hlen
  · intro h
    subst h
    rfl

/-- Шов между «спиралью» канона и «лестницей» UAM: структурный возврат есть
всегда, буквального возврата нет никогда. -/
theorem spiral_structural_not_literal {n : Nat} (L : Layer n) :
    (∀ w : UAM_Free.FreeMonoid Unit, (shiftAction n).act w L ≈ L) ∧
    (∀ w : UAM_Free.FreeMonoid Unit, w ≠ [] → (shiftAction n).act w L ≠ L) := by
  refine ⟨fun w => act_structurallyEquivalent w L, fun w hw hcontra => ?_⟩
  exact hw ((act_eq_self_iff w L).mp hcontra)

/-- Итерации сдвига попарно различны. -/
theorem iterate_injective {n : Nat} (L : Layer n) :
    Function.Injective (fun k : Nat => (shift^[k]) L) := by
  intro k m h
  simp only at h
  have hk : ((shift^[k]) L).idx = L.idx + k := (shift_iterate_fields L k).1
  have hm : ((shift^[m]) L).idx = L.idx + m := (shift_iterate_fields L m).1
  have hsum : L.idx + k = L.idx + m := by rw [← hk, ← hm, h]
  omega

/-- Орбита слоя под действием сдвига бесконечна. -/
theorem orbit_infinite {n : Nat} (L : Layer n) :
    ((shiftAction n).orbit L).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : Nat => (shift^[k]) L) (iterate_injective L) ?_
  intro k
  exact ⟨List.replicate k (), by simp [shiftAction, actOn]⟩

/-! ### Виток спирали как конечный автомат UAM -/

/-- Счётчик сдвигов внутри одного витка: DFA над алфавитом из одной буквы,
состояния — `Fin (canonicalShiftCount + 1)` с поглощающим последним состоянием. -/
def canonDFA : UAM_DFAEval.DFA Unit (Fin (canonicalShiftCount + 1)) where
  δ := fun q _unused => if h : q.val + 1 < canonicalShiftCount + 1 then ⟨q.val + 1, h⟩ else q
  q₀ := ⟨0, by omega⟩
  F := {q | q.val < canonicalShiftCount}

theorem canonDFA_eval_val (w : UAM_Free.FreeMonoid Unit) :
    (canonDFA.eval w).val = min w.length canonicalShiftCount := by
  have key : ∀ (v : UAM_Free.FreeMonoid Unit) (q : Fin (canonicalShiftCount + 1)),
      (canonDFA.evalFrom q v).val = min (q.val + v.length) canonicalShiftCount := by
    intro v
    induction v with
    | nil =>
        intro q
        have hq : q.val < canonicalShiftCount + 1 := q.isLt
        simp only [UAM_DFAEval.DFA.evalFrom, List.length_nil]
        omega
    | cons a ws ih =>
        intro q
        rw [UAM_DFAEval.DFA.evalFrom_cons, ih]
        by_cases h : q.val + 1 < canonicalShiftCount + 1
        · simp only [canonDFA, dif_pos h, List.length_cons]
          omega
        · simp only [canonDFA, dif_neg h, List.length_cons]
          omega
  have hkey := key w canonDFA.q₀
  simpa [canonDFA] using hkey

/-- Язык автомата: ровно слова короче канонического числа сдвигов, то есть
шаги, не завершившие виток спирали. -/
theorem canonDFA_language :
    canonDFA.language =
      {w : UAM_Free.FreeMonoid Unit | w.length < canonicalShiftCount} := by
  ext w
  show (canonDFA.eval w) ∈ canonDFA.F ↔ w.length < canonicalShiftCount
  simp only [canonDFA, Set.mem_setOf_eq]
  rw [show ((canonDFA.eval w).val) = min w.length canonicalShiftCount from
    canonDFA_eval_val w]
  omega

/-- Четыре сдвига канонического текста — это слово из четырёх букв, выводящее
автомат за пределы принимающих состояний, а слой — на следующий виток. -/
theorem four_ticks_leave_language :
    List.replicate canonicalShiftCount () ∉ canonDFA.language := by
  rw [canonDFA_language]
  simp

end Bridges.CanonUAM
