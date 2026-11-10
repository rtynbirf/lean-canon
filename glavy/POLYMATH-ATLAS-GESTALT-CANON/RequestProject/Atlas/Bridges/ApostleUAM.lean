import RequestProject.Atlas.ApostlePipeline
import RequestProject.Atlas.UAM_DFAEval
import RequestProject.Atlas.UAM_MonoidAction

/-!
# Шов: ApostlePipeline ↔ UAM

Конвейер из тринадцати фаз (`ApostlePipeline`) был описан как «детерминированный
конечный автомат» только в комментарии. Здесь он становится автоматом в смысле
UAM: `UAM_DFAEval.DFA` над алфавитом фаз `Phase` с множеством состояний `St`.

Формально доказано:

* `pipelineDFA` — конвейер как DFA из `UAM_DFAEval`;
* `evalFrom_eq_foldl` — вычисление автомата совпадает с прогоном фаз;
* `runToJudas_eq_evalFrom`, `runFull_eq_eval` — исходные прогоны совпадают
  с вычислением автомата на словах `orderToJudas` и `flow`;
* `phaseAction` — прогон фаз как действие свободного моноида `FreeMonoid Phase`
  на состояниях (`UAM_MonoidAction.MonoidAction`), и `phaseAction_eq_evalFrom`;
* `judas_word_mem_language_iff` — закон краха в терминах языка автомата:
  слово «Пётр … Иуда» принимается ровно тогда, когда нагрузка укладывается
  в стек;
* `flow_mem_language` — полное слово из тринадцати фаз принимается всегда
  («Павел вне Стека»);
* `reachable_of_paul` — состояние после `Павла` всегда одно и то же, поэтому
  язык автомата замкнут относительно приписывания фазы `paul`.
-/

namespace Bridges.ApostleUAM

open ApostlePipeline UAM_MonoidAction

/-- Конвейер апостолов как DFA из UAM: буквы — фазы, состояния — `St`,
принимающие состояния — те, в которых ядро не упало. -/
def pipelineDFA (p : Params) : UAM_DFAEval.DFA Phase St where
  δ := fun s ph => step p ph s
  q₀ := start
  F := {s | s.crashed = false}

/-- Вычисление автомата — это в точности прогон списка фаз. -/
theorem evalFrom_eq_foldl (p : Params) (w : UAM_Free.FreeMonoid Phase) (s : St) :
    (pipelineDFA p).evalFrom s w = w.foldl (fun s ph => step p ph s) s := by
  induction w generalizing s with
  | nil => rfl
  | cons a ws ih =>
      rw [UAM_DFAEval.DFA.evalFrom_cons, ih]
      rfl

/-- Прогон фаз 1–12 — вычисление автомата на слове `orderToJudas`. -/
theorem runToJudas_eq_evalFrom (p : Params) (s : St) :
    runToJudas p s = (pipelineDFA p).evalFrom s orderToJudas := by
  rw [evalFrom_eq_foldl]
  rfl

/-- Полный прогон — вычисление автомата на слове `flow` из начального состояния. -/
theorem runFull_eq_eval (p : Params) :
    runFull p start = (pipelineDFA p).eval flow := by
  show runFull p start = (pipelineDFA p).evalFrom (pipelineDFA p).q₀ flow
  rw [evalFrom_eq_foldl]
  rfl

/-! ### Прогон фаз как действие свободного моноида -/

/-- Прогон произвольного слова фаз как действие свободного моноида на состояниях. -/
def phaseAction (p : Params) : MonoidAction (UAM_Free.FreeMonoid Phase) St where
  act := fun w s => w.foldl (fun s ph => step p ph s) s
  one_act := by
    funext s
    rfl
  mul_act := by
    intro a b
    funext s
    show (a ++ b).foldl (fun s ph => step p ph s) s =
      b.foldl (fun s ph => step p ph s) (a.foldl (fun s ph => step p ph s) s)
    rw [List.foldl_append]

/-- Действие свободного моноида фаз совпадает с вычислением DFA. -/
theorem phaseAction_eq_evalFrom (p : Params) (w : UAM_Free.FreeMonoid Phase) (s : St) :
    (phaseAction p).act w s = (pipelineDFA p).evalFrom s w :=
  (evalFrom_eq_foldl p w s).symm

/-! ### Язык конвейера -/

/-- Слово фаз принимается ровно тогда, когда прогон не оставляет флаг краха. -/
theorem mem_language_iff (p : Params) (w : UAM_Free.FreeMonoid Phase) :
    w ∈ (pipelineDFA p).language ↔
      (w.foldl (fun s ph => step p ph s) start).crashed = false := by
  show ((pipelineDFA p).evalFrom (pipelineDFA p).q₀ w) ∈ (pipelineDFA p).F ↔ _
  rw [evalFrom_eq_foldl]
  rfl

/-- **Закон краха в терминах языка.** Слово «Пётр … Иуда» принимается автоматом
ровно тогда, когда выжившая нагрузка укладывается в ёмкость стека. -/
theorem judas_word_mem_language_iff (p : Params) :
    orderToJudas ∈ (pipelineDFA p).language ↔ reduced p ≤ p.capacity := by
  rw [mem_language_iff]
  change (runToJudas p start).crashed = false ↔ _
  rw [runToJudas_crashed]
  simp only [decide_eq_false_iff_not]
  omega

/-- **Павел вне Стека.** Полное слово из тринадцати фаз принимается всегда. -/
theorem flow_mem_language (p : Params) : flow ∈ (pipelineDFA p).language := by
  rw [mem_language_iff]
  change (runFull p start).crashed = false
  rw [paul_recovers]

/-- Состояние после фазы `paul` не зависит от предыстории. -/
theorem evalFrom_paul (p : Params) (w : UAM_Free.FreeMonoid Phase) (s : St) :
    (pipelineDFA p).evalFrom s (w ++ [Phase.paul]) = start := by
  rw [evalFrom_eq_foldl, List.foldl_append]
  rfl

/-- Приписывание `paul` делает принимаемым любое слово: язык автомата замкнут
относительно завершающей фазы «корневого доступа». -/
theorem append_paul_mem_language (p : Params) (w : UAM_Free.FreeMonoid Phase) :
    w ++ [Phase.paul] ∈ (pipelineDFA p).language := by
  show ((pipelineDFA p).evalFrom (pipelineDFA p).q₀ (w ++ [Phase.paul]))
    ∈ (pipelineDFA p).F
  rw [evalFrom_paul]
  rfl

end Bridges.ApostleUAM
