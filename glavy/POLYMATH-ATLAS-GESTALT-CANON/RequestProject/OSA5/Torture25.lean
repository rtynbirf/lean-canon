/-
# OSA-5.0 — сводный набор Torture Tests T01–T25

T01–T20 — набор OSA-4.1 (`RequestProject/OSA4/Audit/Torture20.lean`).
T21–T25 добавлены слоем многошагового ремонта
(`RequestProject/OSA5/Repair.lean`) и проверяют то, чего одношаговый критерий
`repairFor` не проверял: отсутствие одношаговой починки, наличие двухшаговой,
доведение починенной цепочки до `PASS`, минимальность плана и честный отказ
при недостижимой цели.

Итог — `torture25_all_pass : ∀ t : TortureId25, t.passed` и
`torture25_card : Fintype.card TortureId25 = 25`.
-/
import RequestProject.OSA4.Audit.Integration
import RequestProject.OSA5.Repair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Polymath.OSA5

open Polymath.OSA4

/-- Идентификаторы расширенного набора: 20 тестов аудита OSA-4.1 и пять
тестов многошагового ремонта. -/
inductive TortureId25
  /-- Тест из набора OSA-4.1. -/
  | old (t : TortureId)
  /-- Одношаговой починки нет. -/
  | T21
  /-- Двухшаговая починка найдена. -/
  | T22
  /-- Починенная цепочка компилируется в PASS. -/
  | T23
  /-- План минимальной длины. -/
  | T24
  /-- Недостижимая цель: честный отказ. -/
  | T25
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace TortureId25

/-- Проверяемое тестом утверждение. -/
def passed : TortureId25 → Prop
  | .old t => t.passed
  | .T21 => searchRepair registry modelGoal 1 s0 = none
  | .T22 => searchRepair registry modelGoal 2 s0 = some [MEASURE, CHECK_SUFFICIENCY]
  | .T23 =>
      compile ⟨registry, s0, [MEASURE, CHECK_SUFFICIENCY] ++ (MODEL :: []),
        .factExists "Model"⟩ = ⟨.PASS, none, none⟩
  | .T24 => minRepair registry modelGoal 4 s0 = some [MEASURE, CHECK_SUFFICIENCY]
  | .T25 => searchRepair registry (.factExists "Teleported") 3 s0 = none

end TortureId25

/-- **Все 25 тестов пройдены.** -/
theorem torture25_all_pass : ∀ t : TortureId25, t.passed := by
  intro t
  cases t with
  | old t => exact torture_all_pass t
  | T21 => exact T21_no_one_step_repair
  | T22 => exact T22_two_step_repair
  | T23 => exact T23_repaired_pass
  | T24 => exact T24_minimal_plan
  | T25 => exact T25_no_repair_for_unreachable

/-- Тестов ровно 25. -/
theorem torture25_card : Fintype.card TortureId25 = 25 := by decide

/-- Проваленных тестов нет. -/
theorem torture25_no_failures : ¬ ∃ t : TortureId25, ¬ t.passed := by
  rintro ⟨t, ht⟩
  exact ht (torture25_all_pass t)

/-- **Сводный вердикт слоёв OSA-4.1 + OSA-5.0.**  Все 25 тестов пройдены,
шесть интеграционных тестов пройдены, многошаговый ремонт корректен и полон. -/
theorem osa5_audit_report :
    (∀ t : TortureId25, t.passed) ∧
    (∀ t : IntegrationTest, t.claim) ∧
    (∀ (reg : List Op) (goal : Pred) (n : ℕ) (s : KState),
      (searchRepair reg goal n s).isSome ↔
        ∃ p : List Op, chainEnabled p s ∧ eval (execChain p s) goal = .TRUE_KNOWN ∧
          (∀ o ∈ p, o ∈ reg) ∧ p.length ≤ n) :=
  ⟨torture25_all_pass, integration_all_pass, searchRepair_isSome_iff⟩

end Polymath.OSA5
