import RequestProject.Verification
import RequestProject.Certificate
import RequestProject.Retraction
import RequestProject.Example

/-!
# Пример: работа алгоритма верификации

Здесь алгоритм из `RequestProject/Verification.lean` запускается на конкретных
графах.

* положительный пример — демонстрационный граф знаний ATLAS из
  `RequestProject/Example.lean`: вердикт верификации вычисляется как `true`,
  и множество обоснованных утверждений вычисляется явно;
* отрицательный пример — граф доказательств с круговым обоснованием
  (`1` доказано из `2`, `2` доказано из `1`, аксиом нет): вердикт `false`,
  причём необоснованность обоих утверждений доказана.

Все утверждения этого модуля закрыты вычислением (`decide` / `rfl`), то есть
алгоритм действительно исполняется ядром Lean.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath
namespace Demo

/-! ## Положительный пример: граф ATLAS верифицируется -/

/-- Граф доказательств, порождённый демонстрационным графом знаний. -/
def atlasPG : ProofGraph :=
  atlas.toProofGraph atlasAx atlasPr atlasAx_sub atlasPr_sub atlasAx_leaf

/-- Вычисленное множество обоснованных утверждений — все три объекта. -/
theorem atlasPG_groundedSet : atlasPG.groundedSet = {1, 2, 3} := by decide

/-- Вердикт верификации демонстрационного графа знаний вычисляется как `true`. -/
theorem atlas_verifiedBy :
    atlas.verifiedBy atlasAx atlasPr atlasAx_sub atlasPr_sub atlasAx_leaf = true := by
  decide

/-- Тот же результат, но полученный из общей теоремы: вердикт истинен,
следовательно каждый объект графа обоснован. -/
theorem atlas_grounded_by_computation :
    ∀ o ∈ atlas.objects, atlasPG.Grounded o.id :=
  (atlas.verifiedBy_eq_true_iff atlasAx atlasPr atlasAx_sub atlasPr_sub
    atlasAx_leaf).1 atlas_verifiedBy

/-- Для демонстрационного графа существует сертификат — порядок вывода, в
котором посылки каждого объекта стоят строго раньше него. -/
theorem atlas_certificate :
    ∃ l : List ℕ, l.Nodup ∧ (∀ c, c ∈ l ↔ atlasPG.Grounded c) ∧
      l.Pairwise (fun a b => b ∉ atlasPG.premises a) :=
  atlasPG.exists_derivation_order

/-! ## Отзыв аксиомы: зона поражения -/

/-- Единственная аксиома графа отозвана: обоснованных утверждений не
остаётся вовсе — всё знание графа опиралось на неё. -/
theorem atlas_retract_axiom_groundedSet : (atlasPG.retract 1).groundedSet = ∅ := by decide

/-- После отзыва аксиомы граф не проходит верификацию. -/
theorem atlas_retract_axiom_not_verified : (atlasPG.retract 1).verified = false := by decide

/-! ## Отрицательный пример: круговое обоснование не проходит верификацию -/

/-- Посылки кругового графа: `1` опирается на `2`, `2` — на `1`. -/
def circPremises : ℕ → Finset ℕ := fun c => if c = 1 then {2} else if c = 2 then {1} else ∅

/-- Граф доказательств с круговым обоснованием и без аксиом. -/
def circular : ProofGraph where
  claims := {1, 2}
  axioms := ∅
  proved := {1, 2}
  premises := circPremises
  axioms_subset := by decide
  proved_subset := by decide
  premises_subset := by decide
  premises_outside := by
    intro c hc
    have h1 : c ≠ 1 := by rintro rfl; exact hc (by decide)
    have h2 : c ≠ 2 := by rintro rfl; exact hc (by decide)
    simp [circPremises, h1, h2]
  axioms_leaf := by decide

/-- Итерация не выводит ничего: множество обоснованных утверждений пусто. -/
theorem circular_groundedSet : circular.groundedSet = ∅ := by decide

/-- **Круговое доказательство отвергается вычислением.** -/
theorem circular_not_verified : circular.verified = false := by decide

/-- Ни одно из двух утверждений кругового графа не обосновано. -/
theorem circular_not_grounded : ¬ circular.Grounded 1 ∧ ¬ circular.Grounded 2 := by
  constructor
  · intro h
    have := (circular.mem_groundedSet_iff 1).2 h
    rw [circular_groundedSet] at this
    exact absurd this (Finset.notMem_empty 1)
  · intro h
    have := (circular.mem_groundedSet_iff 2).2 h
    rw [circular_groundedSet] at this
    exact absurd this (Finset.notMem_empty 2)

/-- Контрпример, выданный вердиктом, действительно существует. -/
theorem circular_counterexample : ∃ c ∈ circular.claims, ¬ circular.Grounded c :=
  circular.not_verified_iff_exists_ungrounded.1 circular_not_verified

end Demo
end Polymath
