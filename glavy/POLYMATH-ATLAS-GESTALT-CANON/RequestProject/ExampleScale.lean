import RequestProject.Cycle
import RequestProject.ExampleAgents

/-!
# Пример: башня масштабов и цикл на демонстрационном графе

Проверка непустоты слоёв `RequestProject.Scale` и `RequestProject.Cycle`
на конкретных данных.

Строится трёхступенчатая башня знания над демонстрационным графом:

* уровень 0 — исходный граф `atlas` (индивидуальное знание);
* уровень 1 — к нему добавлен механизм «обратная связь» (`atlas1`);
* уровень 2 и выше — добавлена связь механизма с концептом (`atlas2`),
  дальше знание не растёт.

Показано, что это действительно башня (каждый уровень расширяет
предыдущий), что знание нижних уровней сохраняется на верхних, что
у механизма «обратная связь» уровень рождения равен 1, что башня
насыщается на уровне 2 и что все уровни ацикличны.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath
namespace Demo

/-! ## Конкретная башня знания -/

/-- Уровни демонстрационной башни знания. -/
def towerGraph : ℕ → KnowledgeGraph
  | 0 => atlas
  | 1 => atlas1
  | _ + 2 => atlas2

/-- Демонстрационная башня: каждый следующий уровень включает предыдущий. -/
def demoTower : KnowledgeTower where
  graph := towerGraph
  step_extends := by
    intro n
    match n with
    | 0 => exact atlas.addObj_extends mFeed h4
    | 1 =>
      exact atlas1.addRel_extends rMC (by rw [atlas1_ids]; decide) (by rw [atlas1_ids]; decide)
    | (k + 2) => exact KnowledgeGraph.extends_refl _

@[simp] theorem demoTower_graph (n : ℕ) : demoTower.graph n = towerGraph n := rfl

/-- Знание нижнего уровня целиком присутствует на верхнем. -/
theorem demoTower_objects_mono : atlas.objects ⊆ (demoTower.graph 7).objects :=
  demoTower.objects_subset_of_le (m := 0) (by norm_num)

/-- Механизм «обратная связь» появляется на уровне 1 и отсутствует
на уровне 0: его уровень рождения равен единице. -/
theorem demoTower_birth_mFeed :
    mFeed ∈ (demoTower.graph 1).objects ∧ mFeed ∉ (demoTower.graph 0).objects := by
  constructor
  · show mFeed ∈ atlas1.objects
    simp [atlas1, KnowledgeGraph.addObject]
  · show mFeed ∉ atlas.objects
    decide

/-- Общая теорема об уровне рождения применима к этой башне. -/
theorem demoTower_exists_birth :
    ∃ k ≤ 3, mFeed ∈ (demoTower.graph k).objects ∧
      (∀ j < k, mFeed ∉ (demoTower.graph j).objects) ∧
      ∀ j, k ≤ j → mFeed ∈ (demoTower.graph j).objects := by
  refine demoTower.exists_birth (n := 3) ?_
  show mFeed ∈ atlas2.objects
  simp [atlas2, KnowledgeGraph.addRelation, atlas1, KnowledgeGraph.addObject]

/-- **Насыщение конкретной башни**: начиная с уровня 2 знание не растёт. -/
theorem demoTower_saturated (n : ℕ) (hn : 2 ≤ n) :
    demoTower.graph (n + 1) = demoTower.graph n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rfl

/-- Каждый уровень башни ацикличен: демонстрационный протокольный след
не создаёт круговых зависимостей. -/
theorem demoTower_acyclic : ∀ n, (demoTower.graph n).Acyclic := by
  have h2 : atlas2.Acyclic := by
    refine atlas1.addRel_acyclic rMC (by rw [atlas1_ids]; decide)
      (by rw [atlas1_ids]; decide) atlas_acyclic ?_
    intro h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, -⟩
    · exact absurd heq (by decide)
    · exact atlas_foundation c ((atlas1_dep _ _).1 hc)
  intro n
  match n with
  | 0 => exact atlas_acyclic
  | 1 => exact atlas_acyclic
  | (k + 2) => exact h2

/-- Ацикличность верхнего уровня влечёт ацикличность нижнего — общая
теорема, применённая к башне. -/
theorem demoTower_acyclic_of_le : (demoTower.graph 0).Acyclic :=
  demoTower.acyclic_of_le (m := 0) (n := 5) (by norm_num) (demoTower_acyclic 5)

/-! ## Конкретный цикл фаз -/

/-- Три шага цикла от наблюдения приводят к предсказанию. -/
theorem phase_observe_to_predict : Phase.next^[3] Phase.observe = Phase.predict := rfl

/-- Полный оборот цикла возвращает систему в фазу наблюдения. -/
theorem phase_full_turn : Phase.next^[8] Phase.observe = Phase.observe :=
  Phase.next_iterate_eight _

/-- Тождественный оператор накапливающий, и порождённая им башня — это
башня постоянного знания: тривиальный, но корректный оборот цикла. -/
theorem demo_identity_tower (n : ℕ) :
    (KnowledgeTower.ofAccumulating id accumulating_id atlas).graph n = atlas := by
  simp [KnowledgeTower.ofAccumulating]

end Demo
end Polymath
