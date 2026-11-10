import RequestProject.Example
import RequestProject.MetaLearning
import RequestProject.Collective
import RequestProject.Curriculum

/-!
# Пример: работа агентного протокола на демонстрационном графе

Продолжение примера из `RequestProject.Example`: показано, что агентный
протокол непуст и его гарантии применимы невырожденно. Генератор предлагает
новый механизм, интегратор связывает его с существующим концептом,
верификатор повышает зрелость — весь след легален, и после него граф
по-прежнему нормализован, ацикличен и состоит из корректных объектов.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath
namespace Demo

/-- Агент-генератор. -/
def gen : Agent := ⟨10, Role.generator, 1⟩

/-- Агент-интегратор. -/
def intg : Agent := ⟨11, Role.integrator, 1⟩

/-- Агент-верификатор. -/
def ver : Agent := ⟨12, Role.verifier, 1⟩

/-- MECHANISM-4: механизм обратной связи (предлагается генератором). -/
def mFeed : KnowledgeObject := ⟨4, ObjectKind.mechanism, "FeedbackLoop", Maturity.prototype, 1 / 2⟩

/-- Связь «механизм использует концепт информации». -/
def rMC : KnowledgeRelation := ⟨4, 1, RelationKind.uses, 1 / 2⟩

theorem h4 : mFeed.id ∉ atlas.ids := by decide

/-- Состояние графа после действия генератора. -/
def atlas1 : KnowledgeGraph := atlas.addObject mFeed h4

theorem step_propose : atlas.step (Action.propose mFeed) = atlas1 := by
  simp only [KnowledgeGraph.step, atlas1, dif_pos h4]

theorem atlas1_ids : atlas1.ids = insert 4 atlas.ids := atlas.addObj_ids mFeed h4

theorem atlas1_dep (a b : ℕ) : atlas1.Dep a b ↔ atlas.Dep a b := Iff.rfl

/-- Первое действие разрешено: генератор предлагает корректный незрелый
объект, которого в графе ещё не было. -/
theorem perm_propose : Permitted atlas gen (Action.propose mFeed) := by
  refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · norm_num [mFeed]
  · norm_num [mFeed]
  · intro h; exact absurd h (by decide)
  · decide
  · decide

/-- Второе действие разрешено: интегратор связывает существующие объекты
и не замыкает цикл зависимостей. -/
theorem perm_link : Permitted atlas1 intg (Action.link rMC) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [atlas1_ids]; decide
  · rw [atlas1_ids]; decide
  · intro h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, -⟩
    · exact absurd heq (by decide)
    · exact atlas_foundation c ((atlas1_dep _ _).1 hc)

/-- Состояние графа после действия интегратора. -/
def atlas2 : KnowledgeGraph :=
  atlas1.addRelation rMC (by rw [atlas1_ids]; decide) (by rw [atlas1_ids]; decide)

theorem step_link : atlas1.step (Action.link rMC) = atlas2 := by
  have h : rMC.source ∈ atlas1.ids ∧ rMC.target ∈ atlas1.ids := by
    constructor <;> (rw [atlas1_ids]; decide)
  simp only [KnowledgeGraph.step, atlas2, dif_pos h]

/-- Третье действие разрешено: верификатор повышает зрелость до `validated`
(до статуса аксиомы он поднять её не мог бы — уверенность меньше единицы). -/
theorem perm_promote : Permitted atlas2 ver (Action.promote 4 Maturity.validated) := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd h (by decide)

/-- Протокольный след: предложение → связывание → верификация. -/
def trace : List (Agent × Action) :=
  [(gen, Action.propose mFeed), (intg, Action.link rMC),
    (ver, Action.promote 4 Maturity.validated)]

/-- Весь след легален. -/
theorem trace_legal : Legal atlas trace := by
  refine Legal.cons perm_propose ?_
  rw [step_propose]
  refine Legal.cons perm_link ?_
  rw [step_link]
  exact Legal.cons perm_promote Legal.nil

theorem atlas_allWellFormed : atlas.AllWellFormed := by
  intro o ho
  fin_cases ho <;>
    exact ⟨by norm_num [cInfo, iUnc, sRes], by norm_num [cInfo, iUnc, sRes], fun _ => rfl⟩

/-- После легального следа граф по-прежнему нормализован. -/
theorem trace_normalized : (atlas.run trace).Normalized :=
  atlas.run_normalized trace_legal atlas_normalized

/-- После легального следа граф по-прежнему ацикличен. -/
theorem trace_acyclic : (atlas.run trace).Acyclic :=
  atlas.run_acyclic trace_legal atlas_acyclic

/-- После легального следа все объекты графа корректны. -/
theorem trace_allWellFormed : (atlas.run trace).AllWellFormed :=
  atlas.run_allWellFormed trace_legal atlas_allWellFormed

/-! ### След без верификатора не канонизирует знание -/

/-- Тот же след без действия верификатора. -/
def traceNoVer : List (Agent × Action) :=
  [(gen, Action.propose mFeed), (intg, Action.link rMC)]

theorem traceNoVer_legal : Legal atlas traceNoVer := by
  refine Legal.cons perm_propose ?_
  rw [step_propose]
  exact Legal.cons perm_link Legal.nil

/-- Без верификатора множество канонического знания не растёт. -/
theorem traceNoVer_no_canonization :
    (atlas.run traceNoVer).canonicalIds ⊆ atlas.canonicalIds := by
  refine atlas.run_canonicalIds_subset traceNoVer_legal ?_
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · decide
  · rcases List.mem_cons.1 hp with rfl | hp
    · decide
    · exact absurd hp (by simp)

/-! ### Слияние знаний двух агентов -/

/-- Граф знаний второго агента: тот же концепт «информация» и свой механизм. -/
def atlasB : KnowledgeGraph where
  objects := {cInfo, mFeed}
  relations := {rMC}
  unique_id := by
    intro a ha b hb hab
    fin_cases ha <;> fin_cases hb <;> simp_all [cInfo, mFeed]
  src_closed := by decide
  tgt_closed := by decide

theorem atlas_atlasB_compatible : KnowledgeGraph.Compatible atlas atlasB := by
  intro a ha b hb hab
  fin_cases ha <;> fin_cases hb <;> simp_all [cInfo, iUnc, sRes, mFeed]

/-- Коллективный граф знаний двух агентов. -/
def atlasMerged : KnowledgeGraph := KnowledgeGraph.merge atlas atlasB atlas_atlasB_compatible

/-- Слияние сохраняет нормализованность: агенты не спорят об именах. -/
theorem atlasB_normalized : atlasB.Normalized := by
  intro a ha b hb hk hl
  fin_cases ha <;> fin_cases hb <;> simp_all [cInfo, mFeed]

theorem atlasMerged_normalized : atlasMerged.Normalized := by
  refine KnowledgeGraph.merge_normalized _ atlas_normalized atlasB_normalized ?_
  intro a ha b hb hk hl
  fin_cases ha <;> fin_cases hb <;> simp_all [cInfo, iUnc, sRes, mFeed]

/-- Коллективный граф ациклен: оба агента согласны с одной шкалой уровней. -/
theorem atlasMerged_acyclic : atlasMerged.Acyclic := by
  refine KnowledgeGraph.merge_acyclic_of_rank _ id ?_ ?_ <;>
    · rintro a b ⟨r, hr, -, rfl, rfl⟩
      fin_cases hr <;> decide

/-- В коллективном графе нет заявленных противоречий. -/
theorem atlasMerged_conflictFree : atlasMerged.ConflictFree := by
  refine KnowledgeGraph.merge_conflictFree _ ?_ ?_ <;>
    · rintro i j ⟨r, hr, hk, -, -⟩
      fin_cases hr <;> simp_all [rIU, rSI, rSC, rMC]

/-! ### Траектория изучения -/

/-- Конкретная траектория изучения демонстрационного графа:
сначала концепт, затем инвариант, затем шаг. -/
theorem atlas_curriculum_explicit : atlas.Curriculum [1, 2, 3] := by
  refine ⟨?_, by decide, ?_⟩
  · intro i
    rw [atlas_ids]
    simp
  · rintro a b ⟨r, hr, -, rfl, rfl⟩
    fin_cases hr <;> decide

/-- Общая теорема о существовании траектории применима к этому графу. -/
theorem atlas_exists_curriculum : ∃ l, atlas.Curriculum l :=
  atlas.exists_curriculum atlas_acyclic

end Demo
end Polymath
