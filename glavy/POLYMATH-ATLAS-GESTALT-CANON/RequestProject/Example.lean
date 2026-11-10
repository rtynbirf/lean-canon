import RequestProject.ProofGraph

/-!
# Пример: маленький граф знаний ATLAS

Демонстрация непустоты модели: конкретный граф знаний из трёх объектов
(Concept, Invariant, Step) и трёх связей, для которого проверены все
ключевые свойства — целостность, нормализованность, ацикличность,
наличие фундамента и полная обоснованность.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath
namespace Demo

/-- CONCEPT-1: понятие «информация». -/
def cInfo : KnowledgeObject := ⟨1, ObjectKind.concept, "Information", Maturity.canonical, 1⟩

/-- INVARIANT-2: инвариант «неопределённость не возрастает при получении информации». -/
def iUnc : KnowledgeObject := ⟨2, ObjectKind.invariant, "UncertaintyMonotone", Maturity.validated, 1⟩

/-- STEP-3: шаг «остаточная неопределённость». -/
def sRes : KnowledgeObject := ⟨3, ObjectKind.step, "ResidualUncertainty", Maturity.validated, 1⟩

def rIU : KnowledgeRelation := ⟨2, 1, RelationKind.uses, 1⟩
def rSI : KnowledgeRelation := ⟨3, 2, RelationKind.buildsOn, 1⟩
def rSC : KnowledgeRelation := ⟨3, 1, RelationKind.uses, 1⟩

/-- Демонстрационный граф знаний. -/
def atlas : KnowledgeGraph where
  objects := {cInfo, iUnc, sRes}
  relations := {rIU, rSI, rSC}
  unique_id := by decide
  src_closed := by decide
  tgt_closed := by decide

theorem atlas_ids : atlas.ids = {1, 2, 3} := by decide

/-- В демонстрационном графе каждый концепт определён ровно один раз. -/
theorem atlas_normalized : atlas.Normalized := by
  unfold KnowledgeGraph.Normalized
  decide

/-- Граф стратифицирован по номеру уровня, следовательно ацикличен. -/
theorem atlas_acyclic : atlas.Acyclic := by
  refine atlas.acyclic_of_rank id ?_
  rintro a b ⟨r, hr, -, rfl, rfl⟩
  fin_cases hr <;> decide

/-- CONCEPT-1 — фундамент: он ни от чего не зависит. -/
theorem atlas_foundation : ∀ b, ¬ atlas.Dep cInfo.id b := by
  rintro b ⟨r, hr, -, hs, -⟩
  fin_cases hr <;> simp_all [cInfo, rIU, rSI, rSC]

/-- Общая теорема о существовании фундамента применима к этому графу. -/
theorem atlas_exists_foundation : ∃ o ∈ atlas.objects, ∀ b, ¬ atlas.Dep o.id b :=
  atlas.exists_foundation atlas_acyclic ⟨cInfo, by decide⟩

/-- Аксиоматическое основание графа доказательств. -/
def atlasAx : Finset ℕ := {1}

/-- Доказанные утверждения. -/
def atlasPr : Finset ℕ := {2, 3}

theorem atlasAx_sub : atlasAx ⊆ atlas.ids := by decide

theorem atlasPr_sub : atlasPr ⊆ atlas.ids := by decide

theorem atlasAx_leaf : ∀ c ∈ atlasAx, atlas.premises c = ∅ := by decide

/-- Все объекты демонстрационного графа обоснованы: доказательства замкнуты
и трассируются к аксиоматическому основанию. -/
theorem atlas_all_grounded :
    ∀ o ∈ atlas.objects,
      (atlas.toProofGraph atlasAx atlasPr atlasAx_sub atlasPr_sub atlasAx_leaf).Grounded o.id :=
  atlas.all_grounded atlasAx atlasPr atlasAx_sub atlasPr_sub atlasAx_leaf atlas_acyclic
    (by decide)

end Demo
end Polymath
