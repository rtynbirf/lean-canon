/-
# Мост OSA-3.2 → ядро модели знаний

Предложенная композиция операторов — это, с точки зрения ядра модели знаний
(`RequestProject.Core`), путь в графе знаний: каждый оператор становится
Knowledge Object вида `transformation`, а каждый стык `A → B` — структурной
связью `dependsOn`.

Здесь построен этот граф и доказано, что он корректен: ссылочная целостность
и уникальность идентификаторов выполняются по построению, все связи —
структурные, а слой зависимостей фундирован (что даёт право вести индукцию
по цепочке).
-/
import RequestProject.OSA.Theorems
import RequestProject.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

open Polymath

/-- Оператор как объект графа знаний.  Уверенность объекта — дополнение его
собственной суммарной неопределённости (в сотых долях). -/
def opObject (i : ℕ) (o : Operator) : KnowledgeObject where
  id := i
  kind := .transformation
  label := o.id
  maturity := .prototype
  confidence := 1 - (o.uncertainty.total : ℚ) / 100

/-- Объекты графа, порождённого цепочкой операторов. -/
def chainObjects (ops : List Operator) : Finset KnowledgeObject :=
  (Finset.range ops.length).image (fun i => opObject i (ops.getD i default))

/-- Связи графа: оператор с номером `i+1` зависит от оператора с номером `i`. -/
def chainRelations (ops : List Operator) : Finset KnowledgeRelation :=
  (Finset.range (ops.length - 1)).image
    (fun i => { source := i + 1, target := i, kind := .dependsOn, confidence := 1 })

/-- Граф знаний, отвечающий предложенной композиции. -/
def chainGraph (ops : List Operator) : KnowledgeGraph where
  objects := chainObjects ops
  relations := chainRelations ops
  unique_id := by
    intro a ha b hb hid
    simp only [chainObjects, Finset.mem_image, Finset.mem_range] at ha hb
    obtain ⟨i, _, rfl⟩ := ha
    obtain ⟨j, _, rfl⟩ := hb
    simp only [opObject] at hid
    subst hid
    rfl
  src_closed := by
    intro r hr
    simp only [chainRelations, Finset.mem_image, Finset.mem_range] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    refine ⟨opObject (i + 1) (ops.getD (i + 1) default), ?_, rfl⟩
    simp only [chainObjects, Finset.mem_image, Finset.mem_range]
    exact ⟨i + 1, by omega, rfl⟩
  tgt_closed := by
    intro r hr
    simp only [chainRelations, Finset.mem_image, Finset.mem_range] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    refine ⟨opObject i (ops.getD i default), ?_, rfl⟩
    simp only [chainObjects, Finset.mem_image, Finset.mem_range]
    exact ⟨i, by omega, rfl⟩

/-- Идентификаторы графа — в точности номера операторов цепочки. -/
theorem chainGraph_ids (ops : List Operator) :
    (chainGraph ops).ids = Finset.range ops.length := by
  ext i
  simp only [KnowledgeGraph.ids, chainGraph, chainObjects, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨o, ⟨j, hj, rfl⟩, rfl⟩
    exact hj
  · intro hi
    exact ⟨opObject i (ops.getD i default), ⟨i, hi, rfl⟩, rfl⟩

/-- Все связи, порождённые композицией, принадлежат структурному слою
(зависимости), а не причинному. -/
theorem chainGraph_relations_structural (ops : List Operator) :
    ∀ r ∈ (chainGraph ops).relations, r.kind.isStructural = true := by
  intro r hr
  simp only [chainGraph, chainRelations, Finset.mem_image, Finset.mem_range] at hr
  obtain ⟨i, _, rfl⟩ := hr
  rfl

/-- Каждый объект графа корректен, если суммарная собственная
неопределённость оператора не превышает 1.00 (то есть 100 сотых). -/
theorem chainGraph_objects_wellFormed (ops : List Operator)
    (h : ∀ o ∈ ops, o.uncertainty.total ≤ 100) :
    ∀ a ∈ (chainGraph ops).objects, a.WellFormed := by
  intro a ha
  simp only [chainGraph, chainObjects, Finset.mem_image, Finset.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  have hmem : ops.getD i default ∈ ops := by
    rw [List.getD_eq_getElem?_getD]
    have : ops[i]? = some ops[i] := List.getElem?_eq_getElem hi
    rw [this]
    exact List.getElem_mem hi
  have hle : ((ops.getD i default).uncertainty.total : ℚ) ≤ 100 := by
    exact_mod_cast h _ hmem
  have hnn : (0 : ℚ) ≤ ((ops.getD i default).uncertainty.total : ℚ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · simp only [opObject]
    linarith
  · simp only [opObject]
    linarith
  · intro hax
    simp only [opObject] at hax
    exact absurd hax (by decide)

/-- Отношение зависимости, порождённое цепочкой: `i+1` зависит от `i`. -/
def chainDep (ops : List Operator) (a b : ℕ) : Prop :=
  a + 1 = b ∧ b < ops.length

theorem chainDep_lt {ops : List Operator} {a b : ℕ}
    (h : Relation.TransGen (chainDep ops) a b) : a < b := by
  induction h with
  | single hab => obtain ⟨h1, _⟩ := hab; omega
  | tail _ hbc ih => obtain ⟨h1, _⟩ := hbc; omega

/-- **Фундированность слоя зависимостей.**  Спуск по зависимостям цепочки
операторов фундирован, поэтому по композиции законна индукция. -/
theorem chainDep_wellFounded (ops : List Operator) :
    WellFounded (fun b a => chainDep ops a b) := by
  refine wellFounded_flip_of_acyclic (s := Finset.range (ops.length + 1)) ?_ ?_
  · intro a b hab
    obtain ⟨hab, hb⟩ := hab
    exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  · intro a hcyc
    exact absurd (chainDep_lt hcyc) (lt_irrefl a)

end Polymath.OSA
