import RequestProject.Curriculum
import RequestProject.ProofGraph
import RequestProject.Atlas.Canon.L0L42

/-!
# Мост: шкала `L0–L42` как граф знаний

Сорок три уровня канона `L0–L42` (архивный слой
`RequestProject.Atlas.Canon.L0L42`) представлены как Knowledge Objects
модели знаний, а «каждый следующий уровень отрицает инвариант предыдущего» —
как структурная связь `buildsOn`.

Доказано, что получающийся граф знаний корректен, нормализован (имена
уровней попарно различны — `Canon.L0L42.law_of_unique_name`), ацикличен,
имеет явную траекторию изучения `L0 → L1 → … → L42` и полностью обоснован
как граф доказательств с уровнем `L0` в основании.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath
namespace AtlasLadder

open Canon.L0L42

/-- Имя уровня с номером `n` (пустая строка вне шкалы). -/
def levelName (n : ℕ) : String := ((levels[n]?).map Level.name).getD ""

/-- Knowledge Object уровня `Ln`: идентификатор `n + 1`, метка — имя уровня. -/
def ladderObj (n : ℕ) : KnowledgeObject :=
  { id := n + 1
    kind := ObjectKind.concept
    label := levelName n
    maturity := Maturity.canonical
    confidence := 1 }

/-- Связь «уровень `n+1` строится на уровне `n`». -/
def ladderRel (n : ℕ) : KnowledgeRelation :=
  { source := n + 2, target := n + 1, kind := RelationKind.buildsOn, confidence := 1 }

/-- Граф знаний всей шкалы `L0–L42`. -/
def ladder : KnowledgeGraph where
  objects := (Finset.range 43).image ladderObj
  relations := (Finset.range 42).image ladderRel
  unique_id := by
    intro a ha b hb hab
    simp only [Finset.mem_image, Finset.mem_range] at ha hb
    obtain ⟨n, -, rfl⟩ := ha
    obtain ⟨m, -, rfl⟩ := hb
    have : n = m := by simpa [ladderObj] using hab
    rw [this]
  src_closed := by
    intro r hr
    simp only [Finset.mem_image, Finset.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    refine ⟨ladderObj (k + 1), ?_, rfl⟩
    exact Finset.mem_image.2 ⟨k + 1, Finset.mem_range.2 (by omega), rfl⟩
  tgt_closed := by
    intro r hr
    simp only [Finset.mem_image, Finset.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    refine ⟨ladderObj k, ?_, rfl⟩
    exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩

theorem ladder_ids : ladder.ids = (Finset.range 43).image (fun n => n + 1) := by
  simp only [KnowledgeGraph.ids, ladder, Finset.image_image]
  rfl

/-- Все объекты шкалы корректны. -/
theorem ladder_wellFormed : ∀ o ∈ ladder.objects, o.WellFormed := by
  intro o ho
  simp only [ladder, Finset.mem_image, Finset.mem_range] at ho
  obtain ⟨n, -, rfl⟩ := ho
  exact ⟨by norm_num [ladderObj], by norm_num [ladderObj], fun _ => by norm_num [ladderObj]⟩

/-- Имена уровней попарно различны в пределах шкалы. -/
theorem levelName_injOn :
    ∀ n < 43, ∀ m < 43, levelName n = levelName m → n = m := by
  decide

/-- Шкала нормализована: каждый уровень существует ровно один раз. -/
theorem ladder_normalized : ladder.Normalized := by
  intro a ha b hb _ hl
  simp only [ladder, Finset.mem_image, Finset.mem_range] at ha hb
  obtain ⟨n, hn, rfl⟩ := ha
  obtain ⟨m, hm, rfl⟩ := hb
  have : n = m := levelName_injOn n hn m hm (by simpa [ladderObj] using hl)
  rw [this]

/-- Шкала ациклична: зависимости строго убывают по номеру уровня. -/
theorem ladder_acyclic : ladder.Acyclic := by
  refine ladder.acyclic_of_rank id ?_
  rintro a b ⟨r, hr, -, rfl, rfl⟩
  simp only [ladder, Finset.mem_image, Finset.mem_range] at hr
  obtain ⟨k, -, rfl⟩ := hr
  simp [ladderRel]

/-- Уровень `L0` — фундамент шкалы. -/
theorem ladder_foundation : ∀ b, ¬ ladder.Dep (ladderObj 0).id b := by
  rintro b ⟨r, hr, -, hs, -⟩
  simp only [ladder, Finset.mem_image, Finset.mem_range] at hr
  obtain ⟨k, -, rfl⟩ := hr
  simp [ladderObj, ladderRel] at hs

/-- Явная траектория изучения шкалы: уровни изучаются по возрастанию номера. -/
theorem ladder_curriculum : ladder.Curriculum ((List.range 43).map (fun n => n + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [ladder_ids]
    simp
  · exact (List.nodup_range).map (fun _ _ h => by omega)
  · rintro a b ⟨r, hr, -, rfl, rfl⟩
    simp only [ladder, Finset.mem_image, Finset.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    have key : ∀ n < 43, ((List.range 43).map (fun n => n + 1)).idxOf (n + 1) = n := by
      decide
    have h1 : ((List.range 43).map (fun n => n + 1)).idxOf (k + 2) = k + 1 := by
      have := key (k + 1) (by omega)
      simpa [Nat.add_assoc] using this
    have h2 : ((List.range 43).map (fun n => n + 1)).idxOf (k + 1) = k := key k (by omega)
    simp only [ladderRel]
    rw [h1, h2]
    omega

/-- Общая теорема о существовании траектории применима к шкале. -/
theorem ladder_exists_curriculum : ∃ l, ladder.Curriculum l :=
  ladder.exists_curriculum ladder_acyclic

/-! ## Шкала как граф доказательств -/

/-- Основание: уровень `L0`. -/
def ladderAx : Finset ℕ := {1}

/-- Выводимые уровни: `L1 … L42`. -/
def ladderPr : Finset ℕ := (Finset.range 42).image (fun n => n + 2)

theorem ladderAx_sub : ladderAx ⊆ ladder.ids := by
  intro i hi
  rw [ladder_ids]
  simp only [ladderAx, Finset.mem_singleton] at hi
  subst hi
  exact Finset.mem_image.2 ⟨0, by simp⟩

theorem ladderPr_sub : ladderPr ⊆ ladder.ids := by
  intro i hi
  rw [ladder_ids]
  simp only [ladderPr, Finset.mem_image, Finset.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  exact Finset.mem_image.2 ⟨k + 1, Finset.mem_range.2 (by omega), by omega⟩

theorem ladderAx_leaf : ∀ c ∈ ladderAx, ladder.premises c = ∅ := by
  intro c hc
  simp only [ladderAx, Finset.mem_singleton] at hc
  subst hc
  refine Finset.eq_empty_of_forall_notMem ?_
  intro b hb
  rw [KnowledgeGraph.mem_premises_iff] at hb
  obtain ⟨r, hr, -, hs, -⟩ := hb
  simp only [ladder, Finset.mem_image, Finset.mem_range] at hr
  obtain ⟨k, -, rfl⟩ := hr
  simp [ladderRel] at hs

/-- Каждый уровень шкалы обоснован и трассируется к `L0`. -/
theorem ladder_all_grounded :
    ∀ o ∈ ladder.objects,
      (ladder.toProofGraph ladderAx ladderPr ladderAx_sub ladderPr_sub
        ladderAx_leaf).Grounded o.id := by
  refine ladder.all_grounded ladderAx ladderPr ladderAx_sub ladderPr_sub ladderAx_leaf
    ladder_acyclic ?_
  intro i hi
  rw [ladder_ids] at hi
  simp only [Finset.mem_image, Finset.mem_range] at hi
  obtain ⟨n, hn, rfl⟩ := hi
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · left
    simp [ladderAx]
  · right
    refine Finset.mem_image.2 ⟨n - 1, Finset.mem_range.2 (by omega), by omega⟩

end AtlasLadder
end Polymath
