import RequestProject.Agents

/-!
# Коллективное знание: слияние графов разных агентов

Уровни аудита v58 (многоагентные системы) и пункт 6 итогового приоритета
(масштабирование до коллективного уровня).

Знание нескольких агентов объединяется операцией `merge`. Слияние
определено при условии *совместимости*: объекты с одинаковым
идентификатором совпадают (иначе идентификатор перестаёт быть именем
знания). Доказано:

* слияние снова даёт корректный граф знаний и расширяет обе части;
* зависимости объединённого графа — в точности объединение зависимостей;
* конфликты («contradicts») не возникают из ниоткуда: любой конфликт
  объединённого графа уже присутствовал у одного из агентов;
* при общей стратификации объединённое знание остаётся ациклическим;
* знание, обоснованное у одного агента, остаётся обоснованным в общем
  графе доказательств.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

namespace KnowledgeGraph

/-- Графы совместимы, если одинаковый идентификатор означает одинаковый
объект: знание, разделяемое агентами, не расходится. -/
def Compatible (g₁ g₂ : KnowledgeGraph) : Prop :=
  ∀ a ∈ g₁.objects, ∀ b ∈ g₂.objects, a.id = b.id → a = b

theorem compatible_symm {g₁ g₂ : KnowledgeGraph} (h : Compatible g₁ g₂) : Compatible g₂ g₁ :=
  fun a ha b hb hab => (h b hb a ha hab.symm).symm

/-- Слияние знаний двух агентов. -/
def merge (g₁ g₂ : KnowledgeGraph) (h : Compatible g₁ g₂) : KnowledgeGraph where
  objects := g₁.objects ∪ g₂.objects
  relations := g₁.relations ∪ g₂.relations
  unique_id := by
    intro a ha b hb hab
    rcases Finset.mem_union.1 ha with ha' | ha' <;>
      rcases Finset.mem_union.1 hb with hb' | hb'
    · exact g₁.unique_id a ha' b hb' hab
    · exact h a ha' b hb' hab
    · exact (h b hb' a ha' hab.symm).symm
    · exact g₂.unique_id a ha' b hb' hab
  src_closed := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr' | hr'
    · obtain ⟨o, ho, hid⟩ := g₁.src_closed r hr'
      exact ⟨o, Finset.mem_union_left _ ho, hid⟩
    · obtain ⟨o, ho, hid⟩ := g₂.src_closed r hr'
      exact ⟨o, Finset.mem_union_right _ ho, hid⟩
  tgt_closed := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr' | hr'
    · obtain ⟨o, ho, hid⟩ := g₁.tgt_closed r hr'
      exact ⟨o, Finset.mem_union_left _ ho, hid⟩
    · obtain ⟨o, ho, hid⟩ := g₂.tgt_closed r hr'
      exact ⟨o, Finset.mem_union_right _ ho, hid⟩

variable {g₁ g₂ : KnowledgeGraph}

@[simp] theorem merge_objects (h : Compatible g₁ g₂) :
    (merge g₁ g₂ h).objects = g₁.objects ∪ g₂.objects := rfl

@[simp] theorem merge_relations (h : Compatible g₁ g₂) :
    (merge g₁ g₂ h).relations = g₁.relations ∪ g₂.relations := rfl

/-- Слияние расширяет знание первого агента. -/
theorem merge_extends_left (h : Compatible g₁ g₂) : Extends (merge g₁ g₂ h) g₁ :=
  ⟨Finset.subset_union_left, Finset.subset_union_left⟩

/-- Слияние расширяет знание второго агента. -/
theorem merge_extends_right (h : Compatible g₁ g₂) : Extends (merge g₁ g₂ h) g₂ :=
  ⟨Finset.subset_union_right, Finset.subset_union_right⟩

theorem merge_ids (h : Compatible g₁ g₂) : (merge g₁ g₂ h).ids = g₁.ids ∪ g₂.ids := by
  simp [ids, Finset.image_union]

/-- Зависимости коллективного знания — объединение зависимостей агентов. -/
theorem merge_dep (h : Compatible g₁ g₂) (a b : ℕ) :
    (merge g₁ g₂ h).Dep a b ↔ g₁.Dep a b ∨ g₂.Dep a b := by
  constructor
  · rintro ⟨r, hr, hstr, hsrc, htgt⟩
    rcases Finset.mem_union.1 hr with hr' | hr'
    · exact Or.inl ⟨r, hr', hstr, hsrc, htgt⟩
    · exact Or.inr ⟨r, hr', hstr, hsrc, htgt⟩
  · rintro (⟨r, hr, hstr, hsrc, htgt⟩ | ⟨r, hr, hstr, hsrc, htgt⟩)
    · exact ⟨r, Finset.mem_union_left _ hr, hstr, hsrc, htgt⟩
    · exact ⟨r, Finset.mem_union_right _ hr, hstr, hsrc, htgt⟩

/-- Слияние нормализовано, если оба графа нормализованы и не спорят об именах:
одно и то же имя одного и того же типа у обоих агентов означает один объект. -/
theorem merge_normalized (h : Compatible g₁ g₂) (h₁ : g₁.Normalized) (h₂ : g₂.Normalized)
    (hcross : ∀ a ∈ g₁.objects, ∀ b ∈ g₂.objects, a.kind = b.kind → a.label = b.label → a = b) :
    (merge g₁ g₂ h).Normalized := by
  intro a ha b hb hk hl
  rcases Finset.mem_union.1 ha with ha' | ha' <;>
    rcases Finset.mem_union.1 hb with hb' | hb'
  · exact h₁ a ha' b hb' hk hl
  · exact hcross a ha' b hb' hk hl
  · exact (hcross b hb' a ha' hk.symm hl.symm).symm
  · exact h₂ a ha' b hb' hk hl

/-- **Общая стратификация делает коллективное знание ациклическим.** Если оба
агента согласны с одной шкалой уровней, объединение их графов не содержит
циклов зависимостей. -/
theorem merge_acyclic_of_rank (h : Compatible g₁ g₂) (rank : ℕ → ℕ)
    (h₁ : ∀ a b, g₁.Dep a b → rank b < rank a)
    (h₂ : ∀ a b, g₂.Dep a b → rank b < rank a) :
    (merge g₁ g₂ h).Acyclic := by
  refine (merge g₁ g₂ h).acyclic_of_rank rank ?_
  intro a b hab
  rcases (merge_dep h a b).1 hab with hd | hd
  · exact h₁ a b hd
  · exact h₂ a b hd

/-! ### Конфликты знания -/

/-- Явный конфликт: заявленное противоречие между двумя объектами. -/
def Conflict (g : KnowledgeGraph) (i j : ℕ) : Prop :=
  ∃ r ∈ g.relations, r.kind = RelationKind.contradicts ∧ r.source = i ∧ r.target = j

/-- Граф непротиворечив, если явных конфликтов в нём нет. -/
def ConflictFree (g : KnowledgeGraph) : Prop := ∀ i j, ¬ g.Conflict i j

/-- **Конфликты не возникают из ниоткуда.** Любой конфликт объединённого
знания уже присутствовал у одного из агентов. -/
theorem merge_conflict (h : Compatible g₁ g₂) (i j : ℕ) :
    (merge g₁ g₂ h).Conflict i j ↔ g₁.Conflict i j ∨ g₂.Conflict i j := by
  constructor
  · rintro ⟨r, hr, hk, hs, ht⟩
    rcases Finset.mem_union.1 hr with hr' | hr'
    · exact Or.inl ⟨r, hr', hk, hs, ht⟩
    · exact Or.inr ⟨r, hr', hk, hs, ht⟩
  · rintro (⟨r, hr, hk, hs, ht⟩ | ⟨r, hr, hk, hs, ht⟩)
    · exact ⟨r, Finset.mem_union_left _ hr, hk, hs, ht⟩
    · exact ⟨r, Finset.mem_union_right _ hr, hk, hs, ht⟩

/-- Слияние непротиворечивых знаний непротиворечиво. -/
theorem merge_conflictFree (h : Compatible g₁ g₂) (h₁ : g₁.ConflictFree)
    (h₂ : g₂.ConflictFree) : (merge g₁ g₂ h).ConflictFree := by
  intro i j hc
  rcases (merge_conflict h i j).1 hc with hc' | hc'
  · exact h₁ i j hc'
  · exact h₂ i j hc'

/-- Корректность объектов сохраняется при слиянии. -/
theorem merge_allWellFormed (h : Compatible g₁ g₂) (h₁ : g₁.AllWellFormed)
    (h₂ : g₂.AllWellFormed) : (merge g₁ g₂ h).AllWellFormed := by
  intro o ho
  rcases Finset.mem_union.1 ho with ho' | ho'
  · exact h₁ o ho'
  · exact h₂ o ho'

end KnowledgeGraph

/-! ## Слияние графов доказательств -/

namespace ProofGraph

/-- Графы доказательств согласованы, если об общих утверждениях агенты
имеют одинаковое представление (одни и те же посылки). -/
def Agree (P₁ P₂ : ProofGraph) : Prop :=
  ∀ c ∈ P₁.claims, c ∈ P₂.claims → P₁.premises c = P₂.premises c

/-- Слияние графов доказательств двух агентов. -/
def merge (P₁ P₂ : ProofGraph) (h : Agree P₁ P₂) : ProofGraph where
  claims := P₁.claims ∪ P₂.claims
  axioms := P₁.axioms ∪ P₂.axioms
  proved := P₁.proved ∪ P₂.proved
  premises := fun c => if c ∈ P₁.claims then P₁.premises c else P₂.premises c
  axioms_subset := Finset.union_subset_union P₁.axioms_subset P₂.axioms_subset
  proved_subset := Finset.union_subset_union P₁.proved_subset P₂.proved_subset
  premises_subset := by
    intro c hc
    by_cases h₁ : c ∈ P₁.claims
    · simp only [if_pos h₁]
      exact (P₁.premises_subset c h₁).trans Finset.subset_union_left
    · simp only [if_neg h₁]
      have h₂ : c ∈ P₂.claims := by
        rcases Finset.mem_union.1 hc with hc' | hc'
        · exact absurd hc' h₁
        · exact hc'
      exact (P₂.premises_subset c h₂).trans Finset.subset_union_right
  premises_outside := by
    intro c hc
    have h₁ : c ∉ P₁.claims := fun hx => hc (Finset.mem_union_left _ hx)
    have h₂ : c ∉ P₂.claims := fun hx => hc (Finset.mem_union_right _ hx)
    simp only [if_neg h₁]
    exact P₂.premises_outside c h₂
  axioms_leaf := by
    intro c hc
    by_cases h₁ : c ∈ P₁.claims
    · simp only [if_pos h₁]
      rcases Finset.mem_union.1 hc with hc' | hc'
      · exact P₁.axioms_leaf c hc'
      · rw [h c h₁ (P₂.axioms_subset hc')]
        exact P₂.axioms_leaf c hc'
    · simp only [if_neg h₁]
      rcases Finset.mem_union.1 hc with hc' | hc'
      · exact absurd (P₁.axioms_subset hc') h₁
      · exact P₂.axioms_leaf c hc'

variable {P₁ P₂ : ProofGraph}

theorem merge_extends_left (h : Agree P₁ P₂) : Extends (merge P₁ P₂ h) P₁ := by
  refine ⟨Finset.subset_union_left, Finset.subset_union_left, Finset.subset_union_left, ?_⟩
  intro c hc
  simp only [merge, if_pos hc]

theorem merge_extends_right (h : Agree P₁ P₂) : Extends (merge P₁ P₂ h) P₂ := by
  refine ⟨Finset.subset_union_right, Finset.subset_union_right, Finset.subset_union_right, ?_⟩
  intro c hc
  by_cases h₁ : c ∈ P₁.claims
  · simp only [merge, if_pos h₁]
    exact h c h₁ hc
  · simp only [merge, if_neg h₁]

/-- **Коллективное знание не теряет обоснований.** Всё, что обосновано
у одного агента, обосновано и в объединённом графе доказательств. -/
theorem grounded_merge_left (h : Agree P₁ P₂) {c : ℕ} (hg : P₁.Grounded c) :
    (merge P₁ P₂ h).Grounded c :=
  P₁.grounded_mono (merge_extends_left h) hg

theorem grounded_merge_right (h : Agree P₁ P₂) {c : ℕ} (hg : P₂.Grounded c) :
    (merge P₁ P₂ h).Grounded c :=
  P₂.grounded_mono (merge_extends_right h) hg

end ProofGraph

end Polymath
