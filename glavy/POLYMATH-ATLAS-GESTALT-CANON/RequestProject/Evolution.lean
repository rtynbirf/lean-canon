import RequestProject.ProofGraph

/-!
# Эволюция модели знаний: версии, дельты, монотонный рост

Слой, отвечающий за пункт аудита «нет версии модели» и за уровень v11
(эволюция знания). Формализованы элементарные операции роста графа знаний
(добавление объекта, добавление связи), понятие расширения графа
(`Extends`) и доказано, что рост знания:

* сохраняет ссылочную целостность (по построению — результат снова `KnowledgeGraph`);
* сохраняет нормализованность при добавлении нового концепта;
* не создаёт циклов, если новая связь не замыкает существующий путь;
* никогда не разрушает уже установленную обоснованность (`grounded_mono`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

/-! ## Общая лемма: добавление одного ребра к отношению -/

/-- Разбор пути в отношении, к которому добавлено одно ребро `a → b`:
либо путь не использует новое ребро, либо он проходит через него. -/
theorem transGen_insert_edge {α : Type*} {R : α → α → Prop} {a b x y : α}
    (h : Relation.TransGen (fun u v => R u v ∨ (u = a ∧ v = b)) x y) :
    Relation.TransGen R x y ∨
      (Relation.ReflTransGen R x a ∧ Relation.ReflTransGen R b y) := by
  induction h with
  | @single y hxy =>
    rcases hxy with hR | ⟨rfl, rfl⟩
    · exact Or.inl (Relation.TransGen.single hR)
    · exact Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @tail c y _ hlast ih =>
    rcases ih with hxc | ⟨hxa, hbc⟩
    · rcases hlast with hR | ⟨rfl, rfl⟩
      · exact Or.inl (hxc.tail hR)
      · exact Or.inr ⟨hxc.to_reflTransGen, Relation.ReflTransGen.refl⟩
    · rcases hlast with hR | ⟨rfl, rfl⟩
      · exact Or.inr ⟨hxa, hbc.tail hR⟩
      · exact Or.inr ⟨hxa, Relation.ReflTransGen.refl⟩

/-- **Добавление ребра не создаёт цикла**, если из его цели нельзя вернуться
в его источник. Формальное основание безопасного роста графа знаний. -/
theorem acyclic_insert_edge {α : Type*} {R : α → α → Prop} {a b : α}
    (hac : ∀ x, ¬ Relation.TransGen R x x)
    (hba : ¬ Relation.ReflTransGen R b a) :
    ∀ x, ¬ Relation.TransGen (fun u v => R u v ∨ (u = a ∧ v = b)) x x := by
  intro x hx
  rcases transGen_insert_edge hx with hcyc | ⟨hxa, hbx⟩
  · exact hac x hcyc
  · exact hba (hbx.trans hxa)

namespace KnowledgeGraph

variable (g : KnowledgeGraph)

/-! ## Элементарные операции роста -/

/-- Добавление нового объекта знания (с ещё не занятым идентификатором). -/
def addObject (o : KnowledgeObject) (h : o.id ∉ g.ids) : KnowledgeGraph where
  objects := insert o g.objects
  relations := g.relations
  unique_id := by
    intro a ha b hb hab
    have hid : ∀ c ∈ g.objects, c.id ≠ o.id := by
      intro c hc hcid
      exact h ((g.mem_ids_iff o.id).2 ⟨c, hc, hcid⟩)
    rcases Finset.mem_insert.1 ha with rfl | ha'
    · rcases Finset.mem_insert.1 hb with rfl | hb'
      · rfl
      · exact absurd hab.symm (hid b hb')
    · rcases Finset.mem_insert.1 hb with rfl | hb'
      · exact absurd hab (hid a ha')
      · exact g.unique_id a ha' b hb' hab
  src_closed := by
    intro r hr
    obtain ⟨o', ho', hid⟩ := g.src_closed r hr
    exact ⟨o', Finset.mem_insert_of_mem ho', hid⟩
  tgt_closed := by
    intro r hr
    obtain ⟨o', ho', hid⟩ := g.tgt_closed r hr
    exact ⟨o', Finset.mem_insert_of_mem ho', hid⟩

/-- Добавление связи между уже существующими объектами. -/
def addRelation (r : KnowledgeRelation) (hs : r.source ∈ g.ids) (ht : r.target ∈ g.ids) : KnowledgeGraph where
  objects := g.objects
  relations := insert r g.relations
  unique_id := g.unique_id
  src_closed := by
    intro r' hr'
    rcases Finset.mem_insert.1 hr' with rfl | hr'
    · exact (g.mem_ids_iff r'.source).1 hs
    · exact g.src_closed r' hr'
  tgt_closed := by
    intro r' hr'
    rcases Finset.mem_insert.1 hr' with rfl | hr'
    · exact (g.mem_ids_iff r'.target).1 ht
    · exact g.tgt_closed r' hr'

@[simp] theorem addObj_objects (o : KnowledgeObject) (h : o.id ∉ g.ids) :
    (g.addObject o h).objects = insert o g.objects := rfl

@[simp] theorem addObj_relations (o : KnowledgeObject) (h : o.id ∉ g.ids) :
    (g.addObject o h).relations = g.relations := rfl

@[simp] theorem addRel_objects (r : KnowledgeRelation) (hs : r.source ∈ g.ids) (ht : r.target ∈ g.ids) :
    (g.addRelation r hs ht).objects = g.objects := rfl

@[simp] theorem addRel_relations (r : KnowledgeRelation) (hs : r.source ∈ g.ids) (ht : r.target ∈ g.ids) :
    (g.addRelation r hs ht).relations = insert r g.relations := rfl

theorem addObj_ids (o : KnowledgeObject) (h : o.id ∉ g.ids) :
    (g.addObject o h).ids = insert o.id g.ids := by
  simp [ids, addObject]

theorem addRel_ids (r : KnowledgeRelation) (hs : r.source ∈ g.ids) (ht : r.target ∈ g.ids) :
    (g.addRelation r hs ht).ids = g.ids := rfl

/-- Добавление объекта не меняет слой зависимостей. -/
theorem addObj_dep (o : KnowledgeObject) (h : o.id ∉ g.ids) (a b : ℕ) :
    (g.addObject o h).Dep a b ↔ g.Dep a b := Iff.rfl

/-- Добавление объекта сохраняет ацикличность. -/
theorem addObj_acyclic (o : KnowledgeObject) (h : o.id ∉ g.ids) (hac : g.Acyclic) :
    (g.addObject o h).Acyclic := hac

/-- Добавление нового концепта сохраняет нормализованность,
если такого концепта (тип + имя) в графе ещё не было. -/
theorem addObj_normalized (o : KnowledgeObject) (h : o.id ∉ g.ids) (hn : g.Normalized)
    (hfresh : ∀ a ∈ g.objects, a.kind = o.kind → a.label ≠ o.label) :
    (g.addObject o h).Normalized := by
  intro a ha b hb hk hl
  rcases Finset.mem_insert.1 ha with rfl | ha' <;>
    rcases Finset.mem_insert.1 hb with rfl | hb'
  · rfl
  · exact absurd hl.symm (hfresh b hb' hk.symm)
  · exact absurd hl (hfresh a ha' hk)
  · exact hn a ha' b hb' hk hl

/-- Добавление связи не меняет множество объектов, поэтому сохраняет
нормализованность. -/
theorem addRel_normalized (r : KnowledgeRelation) (hs : r.source ∈ g.ids) (ht : r.target ∈ g.ids)
    (hn : g.Normalized) : (g.addRelation r hs ht).Normalized := hn

/-- Зависимости расширенного графа — это старые зависимости плюс, возможно,
одна новая. -/
theorem addRel_dep (r : KnowledgeRelation) (hs : r.source ∈ g.ids) (ht : r.target ∈ g.ids) (a b : ℕ) :
    (g.addRelation r hs ht).Dep a b ↔
      g.Dep a b ∨ (r.kind.isStructural = true ∧ r.source = a ∧ r.target = b) := by
  constructor
  · rintro ⟨r', hr', hstr, hsrc, htgt⟩
    rcases Finset.mem_insert.1 hr' with rfl | hr'
    · exact Or.inr ⟨hstr, hsrc, htgt⟩
    · exact Or.inl ⟨r', hr', hstr, hsrc, htgt⟩
  · rintro (⟨r', hr', hstr, hsrc, htgt⟩ | ⟨hstr, hsrc, htgt⟩)
    · exact ⟨r', Finset.mem_insert_of_mem hr', hstr, hsrc, htgt⟩
    · exact ⟨r, Finset.mem_insert_self _ _, hstr, hsrc, htgt⟩

/-- **Безопасный рост графа знаний.** Добавление связи к ациклическому графу
снова даёт ациклический граф, если из цели связи нельзя (по зависимостям)
добраться до её источника. -/
theorem addRel_acyclic (r : KnowledgeRelation) (hs : r.source ∈ g.ids) (ht : r.target ∈ g.ids)
    (hac : g.Acyclic)
    (hno : ¬ Relation.ReflTransGen g.Dep r.target r.source) :
    (g.addRelation r hs ht).Acyclic := by
  intro x hx
  have hmono : ∀ u v, (g.addRelation r hs ht).Dep u v →
      (g.Dep u v ∨ (u = r.source ∧ v = r.target)) := by
    intro u v huv
    rcases (g.addRel_dep r hs ht u v).1 huv with h | ⟨-, hsrc, htgt⟩
    · exact Or.inl h
    · exact Or.inr ⟨hsrc.symm, htgt.symm⟩
  have hx' : Relation.TransGen (fun u v => g.Dep u v ∨ (u = r.source ∧ v = r.target)) x x :=
    Relation.TransGen.mono hmono hx
  exact acyclic_insert_edge (R := g.Dep) hac hno x hx'

/-! ## Версии модели и монотонность знания -/

/-- Граф `g'` — версия, расширяющая `g`: все объекты и связи сохранены. -/
def Extends (g' g : KnowledgeGraph) : Prop :=
  g.objects ⊆ g'.objects ∧ g.relations ⊆ g'.relations

theorem extends_refl : Extends g g := ⟨subset_rfl, subset_rfl⟩

theorem extends_trans {g₁ g₂ g₃ : KnowledgeGraph} (h₁ : Extends g₂ g₁) (h₂ : Extends g₃ g₂) :
    Extends g₃ g₁ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem addObj_extends (o : KnowledgeObject) (h : o.id ∉ g.ids) : Extends (g.addObject o h) g :=
  ⟨Finset.subset_insert _ _, subset_rfl⟩

theorem addRel_extends (r : KnowledgeRelation) (hs : r.source ∈ g.ids) (ht : r.target ∈ g.ids) :
    Extends (g.addRelation r hs ht) g :=
  ⟨subset_rfl, Finset.subset_insert _ _⟩

/-- Идентификаторы никогда не теряются при переходе к новой версии. -/
theorem ids_subset_of_extends {g' : KnowledgeGraph} (h : Extends g' g) : g.ids ⊆ g'.ids := by
  intro i hi
  obtain ⟨o, ho, hid⟩ := (g.mem_ids_iff i).1 hi
  exact (g'.mem_ids_iff i).2 ⟨o, h.1 ho, hid⟩

/-- Зависимости сохраняются при расширении версии. -/
theorem dep_of_extends {g' : KnowledgeGraph} (h : Extends g' g) {a b : ℕ} (hd : g.Dep a b) :
    g'.Dep a b := by
  obtain ⟨r, hr, hstr, hsrc, htgt⟩ := hd
  exact ⟨r, h.2 hr, hstr, hsrc, htgt⟩

/-- И достижимость по зависимостям тоже. -/
theorem reaches_of_extends {g' : KnowledgeGraph} (h : Extends g' g) {a b : ℕ} (hr : g.Reaches a b) :
    g'.Reaches a b :=
  Relation.TransGen.mono (fun _ _ hd => dep_of_extends g h hd) hr

/-- Ацикличность новой версии влечёт ацикличность старой: рост знания может
только «обнаружить» цикл, но не спрятать его. -/
theorem acyclic_of_extends {g' : KnowledgeGraph} (h : Extends g' g) (hac : g'.Acyclic) : g.Acyclic :=
  fun a hcyc => hac a (reaches_of_extends g h hcyc)

end KnowledgeGraph

/-! ## Монотонность обоснованности в графе доказательств -/

namespace ProofGraph

/-- `P'` — расширение графа доказательств `P`: новые утверждения, аксиомы и
доказательства добавляются, а посылки старых утверждений не меняются. -/
def Extends (P' P : ProofGraph) : Prop :=
  P.claims ⊆ P'.claims ∧ P.axioms ⊆ P'.axioms ∧ P.proved ⊆ P'.proved ∧
    ∀ c ∈ P.claims, P'.premises c = P.premises c

variable (P : ProofGraph)

theorem pextends_refl : Extends P P :=
  ⟨subset_rfl, subset_rfl, subset_rfl, fun _ _ => rfl⟩

theorem pextends_trans {P₁ P₂ P₃ : ProofGraph} (h₁ : Extends P₂ P₁) (h₂ : Extends P₃ P₂) :
    Extends P₃ P₁ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    fun c hc => by rw [h₂.2.2.2 c (h₁.1 hc), h₁.2.2.2 c hc]⟩

/-- **Знание не обесценивается.** Всё, что было обосновано в старой версии,
остаётся обоснованным в любой расширяющей версии. -/
theorem grounded_mono {P' : ProofGraph} (h : Extends P' P) {c : ℕ} (hg : P.Grounded c) :
    P'.Grounded c := by
  induction hg with
  | @ax c hc => exact Grounded.ax (h.2.1 hc)
  | @inf c hc _ ih =>
    refine Grounded.inf (h.2.2.1 hc) ?_
    intro p hp
    have hcc : c ∈ P.claims := P.proved_subset hc
    rw [h.2.2.2 c hcc] at hp
    exact ih p hp

end ProofGraph

end Polymath
