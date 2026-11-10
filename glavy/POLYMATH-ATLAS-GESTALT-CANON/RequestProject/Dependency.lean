import RequestProject.Core

/-!
# Слой зависимостей графа знаний

Структурные связи (`uses`, `depends_on`, `builds_on`) образуют отдельный
слой — граф зависимостей. Здесь доказаны его ключевые свойства:

* фундированность спуска по зависимостям в ациклическом графе;
* существование «фундамента» — объекта без исходящих зависимостей
  (аксиоматического основания) в любом непустом ациклическом графе;
* принцип индукции по зависимостям;
* корректность множества `Impact` (обратная трассировка: что сломается
  при удалении объекта).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

namespace KnowledgeGraph

variable (g : KnowledgeGraph)

/-! ## Отношение зависимости -/

/-- `g.Dep a b` — объект `a` структурно зависит от объекта `b`. -/
def Dep (a b : ℕ) : Prop :=
  ∃ r ∈ g.relations, r.kind.isStructural = true ∧ r.source = a ∧ r.target = b

/-- Непосредственные предпосылки объекта как конечное множество. -/
def premises (a : ℕ) : Finset ℕ :=
  (g.relations.filter (fun r => r.kind.isStructural = true ∧ r.source = a)).image KnowledgeRelation.target

theorem mem_premises_iff (a b : ℕ) : b ∈ g.premises a ↔ g.Dep a b := by
  classical
  simp only [premises, Finset.mem_image, Finset.mem_filter, Dep]
  constructor
  · rintro ⟨r, ⟨hr, hs, hsrc⟩, htgt⟩
    exact ⟨r, hr, hs, hsrc, htgt⟩
  · rintro ⟨r, hr, hs, hsrc, htgt⟩
    exact ⟨r, ⟨hr, hs, hsrc⟩, htgt⟩

/-- Зависимость всегда связывает объекты, реально присутствующие в графе. -/
theorem dep_support {a b : ℕ} (h : g.Dep a b) : a ∈ g.ids ∧ b ∈ g.ids := by
  obtain ⟨r, hr, -, hsrc, htgt⟩ := h
  exact ⟨hsrc ▸ g.src_mem_ids hr, htgt ▸ g.tgt_mem_ids hr⟩

/-- Транзитивное замыкание зависимости: `a` (косвенно) опирается на `b`. -/
def Reaches (a b : ℕ) : Prop := Relation.TransGen g.Dep a b

theorem reaches_of_dep {a b : ℕ} (h : g.Dep a b) : g.Reaches a b :=
  Relation.TransGen.single h

theorem Reaches.trans {a b c : ℕ} (h₁ : g.Reaches a b) (h₂ : g.Reaches b c) : g.Reaches a c :=
  Relation.TransGen.trans h₁ h₂

/-- Граф зависимостей ацикличен: ни один объект не опирается сам на себя. -/
def Acyclic : Prop := ∀ a, ¬ g.Reaches a a

/-! ## Фундированность и фундамент -/

/-- **Фундированность.** В ациклическом графе знаний спуск по зависимостям
обрывается: бесконечных цепочек «зависит от» не существует. -/
theorem wf_dep (hac : g.Acyclic) : WellFounded (fun b a => g.Dep a b) :=
  wellFounded_flip_of_acyclic (s := g.ids) (fun _ _ h => g.dep_support h) hac

/-- **Принцип индукции по зависимостям.** Свойство, наследуемое от всех
предпосылок объекта, выполняется для всех объектов графа. -/
theorem dep_induction (hac : g.Acyclic) {P : ℕ → Prop}
    (h : ∀ a, (∀ b, g.Dep a b → P b) → P a) : ∀ a, P a :=
  fun a => (g.wf_dep hac).induction a (fun x ih => h x (fun b hb => ih b hb))

/-- **Существование фундамента.** Любой непустой ациклический граф знаний
содержит объект без исходящих структурных зависимостей — аксиоматическое
основание, на которое опирается всё остальное. -/
theorem exists_foundation (hac : g.Acyclic) (hne : g.objects.Nonempty) :
    ∃ o ∈ g.objects, ∀ b, ¬ g.Dep o.id b := by
  classical
  have hids : (↑g.ids : Set ℕ).Nonempty := by
    obtain ⟨o, ho⟩ := hne
    exact ⟨o.id, by simpa using (g.mem_ids_iff o.id).2 ⟨o, ho, rfl⟩⟩
  obtain ⟨i, hi, hmin⟩ := (g.wf_dep hac).has_min (↑g.ids : Set ℕ) hids
  obtain ⟨o, ho, hoid⟩ := (g.mem_ids_iff i).1 (by simpa using hi)
  refine ⟨o, ho, ?_⟩
  intro b hb
  rw [hoid] at hb
  exact hmin b (by simpa using (g.dep_support hb).2) hb

/-- В ациклическом графе объект не может быть собственной предпосылкой. -/
theorem not_dep_self (hac : g.Acyclic) (a : ℕ) : ¬ g.Dep a a :=
  fun h => hac a (g.reaches_of_dep h)

/-! ## Стратификация: уровни как критерий ацикличности -/

/-- Если каждая зависимость строго понижает уровень объекта, то уровень
строго понижается вдоль всей цепочки зависимостей. -/
theorem rank_lt_of_reaches (rank : ℕ → ℕ) (h : ∀ a b, g.Dep a b → rank b < rank a)
    {a b : ℕ} (hr : g.Reaches a b) : rank b < rank a := by
  induction hr with
  | single hab => exact h _ _ hab
  | tail _ hlast ih => exact lt_trans (h _ _ hlast) ih

/-- **Критерий ацикличности.** Стратифицированный граф знаний (каждая
зависимость ведёт на строго более низкий уровень) ацикличен. -/
theorem acyclic_of_rank (rank : ℕ → ℕ) (h : ∀ a b, g.Dep a b → rank b < rank a) :
    g.Acyclic :=
  fun a hcyc => lt_irrefl (rank a) (g.rank_lt_of_reaches rank h hcyc)

/-- Уровень (глубина) объекта в ациклическом графе знаний: на единицу
больше максимума уровней его предпосылок. -/
noncomputable def level (hac : g.Acyclic) : ℕ → ℕ :=
  (g.wf_dep hac).fix
    (fun a rec => ((g.premises a).attach.sup
      (fun p => rec p.1 ((g.mem_premises_iff a p.1).1 p.2))) + 1)

theorem level_eq (hac : g.Acyclic) (a : ℕ) :
    g.level hac a =
      ((g.premises a).attach.sup (fun p => g.level hac p.1)) + 1 := by
  rw [level, WellFounded.fix_eq]

/-- **Стратификация.** Каждая зависимость строго понижает уровень. -/
theorem level_lt_of_dep (hac : g.Acyclic) {a b : ℕ} (h : g.Dep a b) :
    g.level hac b < g.level hac a := by
  have hb : b ∈ g.premises a := (g.mem_premises_iff a b).2 h
  have hle : g.level hac b ≤ (g.premises a).attach.sup (fun p => g.level hac p.1) :=
    Finset.le_sup (f := fun p : {x // x ∈ g.premises a} => g.level hac p.1)
      (Finset.mem_attach _ ⟨b, hb⟩)
  rw [g.level_eq hac a]
  exact Nat.lt_succ_of_le hle

/-- **Критерий ацикличности в обе стороны.** Граф знаний ацикличен тогда
и только тогда, когда его можно разложить по уровням. Сортировка по уровню
даёт корректную траекторию изучения: любая предпосылка изучается раньше. -/
theorem acyclic_iff_stratifiable :
    g.Acyclic ↔ ∃ rank : ℕ → ℕ, ∀ a b, g.Dep a b → rank b < rank a := by
  constructor
  · intro hac
    exact ⟨g.level hac, fun _ _ h => g.level_lt_of_dep hac h⟩
  · rintro ⟨rank, hrank⟩
    exact g.acyclic_of_rank rank hrank

/-! ## Impact: обратная трассировка -/

/-- `g.Impact i` — множество объектов, (косвенно) опирающихся на `i`.
Это в точности то, что сломается при удалении объекта `i`. -/
def Impact (i : ℕ) : Set ℕ := {a | g.Reaches a i}

theorem mem_impact_of_dep {a i : ℕ} (h : g.Dep a i) : a ∈ g.Impact i :=
  g.reaches_of_dep h

/-- Impact монотонен вдоль зависимостей: если `a` зависит от `b`,
то всё, что зависит от `a`, зависит и от `b`. -/
theorem impact_subset_of_dep {a b : ℕ} (h : g.Dep a b) : g.Impact a ⊆ g.Impact b :=
  fun _ hx => Relation.TransGen.trans (hx : g.Reaches _ a) (g.reaches_of_dep h)

/-- Пустой Impact означает, что объект ни для кого не является предпосылкой. -/
theorem impact_eq_empty_iff (i : ℕ) : g.Impact i = ∅ ↔ ∀ a, ¬ g.Reaches a i := by
  constructor
  · intro h a ha
    have : a ∈ g.Impact i := ha
    rw [h] at this
    exact this
  · intro h
    ext a
    simp [Impact, h a]

/-- **Критерий безопасного удаления.** Если объект имеет пустой Impact и сам
ни от чего не зависит, то в графе нет ни одной инцидентной ему связи, и его
удаление не затрагивает связи графа. -/
theorem eraseObj_relations_eq_of_no_impact {o : KnowledgeObject}
    (hin : g.Impact o.id = ∅) (hout : ∀ b, ¬ g.Dep o.id b)
    (hstruct : ∀ r ∈ g.relations, r.kind.isStructural = true) :
    (g.eraseObj o).relations = g.relations := by
  refine g.eraseObj_relations_eq_of_isolated o ?_
  intro r hr
  constructor
  · intro hsrc
    exact hout r.target ⟨r, hr, hstruct r hr, hsrc, rfl⟩
  · intro htgt
    have : r.source ∈ g.Impact o.id :=
      g.mem_impact_of_dep (a := r.source) ⟨r, hr, hstruct r hr, rfl, htgt⟩
    rw [hin] at this
    exact this

end KnowledgeGraph

end Polymath
