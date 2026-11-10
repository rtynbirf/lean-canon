import RequestProject.Dependency

/-!
# Дедупликация: приведение графа знаний к нормальной форме

Одна из главных находок аудита — дублирование знания: один и тот же концепт
заводится несколько раз под разными идентификаторами. Предикат
`KnowledgeGraph.Normalized` («один концепт существует ровно один раз») описывает
желаемое состояние; здесь строится **операция**, приводящая граф к этому
состоянию, и доказывается её корректность.

Дедупликация задаётся выбором канонического представителя: функцией
`f : KnowledgeObject → KnowledgeObject` (какой объект считать каноническим для данного класса
дубликатов) и согласованным с ней переименованием идентификаторов
`fid : ℕ → ℕ`. Условия на выбор представителя собраны в структуре
`KnowledgeGraph.CanonChoice`.

Доказано, что результат дедупликации `KnowledgeGraph.dedup`:

* снова является корректным графом знаний (ссылочная целостность
  сохраняется — ни одна связь не «повисает»);
* **нормализован**: пара «тип + имя» определяет объект однозначно;
* не увеличивает объём графа;
* сохраняет все зависимости (в переименованном виде) и не создаёт новых
  зависимостей «из ниоткуда»;
* остаётся ациклическим, если слияние дубликатов согласовано с уровнями;
* **идемпотентен**: уже нормализованный граф дедупликация не меняет.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

namespace KnowledgeGraph

variable (g : KnowledgeGraph)

/-- Выбор канонического представителя класса дубликатов: функция `f`
на объектах и согласованное с ней переименование идентификаторов `fid`. -/
structure CanonChoice (g : KnowledgeGraph) where
  /-- Канонический представитель объекта. -/
  f : KnowledgeObject → KnowledgeObject
  /-- Переименование идентификаторов. -/
  fid : ℕ → ℕ
  /-- Представитель — объект того же графа. -/
  mem : ∀ o ∈ g.objects, f o ∈ g.objects
  /-- Переименование согласовано с выбором представителя. -/
  id_eq : ∀ o ∈ g.objects, fid o.id = (f o).id
  /-- Представитель имеет тот же тип. -/
  kind_eq : ∀ o ∈ g.objects, (f o).kind = o.kind
  /-- Представитель имеет то же имя. -/
  label_eq : ∀ o ∈ g.objects, (f o).label = o.label
  /-- Дубликаты (совпадающие тип и имя) получают общего представителя. -/
  merge : ∀ a ∈ g.objects, ∀ b ∈ g.objects, a.kind = b.kind → a.label = b.label → f a = f b

namespace CanonChoice

variable {g} (c : CanonChoice g)

/-- Переименование связи: её концы заменяются каноническими. -/
def relMap (r : KnowledgeRelation) : KnowledgeRelation := ⟨c.fid r.source, c.fid r.target, r.kind, r.confidence⟩

@[simp] theorem relMap_kind (r : KnowledgeRelation) : (c.relMap r).kind = r.kind := rfl

@[simp] theorem relMap_source (r : KnowledgeRelation) : (c.relMap r).source = c.fid r.source := rfl

@[simp] theorem relMap_target (r : KnowledgeRelation) : (c.relMap r).target = c.fid r.target := rfl

end CanonChoice

/-- **Дедупликация графа знаний.** Каждый объект заменяется своим
каноническим представителем, каждая связь — связью между представителями. -/
def dedup (c : CanonChoice g) : KnowledgeGraph where
  objects := g.objects.image c.f
  relations := g.relations.image c.relMap
  unique_id := by
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
    exact g.unique_id _ (c.mem x hx) _ (c.mem y hy) hab
  src_closed := by
    intro r hr
    obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨o, ho, hoid⟩ := g.src_closed r₀ hr₀
    refine ⟨c.f o, Finset.mem_image_of_mem _ ho, ?_⟩
    rw [c.relMap_source, ← hoid, c.id_eq o ho]
  tgt_closed := by
    intro r hr
    obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨o, ho, hoid⟩ := g.tgt_closed r₀ hr₀
    refine ⟨c.f o, Finset.mem_image_of_mem _ ho, ?_⟩
    rw [c.relMap_target, ← hoid, c.id_eq o ho]

@[simp] theorem dedup_objects (c : CanonChoice g) :
    (g.dedup c).objects = g.objects.image c.f := rfl

@[simp] theorem dedup_relations (c : CanonChoice g) :
    (g.dedup c).relations = g.relations.image c.relMap := rfl

/-- **Дедупликация нормализует граф**: после неё пара «тип + каноническое
имя» определяет объект однозначно, то есть каждый концепт существует
ровно один раз. -/
theorem dedup_normalized (c : CanonChoice g) : (g.dedup c).Normalized := by
  intro a ha b hb hk hl
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
  refine c.merge x hx y hy ?_ ?_
  · rw [← c.kind_eq x hx, ← c.kind_eq y hy]; exact hk
  · rw [← c.label_eq x hx, ← c.label_eq y hy]; exact hl

/-- Дедупликация не увеличивает объём знания. -/
theorem dedup_card_le (c : CanonChoice g) :
    (g.dedup c).objects.card ≤ g.objects.card ∧
      (g.dedup c).relations.card ≤ g.relations.card :=
  ⟨Finset.card_image_le, Finset.card_image_le⟩

/-- Дедупликация ничего не теряет: каждая зависимость исходного графа
присутствует в дедуплицированном (между каноническими представителями). -/
theorem dedup_dep_of_dep (c : CanonChoice g) {a b : ℕ} (h : g.Dep a b) :
    (g.dedup c).Dep (c.fid a) (c.fid b) := by
  obtain ⟨r, hr, hstr, hsrc, htgt⟩ := h
  refine ⟨c.relMap r, Finset.mem_image_of_mem _ hr, hstr, ?_, ?_⟩
  · rw [c.relMap_source, hsrc]
  · rw [c.relMap_target, htgt]

/-- Дедупликация не создаёт зависимостей «из ниоткуда»: всякая зависимость
дедуплицированного графа — образ зависимости исходного. -/
theorem dedup_dep_iff (c : CanonChoice g) {x y : ℕ} :
    (g.dedup c).Dep x y ↔ ∃ a b, g.Dep a b ∧ c.fid a = x ∧ c.fid b = y := by
  constructor
  · rintro ⟨r, hr, hstr, hsrc, htgt⟩
    obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.1 hr
    exact ⟨r₀.source, r₀.target, ⟨r₀, hr₀, hstr, rfl, rfl⟩, hsrc, htgt⟩
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact g.dedup_dep_of_dep c hab

/-- **Слияние дубликатов не создаёт циклов**, если оно согласовано
с уровнями: если каждая зависимость понижает уровень и канонический
представитель имеет тот же уровень, то дедуплицированный граф ацикличен. -/
theorem dedup_acyclic_of_rank (c : CanonChoice g) (rank : ℕ → ℕ)
    (hrank : ∀ a b, g.Dep a b → rank b < rank a)
    (hfid : ∀ i, rank (c.fid i) = rank i) :
    (g.dedup c).Acyclic := by
  refine (g.dedup c).acyclic_of_rank rank ?_
  intro x y hxy
  obtain ⟨a, b, hab, rfl, rfl⟩ := (g.dedup_dep_iff c).1 hxy
  rw [hfid a, hfid b]
  exact hrank a b hab

/-- **Идемпотентность.** В уже нормализованном графе каждый объект является
своим собственным каноническим представителем, поэтому дедупликация
не меняет ни объектов, ни идентификаторов. -/
theorem dedup_fixed_of_normalized (c : CanonChoice g) (hn : g.Normalized)
    {o : KnowledgeObject} (ho : o ∈ g.objects) : c.f o = o :=
  hn _ (c.mem o ho) o ho (c.kind_eq o ho) (c.label_eq o ho)

theorem dedup_objects_eq_of_normalized (c : CanonChoice g) (hn : g.Normalized) :
    (g.dedup c).objects = g.objects := by
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    rw [g.dedup_fixed_of_normalized c hn hx]
    exact hx
  · intro a ha
    exact Finset.mem_image.2 ⟨a, ha, g.dedup_fixed_of_normalized c hn ha⟩

theorem dedup_fid_eq_of_normalized (c : CanonChoice g) (hn : g.Normalized)
    {o : KnowledgeObject} (ho : o ∈ g.objects) : c.fid o.id = o.id := by
  rw [c.id_eq o ho, g.dedup_fixed_of_normalized c hn ho]

/-- Тривиальный выбор представителя: каждый объект канонизирует сам себя.
Он корректен ровно для нормализованных графов и показывает, что структура
`CanonChoice` непуста. -/
def CanonChoice.trivial (hn : g.Normalized) : CanonChoice g where
  f := id
  fid := id
  mem := fun _ ho => ho
  id_eq := fun _ _ => rfl
  kind_eq := fun _ _ => rfl
  label_eq := fun _ _ => rfl
  merge := fun a ha b hb hk hl => hn a ha b hb hk hl

end KnowledgeGraph

end Polymath
