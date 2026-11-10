import Mathlib

/-!
# POLYMATH-ATLAS: ядро формальной модели знаний

Формализация базового слоя модели знаний:

* `ObjectKind`      — типы сущностей онтологии (Symbol, Concept, Mechanism, Invariant,
                 Step, Proof, Observation, Transformation);
* `Maturity`   — состояние зрелости знания (Hypothesis → Prototype → Validated →
                 Canonical → Axiom), образующее линейный порядок;
* `KnowledgeObject`       — Knowledge Object (узел графа знаний);
* `KnowledgeRelation`        — RELATION как самостоятельная сущность (отдельный слой связей);
* `KnowledgeGraph`     — граф знаний со встроенной ссылочной целостностью.

Здесь же доказаны базовые свойства: единственность разрешения ссылки
(отсутствие «битых ссылок»), сохранение нормализованности при удалении
объектов и общая лемма о фундированности ациклического конечного отношения.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

/-! ## Общая лемма о фундированности -/

/-- Если отношение `D` живёт на конечном носителе `s` и ациклично
(нет нетривиальных циклов), то «спуск по зависимостям» фундирован.
Это формальное основание для доказательств индукцией по графу знаний
и для проверки замкнутости доказательств. -/
theorem wellFounded_flip_of_acyclic {s : Finset ℕ} {D : ℕ → ℕ → Prop}
    (hsupp : ∀ a b, D a b → a ∈ s ∧ b ∈ s)
    (hac : ∀ a, ¬ Relation.TransGen D a a) :
    WellFounded (fun b a => D a b) := by
  classical
  set V : Type := {i : ℕ // i ∈ s} with hVdef
  set R : V → V → Prop := fun x y => Relation.TransGen D y.1 x.1 with hRdef
  haveI : IsTrans V R := ⟨fun _ _ _ hxy hyz => hyz.trans hxy⟩
  haveI : Std.Irrefl R := ⟨fun x => hac x.1⟩
  have hwf : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
  have key : ∀ v : V, Acc (fun b a => D a b) v.1 := by
    intro v
    induction v using hwf.induction with
    | _ v ih =>
      refine Acc.intro v.1 ?_
      intro b hb
      have hbs : b ∈ s := (hsupp _ _ hb).2
      exact ih ⟨b, hbs⟩ (Relation.TransGen.single hb)
  refine ⟨fun a => ?_⟩
  by_cases ha : a ∈ s
  · exact key ⟨a, ha⟩
  · exact Acc.intro a (fun b hb => absurd (hsupp _ _ hb).1 ha)

/-! ## Типы сущностей и зрелость знания -/

/-- Тип сущности онтологии знаний. -/
inductive ObjectKind where
  | symbol | concept | mechanism | invariant
  | step | proof | observation | transformation
  deriving DecidableEq, Repr, Inhabited

/-- Состояние зрелости знания. -/
inductive Maturity where
  | hypothesis | prototype | validated | canonical | axiom
  deriving DecidableEq, Repr, Inhabited

/-- Численный ранг зрелости. -/
def Maturity.rank : Maturity → ℕ
  | .hypothesis => 0
  | .prototype => 1
  | .validated => 2
  | .canonical => 3
  | .axiom => 4

theorem Maturity.rank_injective : Function.Injective Maturity.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [Maturity.rank]

/-- Зрелость знания линейно упорядочена. -/
instance : LinearOrder Maturity := LinearOrder.lift' Maturity.rank Maturity.rank_injective

theorem Maturity.le_iff_rank_le (a b : Maturity) : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

theorem Maturity.lt_iff_rank_lt (a b : Maturity) : a < b ↔ a.rank < b.rank := Iff.rfl

/-- Жизненный цикл знания образует строго возрастающую цепочку состояний. -/
theorem Maturity.lifecycle_chain :
    Maturity.hypothesis < Maturity.prototype ∧
    Maturity.prototype < Maturity.validated ∧
    Maturity.validated < Maturity.canonical ∧
    Maturity.canonical < Maturity.axiom := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Maturity.lt_iff_rank_lt, Maturity.rank]

/-- `axiom` — максимальное состояние зрелости. -/
theorem Maturity.le_axiom (m : Maturity) : m ≤ Maturity.axiom := by
  cases m <;> simp [Maturity.le_iff_rank_le, Maturity.rank]

/-- `hypothesis` — минимальное состояние зрелости. -/
theorem Maturity.hypothesis_le (m : Maturity) : Maturity.hypothesis ≤ m := by
  cases m <;> simp [Maturity.le_iff_rank_le, Maturity.rank]

/-! ## Knowledge Object -/

/-- Knowledge Object: атомарный узел графа знаний.
Идентичность объекта определяется числовым `id`, а не именем: `label`
является лишь локализуемым представлением. -/
structure KnowledgeObject where
  id : ℕ
  kind : ObjectKind
  label : String
  maturity : Maturity
  confidence : ℚ
  deriving DecidableEq, Repr

/-- Корректность объекта: уверенность лежит в отрезке `[0,1]`, а объект,
объявленный аксиомой, имеет максимальную уверенность. -/
def KnowledgeObject.WellFormed (o : KnowledgeObject) : Prop :=
  0 ≤ o.confidence ∧ o.confidence ≤ 1 ∧ (o.maturity = Maturity.axiom → o.confidence = 1)

/-! ## Уверенность вдоль цепочки вывода -/

/-- Уверенность вывода, опирающегося на список посылок: минимум по посылкам
(у вывода без посылок — единица). -/
def chainConfidence : List ℚ → ℚ
  | [] => 1
  | c :: t => min c (chainConfidence t)

/-- **Нет «отмывания уверенности».** Уверенность вывода не превосходит
уверенности ни одной из его посылок. -/
theorem chainConfidence_le {l : List ℚ} {c : ℚ} (hc : c ∈ l) : chainConfidence l ≤ c := by
  induction l with
  | nil => exact absurd hc (List.not_mem_nil)
  | cons a t ih =>
    rcases List.mem_cons.1 hc with rfl | ht
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih ht)

/-- Уверенность никогда не превышает единицы, если это верно для посылок. -/
theorem chainConfidence_le_one {l : List ℚ} (h : ∀ c ∈ l, c ≤ 1) : chainConfidence l ≤ 1 := by
  cases l with
  | nil => exact le_refl 1
  | cons a t => exact le_trans (min_le_left _ _) (h a (List.mem_cons_self ..))

/-! ## Relation как отдельная сущность -/

/-- Тип связи. Связь — самостоятельная единица знания, а не поле узла. -/
inductive RelationKind where
  | uses | dependsOn | buildsOn
  | causes | explains | contradicts | instanceOf | partOf | similarTo
  deriving DecidableEq, Repr, Inhabited

/-- Структурные связи — те, что образуют слой зависимостей
(`uses`, `depends_on`, `builds_on`). Именно они формируют граф выводимости. -/
def RelationKind.isStructural : RelationKind → Bool
  | .uses | .dependsOn | .buildsOn => true
  | _ => false

/-- Причинные связи отделены от структурных: «A вызывает B» не означает
«A логически обосновывает B». -/
def RelationKind.isCausal : RelationKind → Bool
  | .causes => true
  | _ => false

/-- Структурный и причинный слои не пересекаются. -/
theorem RelationKind.structural_ne_causal (k : RelationKind) :
    ¬ (k.isStructural = true ∧ k.isCausal = true) := by
  cases k <;> simp [RelationKind.isStructural, RelationKind.isCausal]

/-- RELATION: связь между двумя объектами знания. -/
structure KnowledgeRelation where
  source : ℕ
  target : ℕ
  kind : RelationKind
  confidence : ℚ
  deriving DecidableEq, Repr

/-! ## Граф знаний -/

/-- Граф знаний: множество объектов и множество связей с гарантированной
ссылочной целостностью и уникальностью идентификаторов. -/
structure KnowledgeGraph where
  objects : Finset KnowledgeObject
  relations : Finset KnowledgeRelation
  unique_id : ∀ a ∈ objects, ∀ b ∈ objects, a.id = b.id → a = b
  src_closed : ∀ r ∈ relations, ∃ o ∈ objects, o.id = r.source
  tgt_closed : ∀ r ∈ relations, ∃ o ∈ objects, o.id = r.target

namespace KnowledgeGraph

variable (g : KnowledgeGraph)

/-- Множество идентификаторов графа. -/
def ids : Finset ℕ := g.objects.image KnowledgeObject.id

theorem mem_ids_iff (i : ℕ) : i ∈ g.ids ↔ ∃ o ∈ g.objects, o.id = i := by
  simp [ids]

theorem src_mem_ids {r : KnowledgeRelation} (hr : r ∈ g.relations) : r.source ∈ g.ids := by
  obtain ⟨o, ho, hid⟩ := g.src_closed r hr
  exact (g.mem_ids_iff r.source).2 ⟨o, ho, hid⟩

theorem tgt_mem_ids {r : KnowledgeRelation} (hr : r ∈ g.relations) : r.target ∈ g.ids := by
  obtain ⟨o, ho, hid⟩ := g.tgt_closed r hr
  exact (g.mem_ids_iff r.target).2 ⟨o, ho, hid⟩

/-- **Ссылочная целостность.** Каждая связь разрешается в *единственный*
объект-источник и *единственный* объект-цель: битых и неоднозначных ссылок
в графе знаний не существует. -/
theorem relation_resolves {r : KnowledgeRelation} (hr : r ∈ g.relations) :
    (∃! o, o ∈ g.objects ∧ o.id = r.source) ∧ (∃! o, o ∈ g.objects ∧ o.id = r.target) := by
  constructor
  · obtain ⟨o, ho, hid⟩ := g.src_closed r hr
    exact ⟨o, ⟨ho, hid⟩, fun o' ⟨ho', hid'⟩ => g.unique_id o' ho' o ho (by rw [hid', hid])⟩
  · obtain ⟨o, ho, hid⟩ := g.tgt_closed r hr
    exact ⟨o, ⟨ho, hid⟩, fun o' ⟨ho', hid'⟩ => g.unique_id o' ho' o ho (by rw [hid', hid])⟩

/-- Разрешение идентификатора однозначно. -/
theorem lookup_unique {i : ℕ} {a b : KnowledgeObject} (ha : a ∈ g.objects) (hb : b ∈ g.objects)
    (hia : a.id = i) (hib : b.id = i) : a = b :=
  g.unique_id a ha b hb (by rw [hia, hib])

/-! ### Нормализованность: один концепт существует ровно один раз -/

/-- Граф нормализован, если пара «тип + каноническое имя» определяет объект
однозначно: знание определяется один раз и переиспользуется. -/
def Normalized : Prop :=
  ∀ a ∈ g.objects, ∀ b ∈ g.objects, a.kind = b.kind → a.label = b.label → a = b

/-- В нормализованном графе ссылка по имени однозначна. -/
theorem normalized_lookup_unique (h : g.Normalized) {k : ObjectKind} {l : String}
    {a b : KnowledgeObject} (ha : a ∈ g.objects) (hb : b ∈ g.objects)
    (hka : a.kind = k) (hkb : b.kind = k) (hla : a.label = l) (hlb : b.label = l) :
    a = b :=
  h a ha b hb (by rw [hka, hkb]) (by rw [hla, hlb])

/-! ### Удаление объекта и восстановление целостности -/

/-- Удаление объекта вместе со всеми инцидентными ему связями.
Результат снова является корректным графом знаний: операция
не может породить битую ссылку. -/
def eraseObj (o : KnowledgeObject) : KnowledgeGraph where
  objects := g.objects.erase o
  relations := g.relations.filter (fun r => r.source ≠ o.id ∧ r.target ≠ o.id)
  unique_id := by
    intro a ha b hb hab
    exact g.unique_id a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
  src_closed := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hr, hne, -⟩ := hr
    obtain ⟨o', ho', hid⟩ := g.src_closed r hr
    refine ⟨o', Finset.mem_erase.2 ⟨?_, ho'⟩, hid⟩
    rintro rfl
    exact hne hid.symm
  tgt_closed := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hr, -, hne⟩ := hr
    obtain ⟨o', ho', hid⟩ := g.tgt_closed r hr
    refine ⟨o', Finset.mem_erase.2 ⟨?_, ho'⟩, hid⟩
    rintro rfl
    exact hne hid.symm

theorem eraseObj_objects_subset (o : KnowledgeObject) : (g.eraseObj o).objects ⊆ g.objects :=
  Finset.erase_subset _ _

theorem eraseObj_relations_subset (o : KnowledgeObject) : (g.eraseObj o).relations ⊆ g.relations :=
  Finset.filter_subset _ _

/-- Нормализованность — наследуемое свойство: она сохраняется при удалении. -/
theorem eraseObj_normalized (o : KnowledgeObject) (h : g.Normalized) : (g.eraseObj o).Normalized := by
  intro a ha b hb hk hl
  exact h a (g.eraseObj_objects_subset o ha) b (g.eraseObj_objects_subset o hb) hk hl

/-- **Безопасное удаление.** Если на объект никто не ссылается и он сам ни на
что не ссылается, удаление не затрагивает ни одной связи. -/
theorem eraseObj_relations_eq_of_isolated (o : KnowledgeObject)
    (h : ∀ r ∈ g.relations, r.source ≠ o.id ∧ r.target ≠ o.id) :
    (g.eraseObj o).relations = g.relations := by
  apply Finset.filter_true_of_mem
  intro r hr
  exact h r hr

end KnowledgeGraph

end Polymath
