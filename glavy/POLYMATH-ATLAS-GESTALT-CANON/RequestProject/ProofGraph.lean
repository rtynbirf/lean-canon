import RequestProject.Dependency

/-!
# Граф доказательств

Отдельный от графа знаний слой: утверждения (CLAIM), аксиомы, доказанные
утверждения и их посылки (леммы). Доказаны ключевые свойства верификации:

* обоснованность наследуется вниз по посылкам (замкнутость доказательства);
* всякое обоснованное утверждение трассируется назад к базовому (аксиоме
  или доказательству без посылок);
* циклические «доказательства» ничего не обосновывают;
* в ациклическом графе доказательств, где у каждого утверждения есть
  обоснование, обоснованы все утверждения.

В конце строится мост: граф доказательств, порождённый структурным слоем
графа знаний.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

/-- Граф доказательств. `premises c` — непосредственные посылки утверждения `c`;
`axioms` — принимаемые без доказательства утверждения; `proved` — утверждения,
для которых предъявлен вывод из их посылок. -/
structure ProofGraph where
  claims : Finset ℕ
  axioms : Finset ℕ
  proved : Finset ℕ
  premises : ℕ → Finset ℕ
  axioms_subset : axioms ⊆ claims
  proved_subset : proved ⊆ claims
  premises_subset : ∀ c ∈ claims, premises c ⊆ claims
  premises_outside : ∀ c, c ∉ claims → premises c = ∅
  axioms_leaf : ∀ c ∈ axioms, premises c = ∅

namespace ProofGraph

variable (P : ProofGraph)

/-- Отношение «утверждение `a` опирается на посылку `b`». -/
def Dep (a b : ℕ) : Prop := b ∈ P.premises a

theorem dep_support {a b : ℕ} (h : P.Dep a b) : a ∈ P.claims ∧ b ∈ P.claims := by
  have h' : b ∈ P.premises a := h
  have ha : a ∈ P.claims := by
    by_contra ha
    rw [P.premises_outside a ha] at h'
    exact absurd h' (Finset.notMem_empty b)
  exact ⟨ha, P.premises_subset a ha h'⟩

/-- Транзитивное замыкание: `a` (косвенно) опирается на `b`. -/
def Reaches (a b : ℕ) : Prop := Relation.TransGen P.Dep a b

/-- Ациклический граф доказательств: ни одно утверждение не участвует
в собственном доказательстве. -/
def Acyclic : Prop := ∀ a, ¬ P.Reaches a a

/-- **Обоснованность (grounded).** Утверждение обосновано, если оно аксиома
либо доказано и все его посылки обоснованы. Это формальный аналог
«замкнутого» доказательства. -/
inductive Grounded (P : ProofGraph) : ℕ → Prop
  | ax {c : ℕ} : c ∈ P.axioms → Grounded P c
  | inf {c : ℕ} : c ∈ P.proved → (∀ p ∈ P.premises c, Grounded P p) → Grounded P c

/-- Обоснованное утверждение принадлежит графу. -/
theorem grounded_mem_claims {c : ℕ} (h : P.Grounded c) : c ∈ P.claims := by
  cases h with
  | ax hc => exact P.axioms_subset hc
  | inf hc _ => exact P.proved_subset hc

/-- **Замкнутость по посылкам.** Всякая посылка обоснованного утверждения
сама обоснована. -/
theorem grounded_of_dep {c d : ℕ} (h : P.Grounded c) (hd : P.Dep c d) : P.Grounded d := by
  cases h with
  | ax hc =>
    have hd' : d ∈ P.premises c := hd
    rw [P.axioms_leaf c hc] at hd'
    exact absurd hd' (Finset.notMem_empty d)
  | inf _ hall => exact hall d hd

/-- Замкнутость по всей цепочке зависимостей: обоснованность распространяется
на всё дерево доказательства. -/
theorem grounded_of_reaches {c d : ℕ} (h : P.Grounded c) (hr : P.Reaches c d) :
    P.Grounded d := by
  induction hr with
  | single hd => exact P.grounded_of_dep h hd
  | tail _ hlast ih => exact P.grounded_of_dep ih hlast

/-- Базовое утверждение: аксиома либо доказательство без посылок. -/
def Base (c : ℕ) : Prop := c ∈ P.axioms ∨ (c ∈ P.proved ∧ P.premises c = ∅)

/-- **Обратная трассировка.** Всякое обоснованное утверждение приводит
по цепочке посылок к базовому утверждению. -/
theorem grounded_trace {c : ℕ} (h : P.Grounded c) :
    ∃ b, Relation.ReflTransGen P.Dep c b ∧ P.Base b := by
  induction h with
  | @ax c hc => exact ⟨c, Relation.ReflTransGen.refl, Or.inl hc⟩
  | @inf c hc _ ih =>
    by_cases hemp : P.premises c = ∅
    · exact ⟨c, Relation.ReflTransGen.refl, Or.inr ⟨hc, hemp⟩⟩
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hemp
      obtain ⟨b, hb, hbase⟩ := ih p hp
      exact ⟨b, Relation.ReflTransGen.head hp hb, hbase⟩

/-- **Циклические доказательства ничего не обосновывают.** Если каждое
утверждение множества `S` опирается на посылку из `S` и в `S` нет аксиом,
то ни одно утверждение из `S` не обосновано. -/
theorem not_grounded_of_circular {S : Set ℕ}
    (hloop : ∀ x ∈ S, ∃ p ∈ P.premises x, p ∈ S)
    (hax : ∀ x ∈ S, x ∉ P.axioms) :
    ∀ c ∈ S, ¬ P.Grounded c := by
  have key : ∀ c, P.Grounded c → c ∉ S := by
    intro c hc
    induction hc with
    | @ax c hcax => exact fun hS => hax c hS hcax
    | @inf c _ _ ih =>
      intro hS
      obtain ⟨p, hp, hpS⟩ := hloop c hS
      exact ih p hp hpS
  exact fun c hc hg => key c hg hc

/-- Утверждение, ссылающееся на само себя, не обосновано. -/
theorem not_grounded_self_loop {c : ℕ} (hc : c ∈ P.premises c) (hax : c ∉ P.axioms) :
    ¬ P.Grounded c := by
  refine P.not_grounded_of_circular (S := {c}) ?_ ?_ c rfl
  · rintro x rfl; exact ⟨x, hc, rfl⟩
  · rintro x rfl; exact hax

/-- **Полнота верификации.** Если граф доказательств ацикличен и каждое
утверждение либо аксиома, либо доказано, то обоснованы все утверждения. -/
theorem all_grounded_of_acyclic (hac : P.Acyclic)
    (hjust : ∀ c ∈ P.claims, c ∈ P.axioms ∨ c ∈ P.proved) :
    ∀ c ∈ P.claims, P.Grounded c := by
  have hwf : WellFounded (fun b a => P.Dep a b) :=
    wellFounded_flip_of_acyclic (s := P.claims) (fun _ _ h => P.dep_support h) hac
  intro c
  induction c using hwf.induction with
  | _ c ih =>
    intro hc
    rcases hjust c hc with hax | hpr
    · exact Grounded.ax hax
    · refine Grounded.inf hpr ?_
      intro p hp
      exact ih p hp (P.premises_subset c hc hp)

/-- Уровень строго понижается вдоль цепочки посылок. -/
theorem rank_lt_of_reaches (rank : ℕ → ℕ) (h : ∀ a b, P.Dep a b → rank b < rank a)
    {a b : ℕ} (hr : P.Reaches a b) : rank b < rank a := by
  induction hr with
  | single hab => exact h _ _ hab
  | tail _ hlast ih => exact lt_trans (h _ _ hlast) ih

/-- **Критерий ацикличности для графа доказательств.** Если каждая посылка
строго понижает уровень, граф доказательств ацикличен. -/
theorem acyclic_of_rank (rank : ℕ → ℕ) (h : ∀ a b, P.Dep a b → rank b < rank a) :
    P.Acyclic :=
  fun a hcyc => lt_irrefl (rank a) (P.rank_lt_of_reaches rank h hcyc)

/-- **Обнаружение незамкнутого доказательства.** Если хотя бы одна посылка
не обоснована, то и само утверждение не обосновано. -/
theorem not_grounded_of_premise_not_grounded {c p : ℕ} (hp : p ∈ P.premises c)
    (h : ¬ P.Grounded p) : ¬ P.Grounded c :=
  fun hc => h (P.grounded_of_dep hc hp)

end ProofGraph

/-! ## Мост: граф доказательств над графом знаний -/

namespace KnowledgeGraph

variable (g : KnowledgeGraph)

/-- Граф доказательств, порождённый структурным слоем графа знаний:
утверждения — объекты графа, посылки — их структурные зависимости. -/
def toProofGraph (ax pr : Finset ℕ) (hax : ax ⊆ g.ids) (hpr : pr ⊆ g.ids)
    (haxleaf : ∀ c ∈ ax, g.premises c = ∅) : ProofGraph where
  claims := g.ids
  axioms := ax
  proved := pr
  premises := g.premises
  axioms_subset := hax
  proved_subset := hpr
  premises_subset := by
    intro c _ b hb
    exact (g.dep_support ((g.mem_premises_iff c b).1 hb)).2
  premises_outside := by
    intro c hc
    by_contra hne
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hne
    exact hc (g.dep_support ((g.mem_premises_iff c b).1 hb)).1
  axioms_leaf := haxleaf

/-- Зависимость в порождённом графе доказательств — это в точности
структурная зависимость графа знаний. -/
theorem toPGraph_dep (ax pr : Finset ℕ) (hax : ax ⊆ g.ids) (hpr : pr ⊆ g.ids)
    (haxleaf : ∀ c ∈ ax, g.premises c = ∅) (a b : ℕ) :
    (g.toProofGraph ax pr hax hpr haxleaf).Dep a b ↔ g.Dep a b :=
  g.mem_premises_iff a b

/-- Ацикличность графа знаний влечёт ацикличность порождённого графа
доказательств. -/
theorem toPGraph_acyclic (ax pr : Finset ℕ) (hax : ax ⊆ g.ids) (hpr : pr ⊆ g.ids)
    (haxleaf : ∀ c ∈ ax, g.premises c = ∅) (hacg : g.Acyclic) :
    (g.toProofGraph ax pr hax hpr haxleaf).Acyclic := by
  intro a hcyc
  refine hacg a ?_
  refine Relation.TransGen.mono ?_ hcyc
  intro x y hxy
  exact (g.toPGraph_dep ax pr hax hpr haxleaf x y).1 hxy

/-- **Итоговая теорема о верификации графа знаний.** Если граф знаний
ацикличен и каждый его объект объявлен аксиомой или снабжён доказательством,
то каждый объект графа обоснован: все доказательства замкнуты. -/
theorem all_grounded (ax pr : Finset ℕ) (hax : ax ⊆ g.ids) (hpr : pr ⊆ g.ids)
    (haxleaf : ∀ c ∈ ax, g.premises c = ∅) (hacg : g.Acyclic)
    (hjust : ∀ c ∈ g.ids, c ∈ ax ∨ c ∈ pr) :
    ∀ o ∈ g.objects, (g.toProofGraph ax pr hax hpr haxleaf).Grounded o.id := by
  intro o ho
  refine ProofGraph.all_grounded_of_acyclic _
    (g.toPGraph_acyclic ax pr hax hpr haxleaf hacg) hjust o.id ?_
  exact (g.mem_ids_iff o.id).2 ⟨o, ho, rfl⟩

end KnowledgeGraph

end Polymath
