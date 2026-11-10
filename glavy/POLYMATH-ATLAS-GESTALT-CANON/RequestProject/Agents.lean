import RequestProject.Evolution

/-!
# Агентная архитектура: роли, протокол и его гарантии

Уровень аудита v9 (агенты) и пункт «построить агентную архитектуру с ролями
и протоколами» итогового приоритета.

Модель: агент имеет *роль*, роль определяет, какие *действия* над графом
знаний ему разрешены, а протокол — это цепочка разрешённых действий
(`Legal`). Доказано, что протокол сохраняет все инварианты ядра:

* ссылочная целостность (по построению: каждое действие возвращает `KnowledgeGraph`);
* нормализованность «один концепт существует ровно один раз»;
* корректность объектов (уверенность в `[0,1]`, аксиома ⇒ уверенность `1`);
* ацикличность графа зависимостей;
* **ни один объект не становится каноническим или аксиомой без участия
  агента-верификатора.**
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

/-! ## Дополнительные операции над графом знаний -/

namespace KnowledgeGraph

variable (g : KnowledgeGraph)

/-- Удаление объекта по идентификатору вместе с инцидентными связями. -/
def eraseId (i : ℕ) : KnowledgeGraph where
  objects := g.objects.filter (fun o => o.id ≠ i)
  relations := g.relations.filter (fun r => r.source ≠ i ∧ r.target ≠ i)
  unique_id := by
    intro a ha b hb hab
    exact g.unique_id a (Finset.mem_of_mem_filter _ ha) b (Finset.mem_of_mem_filter _ hb) hab
  src_closed := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hr, hne, -⟩ := hr
    obtain ⟨o, ho, hid⟩ := g.src_closed r hr
    exact ⟨o, Finset.mem_filter.2 ⟨ho, by rw [hid]; exact hne⟩, hid⟩
  tgt_closed := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hr, -, hne⟩ := hr
    obtain ⟨o, ho, hid⟩ := g.tgt_closed r hr
    exact ⟨o, Finset.mem_filter.2 ⟨ho, by rw [hid]; exact hne⟩, hid⟩

@[simp] theorem eraseId_relations (i : ℕ) :
    (g.eraseId i).relations = g.relations.filter (fun r => r.source ≠ i ∧ r.target ≠ i) := rfl

theorem eraseId_objects_subset (i : ℕ) : (g.eraseId i).objects ⊆ g.objects :=
  Finset.filter_subset _ _

theorem eraseId_relations_subset (i : ℕ) : (g.eraseId i).relations ⊆ g.relations :=
  Finset.filter_subset _ _

theorem eraseId_normalized (i : ℕ) (h : g.Normalized) : (g.eraseId i).Normalized :=
  fun a ha b hb hk hl =>
    h a (g.eraseId_objects_subset i ha) b (g.eraseId_objects_subset i hb) hk hl

theorem eraseId_dep {i a b : ℕ} (h : (g.eraseId i).Dep a b) : g.Dep a b := by
  obtain ⟨r, hr, hstr, hsrc, htgt⟩ := h
  exact ⟨r, g.eraseId_relations_subset i hr, hstr, hsrc, htgt⟩

theorem eraseId_acyclic (i : ℕ) (hac : g.Acyclic) : (g.eraseId i).Acyclic := by
  intro a hcyc
  exact hac a (Relation.TransGen.mono (fun _ _ h => g.eraseId_dep h) hcyc)

/-- Изменение зрелости объекта с заданным идентификатором. -/
def setMaturity (i : ℕ) (m : Maturity) : KnowledgeGraph where
  objects := g.objects.image (fun o => if o.id = i then { o with maturity := m } else o)
  relations := g.relations
  unique_id := by
    intro a ha b hb hab
    simp only [Finset.mem_image] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hxid : (if x.id = i then { x with maturity := m } else x).id = x.id := by
      split <;> rfl
    have hyid : (if y.id = i then { y with maturity := m } else y).id = y.id := by
      split <;> rfl
    have : x = y := g.unique_id x hx y hy (by rw [← hxid, ← hyid]; exact hab)
    rw [this]
  src_closed := by
    intro r hr
    obtain ⟨o, ho, hid⟩ := g.src_closed r hr
    refine ⟨_, Finset.mem_image_of_mem _ ho, ?_⟩
    rw [show (if o.id = i then { o with maturity := m } else o).id = o.id by split <;> rfl]
    exact hid
  tgt_closed := by
    intro r hr
    obtain ⟨o, ho, hid⟩ := g.tgt_closed r hr
    refine ⟨_, Finset.mem_image_of_mem _ ho, ?_⟩
    rw [show (if o.id = i then { o with maturity := m } else o).id = o.id by split <;> rfl]
    exact hid

@[simp] theorem setMaturity_relations (i : ℕ) (m : Maturity) :
    (g.setMaturity i m).relations = g.relations := rfl

theorem setMaturity_acyclic (i : ℕ) (m : Maturity) (hac : g.Acyclic) :
    (g.setMaturity i m).Acyclic := hac

theorem setMaturity_normalized (i : ℕ) (m : Maturity) (h : g.Normalized) :
    (g.setMaturity i m).Normalized := by
  intro a ha b hb hk hl
  simp only [setMaturity, Finset.mem_image] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have hxk : (if x.id = i then { x with maturity := m } else x).kind = x.kind := by split <;> rfl
  have hyk : (if y.id = i then { y with maturity := m } else y).kind = y.kind := by split <;> rfl
  have hxl : (if x.id = i then { x with maturity := m } else x).label = x.label := by
    split <;> rfl
  have hyl : (if y.id = i then { y with maturity := m } else y).label = y.label := by
    split <;> rfl
  have : x = y := h x hx y hy (by rw [← hxk, ← hyk]; exact hk) (by rw [← hxl, ← hyl]; exact hl)
  rw [this]

end KnowledgeGraph

/-! ## Роли, агенты и действия -/

/-- Роль агента в системе. -/
inductive Role where
  | generator | verifier | critic | integrator | archivist
  deriving DecidableEq, Repr, Inhabited

/-- Агент: идентификатор, роль и уровень доверия. -/
structure Agent where
  id : ℕ
  role : Role
  trust : ℚ
  deriving DecidableEq, Repr

/-- Действие над графом знаний. -/
inductive Action where
  | propose (o : KnowledgeObject)
  | link (r : KnowledgeRelation)
  | promote (i : ℕ) (m : Maturity)
  | retract (i : ℕ)
  deriving DecidableEq, Repr

/-- Порождать новые объекты знания может только генератор. -/
def Role.mayPropose : Role → Bool
  | .generator => true
  | _ => false

/-- Связывать объекты может только интегратор. -/
def Role.mayLink : Role → Bool
  | .integrator => true
  | _ => false

/-- Повышать зрелость знания может только верификатор. -/
def Role.mayPromote : Role → Bool
  | .verifier => true
  | _ => false

/-- Отзывать знание может только критик. -/
def Role.mayRetract : Role → Bool
  | .critic => true
  | _ => false

theorem Role.mayPromote_iff (r : Role) : r.mayPromote = true ↔ r = Role.verifier := by
  cases r <;> simp [Role.mayPromote]

/-- Протокол: какие действия разрешены агенту в текущем состоянии графа.

* генератор предлагает только корректный объект незрелого статуса и только
  такой, которого (в смысле «тип + имя») в графе ещё нет;
* интегратор связывает лишь существующие объекты и не имеет права замкнуть
  цикл зависимостей;
* верификатор объявляет аксиомой лишь знание с уверенностью `1`. -/
def Permitted (g : KnowledgeGraph) (a : Agent) : Action → Prop
  | .propose o =>
      a.role.mayPropose = true ∧ o.WellFormed ∧ o.maturity ≤ Maturity.prototype ∧
        ∀ x ∈ g.objects, x.kind = o.kind → x.label ≠ o.label
  | .link r =>
      a.role.mayLink = true ∧ r.source ∈ g.ids ∧ r.target ∈ g.ids ∧
        ¬ Relation.ReflTransGen g.Dep r.target r.source
  | .promote i m =>
      a.role.mayPromote = true ∧
        (m = Maturity.axiom → ∀ o ∈ g.objects, o.id = i → o.confidence = 1)
  | .retract _ => a.role.mayRetract = true

/-! ## Семантика действий -/

namespace KnowledgeGraph

/-- Применение действия к графу знаний. Результат — снова корректный граф
знаний: ссылочная целостность гарантирована типом. -/
def step (g : KnowledgeGraph) : Action → KnowledgeGraph
  | .propose o => if h : o.id ∉ g.ids then g.addObject o h else g
  | .link r => if h : r.source ∈ g.ids ∧ r.target ∈ g.ids then g.addRelation r h.1 h.2 else g
  | .promote i m => g.setMaturity i m
  | .retract i => g.eraseId i

/-- Выполнение цепочки действий (протокольного следа). -/
def run : KnowledgeGraph → List (Agent × Action) → KnowledgeGraph
  | g, [] => g
  | g, p :: t => run (g.step p.2) t

@[simp] theorem run_nil (g : KnowledgeGraph) : g.run [] = g := rfl

@[simp] theorem run_cons (g : KnowledgeGraph) (p : Agent × Action) (t : List (Agent × Action)) :
    g.run (p :: t) = (g.step p.2).run t := rfl

end KnowledgeGraph

/-- Легальный протокольный след: каждое действие разрешено агенту
в том состоянии графа, в котором оно выполняется. -/
inductive Legal : KnowledgeGraph → List (Agent × Action) → Prop
  | nil {g : KnowledgeGraph} : Legal g []
  | cons {g : KnowledgeGraph} {ag : Agent} {a : Action} {t : List (Agent × Action)} :
      Permitted g ag a → Legal (g.step a) t → Legal g ((ag, a) :: t)

namespace KnowledgeGraph

variable (g : KnowledgeGraph)

/-! ## Гарантии протокола -/

/-- **Ссылочная целостность сохраняется всегда.** После любого следа действий
каждая связь по-прежнему разрешается в единственный источник и единственную
цель. -/
theorem run_relation_resolves (tr : List (Agent × Action)) {r : KnowledgeRelation}
    (hr : r ∈ (g.run tr).relations) :
    (∃! o, o ∈ (g.run tr).objects ∧ o.id = r.source) ∧
      (∃! o, o ∈ (g.run tr).objects ∧ o.id = r.target) :=
  (g.run tr).relation_resolves hr

/-- Одно разрешённое действие сохраняет нормализованность. -/
theorem step_normalized {ag : Agent} {a : Action} (hp : Permitted g ag a)
    (hn : g.Normalized) : (g.step a).Normalized := by
  cases a with
  | propose o =>
    obtain ⟨-, -, -, hfresh⟩ := hp
    by_cases h : o.id ∉ g.ids
    · simpa [step, h] using g.addObj_normalized o h hn hfresh
    · simpa [step, h] using hn
  | link r =>
    by_cases h : r.source ∈ g.ids ∧ r.target ∈ g.ids
    · simpa [step, h] using hn
    · simpa [step, h] using hn
  | promote i m => exact g.setMaturity_normalized i m hn
  | retract i => exact g.eraseId_normalized i hn

/-- Одно разрешённое действие сохраняет ацикличность. -/
theorem step_acyclic {ag : Agent} {a : Action} (hp : Permitted g ag a)
    (hac : g.Acyclic) : (g.step a).Acyclic := by
  cases a with
  | propose o =>
    by_cases h : o.id ∉ g.ids
    · simpa [step, h] using g.addObj_acyclic o h hac
    · simpa [step, h] using hac
  | link r =>
    obtain ⟨-, hs, ht, hno⟩ := hp
    have h : r.source ∈ g.ids ∧ r.target ∈ g.ids := ⟨hs, ht⟩
    simpa [step, h] using g.addRel_acyclic r hs ht hac hno
  | promote i m => exact g.setMaturity_acyclic i m hac
  | retract i => exact g.eraseId_acyclic i hac

/-- Все объекты графа корректны. -/
def AllWellFormed : Prop := ∀ o ∈ g.objects, o.WellFormed

/-- Одно разрешённое действие сохраняет корректность объектов: в частности,
верификатор не может объявить аксиомой знание с уверенностью меньше `1`. -/
theorem step_allWellFormed {ag : Agent} {a : Action} (hp : Permitted g ag a)
    (hw : g.AllWellFormed) : (g.step a).AllWellFormed := by
  cases a with
  | propose o =>
    obtain ⟨-, hwf, -, -⟩ := hp
    by_cases h : o.id ∉ g.ids
    · simp only [step, dif_pos h, AllWellFormed, addObj_objects]
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact hwf
      · exact hw x hx'
    · simpa [step, h] using hw
  | link r =>
    by_cases h : r.source ∈ g.ids ∧ r.target ∈ g.ids
    · simpa [step, h] using hw
    · simpa [step, h] using hw
  | promote i m =>
    obtain ⟨-, hax⟩ := hp
    intro x hx
    simp only [step, setMaturity, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨h0, h1, hA⟩ := hw y hy
    by_cases hid : y.id = i
    · simp only [hid, if_true]
      refine ⟨h0, h1, ?_⟩
      intro hm
      exact hax hm y hy hid
    · simpa [hid] using ⟨h0, h1, hA⟩
  | retract i =>
    intro x hx
    exact hw x (g.eraseId_objects_subset i hx)

/-- **Легальный протокол сохраняет нормализованность.** -/
theorem run_normalized {tr : List (Agent × Action)} (hl : Legal g tr) (hn : g.Normalized) :
    (g.run tr).Normalized := by
  induction hl with
  | nil => exact hn
  | @cons g ag a t hp _ ih => exact ih (g.step_normalized hp hn)

/-- **Легальный протокол сохраняет ацикличность графа зависимостей.** -/
theorem run_acyclic {tr : List (Agent × Action)} (hl : Legal g tr) (hac : g.Acyclic) :
    (g.run tr).Acyclic := by
  induction hl with
  | nil => exact hac
  | @cons g ag a t hp _ ih => exact ih (g.step_acyclic hp hac)

/-- **Легальный протокол сохраняет корректность объектов.** -/
theorem run_allWellFormed {tr : List (Agent × Action)} (hl : Legal g tr)
    (hw : g.AllWellFormed) : (g.run tr).AllWellFormed := by
  induction hl with
  | nil => exact hw
  | @cons g ag a t hp _ ih => exact ih (g.step_allWellFormed hp hw)

/-! ### Никакой канонизации без верификатора -/

/-- Идентификаторы объектов, признанных каноническими (или аксиомами). -/
def canonicalIds : Finset ℕ :=
  (g.objects.filter (fun o => Maturity.canonical ≤ o.maturity)).image KnowledgeObject.id

theorem mem_canonicalIds_iff (i : ℕ) :
    i ∈ g.canonicalIds ↔ ∃ o ∈ g.objects, Maturity.canonical ≤ o.maturity ∧ o.id = i := by
  simp only [canonicalIds, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨o, ⟨ho, hm⟩, hid⟩; exact ⟨o, ho, hm, hid⟩
  · rintro ⟨o, ho, hm, hid⟩; exact ⟨o, ⟨ho, hm⟩, hid⟩

/-- Действие агента, не являющегося верификатором, не расширяет множество
канонического знания. -/
theorem step_canonicalIds_subset {ag : Agent} {a : Action} (hp : Permitted g ag a)
    (hv : ag.role ≠ Role.verifier) : (g.step a).canonicalIds ⊆ g.canonicalIds := by
  cases a with
  | propose o =>
    obtain ⟨-, -, hm, -⟩ := hp
    by_cases h : o.id ∉ g.ids
    · intro i hi
      rw [mem_canonicalIds_iff] at hi ⊢
      obtain ⟨x, hx, hxm, hxid⟩ := hi
      rw [show (g.step (Action.propose o)).objects = insert o g.objects by simp [step, h]] at hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact absurd (le_trans hxm hm) (by decide)
      · exact ⟨x, hx', hxm, hxid⟩
    · simp [step, h]
  | link r =>
    by_cases h : r.source ∈ g.ids ∧ r.target ∈ g.ids
    · simp [step, h, canonicalIds, addRelation]
    · simp [step, h]
  | promote i m =>
    exact absurd ((Role.mayPromote_iff ag.role).1 hp.1) hv
  | retract i =>
    intro j hj
    rw [mem_canonicalIds_iff] at hj ⊢
    obtain ⟨x, hx, hxm, hxid⟩ := hj
    exact ⟨x, g.eraseId_objects_subset i hx, hxm, hxid⟩

/-- **Знание не канонизируется само собой.** Если в легальном протокольном
следе не участвует ни один агент-верификатор, то множество канонического
знания не растёт: статус «canonical»/«axiom» может быть присвоен только
действием верификатора. -/
theorem run_canonicalIds_subset {tr : List (Agent × Action)} (hl : Legal g tr)
    (hv : ∀ p ∈ tr, p.1.role ≠ Role.verifier) :
    (g.run tr).canonicalIds ⊆ g.canonicalIds := by
  induction hl with
  | nil => exact subset_rfl
  | @cons g ag a t hp _ ih =>
    have hag : ag.role ≠ Role.verifier := hv (ag, a) (List.mem_cons_self ..)
    have hrest : ∀ p ∈ t, p.1.role ≠ Role.verifier :=
      fun p hpt => hv p (List.mem_cons_of_mem _ hpt)
    exact (ih hrest).trans (g.step_canonicalIds_subset hp hag)

end KnowledgeGraph

end Polymath
