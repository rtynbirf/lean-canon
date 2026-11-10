import RequestProject.Scale

/-!
# Единый цикл системы: OBSERVE → … → EVOLVE

Финальный вывод аудита: архитектура должна строиться вокруг замкнутого цикла

`REPRESENTATION → PROCESS → FEEDBACK → EVOLUTION → NEW REPRESENTATION`,

развёрнутого в оператор `OBSERVE → REPRESENT → MODEL → PREDICT → ACT →
MEASURE → UPDATE → EVOLVE`.

Формализованы обе стороны цикла.

* **Фазовая сторона.** Фазы `Phase` и переход `Phase.next`. Доказано, что
  цикл действительно замкнут (восемь шагов возвращают в исходную фазу),
  что переход — биекция (у каждой фазы ровно один предшественник и ровно
  один преемник, тупиков и развилок нет) и что из любой фазы достижима
  любая другая.
* **Операторная сторона.** Один оборот цикла — это композиция
  «представление → обработка → обратная связь → эволюция» над графом
  знаний. Доказано, что оборот только накапливает знание (`Extends`),
  сохраняет любые пошаговые инварианты (в частности ацикличность
  и нормализованность), порождает башню знания `KnowledgeTower` и в конечном
  универсуме за конечное число оборотов выходит на неподвижную точку.
* **Обратная связь на уровне доказательств.** Множество обоснованных
  утверждений `groundedClaims` только растёт вдоль цикла и в конечном
  универсуме утверждений стабилизируется.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

/-! ## Фазы цикла -/

/-- Фаза единого операционного цикла системы. -/
inductive Phase where
  | observe | represent | model | predict | act | measure | update | evolve
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Переход к следующей фазе; после `evolve` цикл замыкается на `observe`. -/
def Phase.next : Phase → Phase
  | .observe => .represent
  | .represent => .model
  | .model => .predict
  | .predict => .act
  | .act => .measure
  | .measure => .update
  | .update => .evolve
  | .evolve => .observe

/-- **Цикл замкнут.** Восемь переходов возвращают систему в исходную фазу. -/
theorem Phase.next_iterate_eight (p : Phase) : Phase.next^[8] p = p := by
  cases p <;> rfl

/-- Переход между фазами — биекция: у каждой фазы ровно один преемник
и ровно один предшественник, тупиков и развилок в цикле нет. -/
theorem Phase.next_bijective : Function.Bijective Phase.next := by
  have hinj : Function.Injective Phase.next := by
    intro a b h
    revert h
    cases a <;> cases b <;> simp [Phase.next]
  exact Finite.injective_iff_bijective.1 hinj

/-- **Достижимость.** Из любой фазы за не более чем семь шагов достижима
любая другая фаза цикла. -/
theorem Phase.reachable (p q : Phase) : ∃ n : Fin 8, Phase.next^[n.val] p = q := by
  revert p q
  decide

/-! ## Оборот цикла над графом знаний -/

/-- Один оборот цикла: представление → обработка → обратная связь →
эволюция. Каждая стадия — операция над графом знаний. -/
def cycleRun (represent process feedback evolution : KnowledgeGraph → KnowledgeGraph) : KnowledgeGraph → KnowledgeGraph :=
  evolution ∘ feedback ∘ process ∘ represent

/-- Стадия «накапливающая»: она может добавлять знание, но не удалять его. -/
def Accumulating (F : KnowledgeGraph → KnowledgeGraph) : Prop := ∀ g, KnowledgeGraph.Extends (F g) g

theorem accumulating_id : Accumulating id := fun g => KnowledgeGraph.extends_refl g

theorem accumulating_comp {F G : KnowledgeGraph → KnowledgeGraph} (hF : Accumulating F)
    (hG : Accumulating G) : Accumulating (F ∘ G) :=
  fun g => KnowledgeGraph.extends_trans (hG g) (hF (G g))

/-- **Оборот цикла только накапливает знание.** Если каждая стадия
накапливающая, то и весь оборот накапливающий. -/
theorem cycleRun_accumulating {represent process feedback evolution : KnowledgeGraph → KnowledgeGraph}
    (hr : Accumulating represent) (hp : Accumulating process)
    (hf : Accumulating feedback) (he : Accumulating evolution) :
    Accumulating (cycleRun represent process feedback evolution) := by
  have h₁ : Accumulating (process ∘ represent) := accumulating_comp hp hr
  have h₂ : Accumulating (feedback ∘ process ∘ represent) := accumulating_comp hf h₁
  exact accumulating_comp he h₂

/-- Инвариант, сохраняемый каждой стадией, сохраняется и оборотом цикла. -/
theorem cycleRun_invariant {represent process feedback evolution : KnowledgeGraph → KnowledgeGraph}
    (Inv : KnowledgeGraph → Prop)
    (hr : ∀ g, Inv g → Inv (represent g)) (hp : ∀ g, Inv g → Inv (process g))
    (hf : ∀ g, Inv g → Inv (feedback g)) (he : ∀ g, Inv g → Inv (evolution g))
    (g : KnowledgeGraph) (hg : Inv g) :
    Inv (cycleRun represent process feedback evolution g) :=
  he _ (hf _ (hp _ (hr g hg)))

/-! ## Цикл порождает башню знания -/

/-- Итерации накапливающего оператора образуют башню знания: каждый
следующий оборот цикла даёт новый уровень, включающий предыдущий. -/
def KnowledgeTower.ofAccumulating (F : KnowledgeGraph → KnowledgeGraph) (hF : Accumulating F) (g₀ : KnowledgeGraph) : KnowledgeTower where
  graph := fun n => F^[n] g₀
  step_extends := by
    intro n
    rw [Function.iterate_succ_apply']
    exact hF _

@[simp] theorem KnowledgeTower.ofAccumulating_graph (F : KnowledgeGraph → KnowledgeGraph) (hF : Accumulating F)
    (g₀ : KnowledgeGraph) (n : ℕ) : (KnowledgeTower.ofAccumulating F hF g₀).graph n = F^[n] g₀ := rfl

/-- **Знание цикла монотонно.** Всё, что известно после `m` оборотов,
известно и после любого большего числа оборотов. -/
theorem cycle_objects_subset (F : KnowledgeGraph → KnowledgeGraph) (hF : Accumulating F) (g₀ : KnowledgeGraph)
    {m n : ℕ} (h : m ≤ n) : (F^[m] g₀).objects ⊆ (F^[n] g₀).objects :=
  (KnowledgeTower.ofAccumulating F hF g₀).objects_subset_of_le h

/-- Зависимости, установленные на некотором обороте цикла, сохраняются. -/
theorem cycle_dep_of_le (F : KnowledgeGraph → KnowledgeGraph) (hF : Accumulating F) (g₀ : KnowledgeGraph)
    {m n : ℕ} (h : m ≤ n) {a b : ℕ} (hd : (F^[m] g₀).Dep a b) : (F^[n] g₀).Dep a b :=
  (KnowledgeTower.ofAccumulating F hF g₀).dep_of_le h hd

/-- **Замыкание цикла.** Накапливающий оборот цикла, работающий внутри
конечного универсума объектов и связей, за конечное число оборотов выходит
на неподвижную точку: очередной оборот уже ничего не добавляет. -/
theorem cycle_stabilizes (F : KnowledgeGraph → KnowledgeGraph) (hF : Accumulating F)
    (U : Finset KnowledgeObject) (V : Finset KnowledgeRelation) (g₀ : KnowledgeGraph)
    (hclosed : ∀ g, g.objects ⊆ U → g.relations ⊆ V →
      (F g).objects ⊆ U ∧ (F g).relations ⊆ V)
    (hU₀ : g₀.objects ⊆ U) (hV₀ : g₀.relations ⊆ V) :
    ∃ n ≤ U.card + V.card,
      (F^[n + 1] g₀).objects = (F^[n] g₀).objects ∧
        (F^[n + 1] g₀).relations = (F^[n] g₀).relations :=
  selfImprovement_stabilizes F U V hF hclosed g₀ hU₀ hV₀

/-! ## Обратная связь на уровне доказательств -/

namespace ProofGraph

open Classical in
/-- Множество обоснованных утверждений графа доказательств — «капитал»
проверенного знания, который измеряет обратная связь цикла. -/
noncomputable def groundedClaims (P : ProofGraph) : Finset ℕ :=
  P.claims.filter (fun c => P.Grounded c)

theorem mem_groundedClaims {P : ProofGraph} {c : ℕ} :
    c ∈ P.groundedClaims ↔ P.Grounded c := by
  classical
  simp only [groundedClaims, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨P.grounded_mem_claims h, h⟩⟩

theorem groundedClaims_subset_claims (P : ProofGraph) : P.groundedClaims ⊆ P.claims :=
  fun _ hc => P.grounded_mem_claims (mem_groundedClaims.1 hc)

/-- **Обратная связь не разрушает знания.** При переходе к расширенной
версии графа доказательств множество обоснованных утверждений только
растёт. -/
theorem groundedClaims_mono {P P' : ProofGraph} (h : Extends P' P) :
    P.groundedClaims ⊆ P'.groundedClaims := by
  intro c hc
  exact mem_groundedClaims.2 (grounded_mono P h (mem_groundedClaims.1 hc))

theorem groundedClaims_card_mono {P P' : ProofGraph} (h : Extends P' P) :
    P.groundedClaims.card ≤ P'.groundedClaims.card :=
  Finset.card_le_card (groundedClaims_mono h)

end ProofGraph

namespace ProofTower

variable (S : ProofTower)

/-- Объём проверенного знания вдоль башни (цикла) не убывает. -/
theorem groundedClaims_subset_of_le {m n : ℕ} (h : m ≤ n) :
    (S.pgraph m).groundedClaims ⊆ (S.pgraph n).groundedClaims :=
  ProofGraph.groundedClaims_mono (S.extends_of_le h)

/-- **Насыщение проверенного знания.** Если все утверждения башни лежат
в конечном универсуме `C`, то не позднее чем через `C.card` уровней
множество обоснованных утверждений перестаёт расти. -/
theorem groundedClaims_saturates (C : Finset ℕ) (hC : ∀ n, (S.pgraph n).claims ⊆ C) :
    ∃ n ≤ C.card, (S.pgraph (n + 1)).groundedClaims = (S.pgraph n).groundedClaims := by
  set c : ℕ → ℕ := fun n => (S.pgraph n).groundedClaims.card with hc
  have hsub : ∀ n, (S.pgraph n).groundedClaims ⊆ (S.pgraph (n + 1)).groundedClaims :=
    fun n => ProofGraph.groundedClaims_mono (S.step_extends n)
  have hmono : ∀ n, c n ≤ c (n + 1) := fun n => Finset.card_le_card (hsub n)
  have hb : ∀ n, c n ≤ C.card := fun n =>
    Finset.card_le_card (((S.pgraph n).groundedClaims_subset_claims).trans (hC n))
  obtain ⟨n, hn, hcn⟩ := monotone_bounded_stabilizes c C.card hmono hb
  refine ⟨n, hn, ?_⟩
  exact (Finset.eq_of_subset_of_card_le (hsub n) (le_of_eq hcn)).symm

end ProofTower

end Polymath
