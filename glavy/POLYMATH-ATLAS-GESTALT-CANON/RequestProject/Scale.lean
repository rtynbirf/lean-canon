import RequestProject.Collective
import RequestProject.MetaLearning

/-!
# Масштабные уровни знания: башня графов

Пункт 6 итогового приоритета аудита в его полной форме — масштабирование
не только до коллективного, но и до цивилизационного, планетарного,
космического и мета-уровня.

Формализация: шкала масштабов `Scale` (линейно упорядоченная) и **башня
знания** `KnowledgeTower` — семейство графов знаний, индексированное уровнем, в
котором каждый следующий уровень расширяет предыдущий (интегрирует, а не
переписывает знание нижнего уровня).

Доказано:

* знание монотонно вдоль всей башни: объекты, связи, зависимости и
  достижимость сохраняются при переходе на любой более высокий уровень;
* переход на более высокий уровень не может «спрятать» цикл: ацикличность
  верхнего уровня влечёт ацикличность всех нижних, а нормализованность
  верхнего уровня наследуется нижними;
* у каждого элемента знания есть **уровень рождения** — минимальный уровень
  башни, на котором он появляется, и выше этого уровня он присутствует
  всегда: знание не возникает «из ниоткуда» дважды;
* **насыщение**: в конечном универсуме объектов и связей башня за конечное
  число уровней перестаёт расти;
* башня графов доказательств: всё, что обосновано на некотором уровне,
  остаётся обоснованным на всех более высоких.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

/-! ## Шкала масштабов -/

/-- Уровень организации знания — от отдельного агента до мета-уровня. -/
inductive Scale where
  | individual | collective | civilizational | planetary | cosmic | universal | metaScale
  deriving DecidableEq, Repr, Inhabited

/-- Численный ранг масштаба. -/
def Scale.rank : Scale → ℕ
  | .individual => 0
  | .collective => 1
  | .civilizational => 2
  | .planetary => 3
  | .cosmic => 4
  | .universal => 5
  | .metaScale => 6

theorem Scale.rank_injective : Function.Injective Scale.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [Scale.rank]

instance : LinearOrder Scale := LinearOrder.lift' Scale.rank Scale.rank_injective

theorem Scale.le_iff_rank_le (a b : Scale) : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

theorem Scale.lt_iff_rank_lt (a b : Scale) : a < b ↔ a.rank < b.rank := Iff.rfl

/-- Масштабы образуют строго возрастающую цепочку: индивидуальный уровень —
наименьший, мета-уровень — наибольший. -/
theorem Scale.chain :
    Scale.individual < Scale.collective ∧ Scale.collective < Scale.civilizational ∧
      Scale.civilizational < Scale.planetary ∧ Scale.planetary < Scale.cosmic ∧
      Scale.cosmic < Scale.universal ∧ Scale.universal < Scale.metaScale := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Scale.lt_iff_rank_lt, Scale.rank]

theorem Scale.individual_le (s : Scale) : Scale.individual ≤ s := by
  cases s <;> simp [Scale.le_iff_rank_le, Scale.rank]

theorem Scale.le_meta (s : Scale) : s ≤ Scale.metaScale := by
  cases s <;> simp [Scale.le_iff_rank_le, Scale.rank]

/-! ## Башня графов знаний -/

/-- **Башня знания.** Семейство графов знаний, проиндексированное уровнем
масштаба: каждый следующий уровень целиком включает предыдущий. -/
structure KnowledgeTower where
  graph : ℕ → KnowledgeGraph
  step_extends : ∀ n, KnowledgeGraph.Extends (graph (n + 1)) (graph n)

namespace KnowledgeTower

variable (T : KnowledgeTower)

/-- Знание монотонно вдоль башни: верхний уровень расширяет любой нижний. -/
theorem extends_of_le {m n : ℕ} (h : m ≤ n) : KnowledgeGraph.Extends (T.graph n) (T.graph m) := by
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.1 h
    subst this
    exact KnowledgeGraph.extends_refl _
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with hk | hk
    · exact KnowledgeGraph.extends_trans (ih (Nat.lt_succ_iff.1 hk)) (T.step_extends k)
    · subst hk
      exact KnowledgeGraph.extends_refl _

/-- Объекты не теряются при подъёме по башне. -/
theorem objects_subset_of_le {m n : ℕ} (h : m ≤ n) :
    (T.graph m).objects ⊆ (T.graph n).objects := (T.extends_of_le h).1

/-- Связи не теряются при подъёме по башне. -/
theorem relations_subset_of_le {m n : ℕ} (h : m ≤ n) :
    (T.graph m).relations ⊆ (T.graph n).relations := (T.extends_of_le h).2

/-- Идентификаторы знания не теряются. -/
theorem ids_subset_of_le {m n : ℕ} (h : m ≤ n) : (T.graph m).ids ⊆ (T.graph n).ids :=
  KnowledgeGraph.ids_subset_of_extends _ (T.extends_of_le h)

/-- Зависимости сохраняются при подъёме по башне. -/
theorem dep_of_le {m n : ℕ} (h : m ≤ n) {a b : ℕ} (hd : (T.graph m).Dep a b) :
    (T.graph n).Dep a b :=
  KnowledgeGraph.dep_of_extends _ (T.extends_of_le h) hd

/-- Достижимость по зависимостям сохраняется при подъёме по башне. -/
theorem reaches_of_le {m n : ℕ} (h : m ≤ n) {a b : ℕ} (hr : (T.graph m).Reaches a b) :
    (T.graph n).Reaches a b :=
  KnowledgeGraph.reaches_of_extends _ (T.extends_of_le h) hr

/-- **Верхний уровень не прячет противоречий.** Если знание ациклично на
некотором уровне башни, оно ациклично и на всех нижних. -/
theorem acyclic_of_le {m n : ℕ} (h : m ≤ n) (hac : (T.graph n).Acyclic) :
    (T.graph m).Acyclic :=
  KnowledgeGraph.acyclic_of_extends _ (T.extends_of_le h) hac

/-- Нормализованность верхнего уровня наследуется нижними: если на общем
уровне «один концепт существует ровно один раз», то это верно и локально. -/
theorem normalized_of_le {m n : ℕ} (h : m ≤ n) (hn : (T.graph n).Normalized) :
    (T.graph m).Normalized :=
  fun a ha b hb hk hl =>
    hn a (T.objects_subset_of_le h ha) b (T.objects_subset_of_le h hb) hk hl

/-- **Уровень рождения знания.** Всякий объект, присутствующий на некотором
уровне башни, имеет минимальный уровень появления: ниже него объекта нет,
а начиная с него он присутствует на всех уровнях. -/
theorem exists_birth {n : ℕ} {o : KnowledgeObject} (ho : o ∈ (T.graph n).objects) :
    ∃ k ≤ n, o ∈ (T.graph k).objects ∧ (∀ j < k, o ∉ (T.graph j).objects) ∧
      ∀ j, k ≤ j → o ∈ (T.graph j).objects := by
  classical
  have hex : ∃ k, o ∈ (T.graph k).objects := ⟨n, ho⟩
  refine ⟨Nat.find hex, Nat.find_le ho, Nat.find_spec hex, ?_, ?_⟩
  · intro j hj
    exact Nat.find_min hex hj
  · intro j hj
    exact T.objects_subset_of_le hj (Nat.find_spec hex)

/-- Аналогично для связей: у каждой связи есть уровень рождения. -/
theorem exists_birth_rel {n : ℕ} {r : KnowledgeRelation} (hr : r ∈ (T.graph n).relations) :
    ∃ k ≤ n, r ∈ (T.graph k).relations ∧ (∀ j < k, r ∉ (T.graph j).relations) ∧
      ∀ j, k ≤ j → r ∈ (T.graph j).relations := by
  classical
  have hex : ∃ k, r ∈ (T.graph k).relations := ⟨n, hr⟩
  refine ⟨Nat.find hex, Nat.find_le hr, Nat.find_spec hex, ?_, ?_⟩
  · intro j hj
    exact Nat.find_min hex hj
  · intro j hj
    exact T.relations_subset_of_le hj (Nat.find_spec hex)

/-- **Насыщение башни.** Если всё знание башни живёт в конечном универсуме
объектов `U` и связей `V`, то начиная с некоторого уровня (не позднее
`U.card + V.card`) очередной уровень уже ничего не добавляет. -/
theorem saturates (U : Finset KnowledgeObject) (V : Finset KnowledgeRelation)
    (hU : ∀ n, (T.graph n).objects ⊆ U) (hV : ∀ n, (T.graph n).relations ⊆ V) :
    ∃ n ≤ U.card + V.card,
      (T.graph (n + 1)).objects = (T.graph n).objects ∧
        (T.graph (n + 1)).relations = (T.graph n).relations := by
  set c : ℕ → ℕ := fun n => (T.graph n).objects.card + (T.graph n).relations.card with hc
  have hobj : ∀ n, (T.graph n).objects ⊆ (T.graph (n + 1)).objects :=
    fun n => (T.step_extends n).1
  have hrel : ∀ n, (T.graph n).relations ⊆ (T.graph (n + 1)).relations :=
    fun n => (T.step_extends n).2
  have hcmono : ∀ n, c n ≤ c (n + 1) :=
    fun n => Nat.add_le_add (Finset.card_le_card (hobj n)) (Finset.card_le_card (hrel n))
  have hcb : ∀ n, c n ≤ U.card + V.card :=
    fun n => Nat.add_le_add (Finset.card_le_card (hU n)) (Finset.card_le_card (hV n))
  obtain ⟨n, hn, hcn⟩ := monotone_bounded_stabilizes c (U.card + V.card) hcmono hcb
  have h1 : (T.graph n).objects.card ≤ (T.graph (n + 1)).objects.card :=
    Finset.card_le_card (hobj n)
  have h2 : (T.graph n).relations.card ≤ (T.graph (n + 1)).relations.card :=
    Finset.card_le_card (hrel n)
  simp only [hc] at hcn
  refine ⟨n, hn, ?_, ?_⟩
  · exact (Finset.eq_of_subset_of_card_le (hobj n) (by omega)).symm
  · exact (Finset.eq_of_subset_of_card_le (hrel n) (by omega)).symm

end KnowledgeTower

/-! ## Башня графов доказательств -/

/-- Башня доказательного знания: каждый следующий уровень расширяет
предыдущий как граф доказательств. -/
structure ProofTower where
  pgraph : ℕ → ProofGraph
  step_extends : ∀ n, ProofGraph.Extends (pgraph (n + 1)) (pgraph n)

namespace ProofTower

variable (S : ProofTower)

theorem extends_of_le {m n : ℕ} (h : m ≤ n) : ProofGraph.Extends (S.pgraph n) (S.pgraph m) := by
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.1 h
    subst this
    exact ProofGraph.pextends_refl _
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with hk | hk
    · exact ProofGraph.pextends_trans (ih (Nat.lt_succ_iff.1 hk)) (S.step_extends k)
    · subst hk
      exact ProofGraph.pextends_refl _

/-- **Обоснованность живёт вверх по масштабам.** Всё, что доказано на
некотором уровне, остаётся доказанным на всех более высоких уровнях: подъём
масштаба не обесценивает знание. -/
theorem grounded_of_le {m n : ℕ} (h : m ≤ n) {c : ℕ} (hg : (S.pgraph m).Grounded c) :
    (S.pgraph n).Grounded c :=
  ProofGraph.grounded_mono _ (S.extends_of_le h) hg

/-- Утверждения не исчезают при подъёме по башне. -/
theorem claims_subset_of_le {m n : ℕ} (h : m ≤ n) :
    (S.pgraph m).claims ⊆ (S.pgraph n).claims := (S.extends_of_le h).1

/-- Посылки уже существующих утверждений не переписываются на верхних
уровнях: доказательство, однажды зафиксированное, остаётся тем же. -/
theorem premises_eq_of_le {m n : ℕ} (h : m ≤ n) {c : ℕ} (hc : c ∈ (S.pgraph m).claims) :
    (S.pgraph n).premises c = (S.pgraph m).premises c := (S.extends_of_le h).2.2.2 c hc

end ProofTower

end Polymath
