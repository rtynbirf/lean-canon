import RequestProject.Agents

/-!
# Метаобучение и самоизменение

Уровни аудита v62–v64 (метаобучение, самоизменение, рекурсивное
самоулучшение) и пункт 5 итогового приоритета.

Самоизменение моделируется как оператор `F : KnowledgeGraph → KnowledgeGraph`, который
система применяет к собственному графу знаний. Доказано:

* **сохранение инвариантов при самоизменении**: если один шаг сохраняет
  свойство, то его сохраняет и любое число шагов (в частности,
  ссылочная целостность, нормализованность и ацикличность);
* **сходимость рекурсивного самоулучшения**: монотонный оператор,
  работающий внутри конечного универсума, за конечное число шагов
  достигает неподвижной точки;
* **невозможность самообоснования**: правило, ссылающееся на себя как на
  посылку, не обосновано, поэтому самоизменение не может «доказать себя».
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath

/-! ## Стабилизация монотонной ограниченной величины -/

/-- Неубывающая ограниченная числовая характеристика обязательно
стабилизируется на одном из первых `B + 1` шагов. -/
theorem monotone_bounded_stabilizes (c : ℕ → ℕ) (B : ℕ)
    (hmono : ∀ n, c n ≤ c (n + 1)) (hb : ∀ n, c n ≤ B) :
    ∃ n ≤ B, c (n + 1) = c n := by
  by_contra hcon
  push_neg at hcon
  have hstrict : ∀ n ≤ B, c n < c (n + 1) := by
    intro n hn
    exact lt_of_le_of_ne (hmono n) (fun h => hcon n hn h.symm)
  have key : ∀ n ≤ B + 1, n ≤ c n := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hkB : k ≤ B := by omega
      have := hstrict k hkB
      have hk' : k ≤ c k := ih (by omega)
      omega
  have h1 : B + 1 ≤ c (B + 1) := key (B + 1) le_rfl
  have h2 : c (B + 1) ≤ B := hb (B + 1)
  omega

/-! ## Самоизменение сохраняет инварианты -/

/-- **Инвариант самоизменения.** Если оператор самоизменения сохраняет
свойство `Inv` за один шаг, то оно сохраняется после любого числа шагов. -/
theorem iterate_invariant (F : KnowledgeGraph → KnowledgeGraph) (Inv : KnowledgeGraph → Prop)
    (hF : ∀ g, Inv g → Inv (F g)) (g₀ : KnowledgeGraph) (h₀ : Inv g₀) (n : ℕ) :
    Inv (F^[n] g₀) := by
  induction n with
  | zero => simpa using h₀
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hF _ ih

/-- Ацикличность сохраняется при любом числе шагов самоизменения. -/
theorem iterate_acyclic (F : KnowledgeGraph → KnowledgeGraph)
    (hF : ∀ g, g.Acyclic → (F g).Acyclic) (g₀ : KnowledgeGraph) (h₀ : g₀.Acyclic) (n : ℕ) :
    (F^[n] g₀).Acyclic :=
  iterate_invariant F KnowledgeGraph.Acyclic hF g₀ h₀ n

/-- Нормализованность («один концепт существует ровно один раз») сохраняется
при любом числе шагов самоизменения. -/
theorem iterate_normalized (F : KnowledgeGraph → KnowledgeGraph)
    (hF : ∀ g, g.Normalized → (F g).Normalized) (g₀ : KnowledgeGraph) (h₀ : g₀.Normalized) (n : ℕ) :
    (F^[n] g₀).Normalized :=
  iterate_invariant F KnowledgeGraph.Normalized hF g₀ h₀ n

/-- Ссылочная целостность самоизменяющейся системы не нарушается никогда:
каждое состояние — корректный граф знаний. -/
theorem iterate_relation_resolves (F : KnowledgeGraph → KnowledgeGraph) (g₀ : KnowledgeGraph) (n : ℕ)
    {r : KnowledgeRelation} (hr : r ∈ (F^[n] g₀).relations) :
    (∃! o, o ∈ (F^[n] g₀).objects ∧ o.id = r.source) ∧
      (∃! o, o ∈ (F^[n] g₀).objects ∧ o.id = r.target) :=
  (F^[n] g₀).relation_resolves hr

/-! ## Сходимость рекурсивного самоулучшения -/

/-- **Рекурсивное самоулучшение сходится.** Монотонный оператор самоизменения
(знание только накапливается), работающий внутри конечного универсума
объектов `U` и связей `V`, за конечное число шагов достигает неподвижной
точки: очередная итерация уже ничего не добавляет. -/
theorem selfImprovement_stabilizes (F : KnowledgeGraph → KnowledgeGraph) (U : Finset KnowledgeObject) (V : Finset KnowledgeRelation)
    (hmono : ∀ g, KnowledgeGraph.Extends (F g) g)
    (hclosed : ∀ g, g.objects ⊆ U → g.relations ⊆ V →
      (F g).objects ⊆ U ∧ (F g).relations ⊆ V)
    (g₀ : KnowledgeGraph) (hU₀ : g₀.objects ⊆ U) (hV₀ : g₀.relations ⊆ V) :
    ∃ n ≤ U.card + V.card,
      (F^[n + 1] g₀).objects = (F^[n] g₀).objects ∧
        (F^[n + 1] g₀).relations = (F^[n] g₀).relations := by
  set G : ℕ → KnowledgeGraph := fun n => F^[n] g₀ with hG
  have hsucc : ∀ n, G (n + 1) = F (G n) := by
    intro n
    simp [hG, Function.iterate_succ_apply']
  have hobj : ∀ n, (G n).objects ⊆ (G (n + 1)).objects := by
    intro n; rw [hsucc n]; exact (hmono (G n)).1
  have hrel : ∀ n, (G n).relations ⊆ (G (n + 1)).relations := by
    intro n; rw [hsucc n]; exact (hmono (G n)).2
  have hbound : ∀ n, (G n).objects ⊆ U ∧ (G n).relations ⊆ V := by
    intro n
    induction n with
    | zero => exact ⟨by simpa [hG] using hU₀, by simpa [hG] using hV₀⟩
    | succ k ih => rw [hsucc k]; exact hclosed _ ih.1 ih.2
  have hboundU : ∀ n, (G n).objects ⊆ U := fun n => (hbound n).1
  have hboundV : ∀ n, (G n).relations ⊆ V := fun n => (hbound n).2
  set c : ℕ → ℕ := fun n => (G n).objects.card + (G n).relations.card with hc
  have hcmono : ∀ n, c n ≤ c (n + 1) :=
    fun n => Nat.add_le_add (Finset.card_le_card (hobj n)) (Finset.card_le_card (hrel n))
  have hcb : ∀ n, c n ≤ U.card + V.card :=
    fun n => Nat.add_le_add (Finset.card_le_card (hboundU n)) (Finset.card_le_card (hboundV n))
  obtain ⟨n, hn, hcn⟩ := monotone_bounded_stabilizes c (U.card + V.card) hcmono hcb
  refine ⟨n, hn, ?_, ?_⟩
  · have hcard : (G (n + 1)).objects.card ≤ (G n).objects.card := by
      have h1 : (G n).objects.card ≤ (G (n + 1)).objects.card :=
        Finset.card_le_card (hobj n)
      have h2 : (G n).relations.card ≤ (G (n + 1)).relations.card :=
        Finset.card_le_card (hrel n)
      simp only [hc] at hcn
      omega
    exact (Finset.eq_of_subset_of_card_le (hobj n) hcard).symm
  · have hcard : (G (n + 1)).relations.card ≤ (G n).relations.card := by
      have h1 : (G n).objects.card ≤ (G (n + 1)).objects.card :=
        Finset.card_le_card (hobj n)
      have h2 : (G n).relations.card ≤ (G (n + 1)).relations.card :=
        Finset.card_le_card (hrel n)
      simp only [hc] at hcn
      omega
    exact (Finset.eq_of_subset_of_card_le (hrel n) hcard).symm

/-! ## Границы самообоснования -/

namespace ProofGraph

variable (P : ProofGraph)

/-- **Метаправило не может обосновать само себя.** Если правило самоизменения
включено в граф доказательств как утверждение, опирающееся (пусть и косвенно)
на самого себя, и не объявлено аксиомой, то оно не обосновано. -/
theorem not_grounded_of_self_reaching {c : ℕ} (hcyc : P.Reaches c c)
    (hax : ∀ x, P.Reaches c x → P.Reaches x c → x ∉ P.axioms) :
    ¬ P.Grounded c := by
  refine P.not_grounded_of_circular (S := {x | P.Reaches c x ∧ P.Reaches x c}) ?_ ?_ c
    ⟨hcyc, hcyc⟩
  · rintro x ⟨hcx, hxc⟩
    obtain ⟨p, hp, hpc⟩ := Relation.TransGen.head'_iff.1 hxc
    refine ⟨p, hp, ?_, ?_⟩
    · exact hcx.tail hp
    · rcases Relation.reflTransGen_iff_eq_or_transGen.1 hpc with rfl | h
      · exact hcx.tail hp
      · exact h
  · rintro x ⟨hcx, hxc⟩
    exact hax x hcx hxc

/-- Следствие: система, «доказывающая» своё улучшение ссылкой на само это
улучшение, не получает обоснования. -/
theorem not_grounded_self_improvement {c : ℕ} (hself : c ∈ P.premises c)
    (hax : c ∉ P.axioms) : ¬ P.Grounded c :=
  P.not_grounded_self_loop hself hax

end ProofGraph

end Polymath
