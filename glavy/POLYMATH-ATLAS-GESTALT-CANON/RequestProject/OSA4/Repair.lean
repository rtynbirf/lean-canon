/-
# OSA-4.0 — лексикографический оптимизатор ремонта

Формализация §8 «LEXICOGRAPHIC REPAIR OPTIMIZER» и LAW-018 (Repair
Soundness) кодекса OSA-4.0.  Целевой вектор ремонта

    V = [SafetyViolations, ResidualProofObligations,
         EffectPolicyViolations, ResidualUncertainty, ExecutionCost]

минимизируется лексикографически: безопасность абсолютно доминирует над
стоимостью (тест T15: «дёшево и небезопасно» проигрывает «дорого и
безопасно»).
-/
import RequestProject.OSA4.Effects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-- Целевой вектор ремонта. -/
structure RVec where
  /-- Нарушения безопасности. -/
  safety : ℕ
  /-- Оставшиеся обязательства доказательства. -/
  obligations : ℕ
  /-- Нарушения политики эффектов. -/
  policy : ℕ
  /-- Остаточная неопределённость. -/
  uncertainty : ℕ
  /-- Стоимость исполнения. -/
  cost : ℕ
  deriving DecidableEq, Repr, Inhabited

namespace RVec

/-- Лексикографический ключ вектора. -/
def key (v : RVec) : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (v.safety, toLex (v.obligations, toLex (v.policy,
    toLex (v.uncertainty, v.cost))))

/-- Лексикографический порядок на векторах ремонта. -/
def lt (a b : RVec) : Prop := a.key < b.key

/-- Нестрогий лексикографический порядок. -/
def le (a b : RVec) : Prop := a.key ≤ b.key

instance : DecidableRel lt := fun a b => by unfold lt; infer_instance
instance : DecidableRel le := fun a b => by unfold le; infer_instance

theorem lt_irrefl (a : RVec) : ¬ lt a a := by
  simp [lt]

theorem lt_trans {a b c : RVec} (h₁ : lt a b) (h₂ : lt b c) : lt a c :=
  _root_.lt_trans h₁ h₂

theorem le_total' (a b : RVec) : le a b ∨ le b a := by
  unfold le; exact _root_.le_total a.key b.key

theorem lt_or_ge (a b : RVec) : lt a b ∨ le b a := by
  unfold lt le
  rcases _root_.lt_or_ge a.key b.key with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem le_refl' (a : RVec) : le a a := le_of_eq rfl

theorem le_trans' {a b c : RVec} (h₁ : le a b) (h₂ : le b c) : le a c :=
  _root_.le_trans h₁ h₂

/-- **Безопасность доминирует.**  Меньшее число нарушений безопасности
делает вектор лучше при *любых* остальных компонентах — в частности при
любой стоимости. -/
theorem safety_dominates {a b : RVec} (h : a.safety < b.safety) : lt a b := by
  simp [lt, key, Prod.Lex.toLex_lt_toLex, h]

/-- **T15.**  Дешёвый небезопасный ремонт `[1,0,0,0,1]` проигрывает дорогому
безопасному `[0,0,0,0,3]`. -/
theorem torture_T15_safe_beats_cheap :
    lt ⟨0, 0, 0, 0, 3⟩ ⟨1, 0, 0, 0, 1⟩ :=
  safety_dominates (by norm_num)

/-- При равной безопасности сравниваются обязательства доказательства. -/
theorem obligations_second {a b : RVec} (hs : a.safety = b.safety)
    (h : a.obligations < b.obligations) : lt a b := by
  simp [lt, key, Prod.Lex.toLex_lt_toLex, hs, h]

/-- Стоимость — последний критерий: она решает только при совпадении всех
предыдущих компонент. -/
theorem cost_last {a b : RVec} (hs : a.safety = b.safety)
    (ho : a.obligations = b.obligations) (hp : a.policy = b.policy)
    (hu : a.uncertainty = b.uncertainty) (h : a.cost < b.cost) : lt a b := by
  simp [lt, key, Prod.Lex.toLex_lt_toLex, hs, ho, hp, hu, h]

/-- Выбор лучшего кандидата среди `a` и списка `l`: лексикографический
минимум. -/
def bestAux (a : RVec) : List RVec → RVec
  | [] => a
  | b :: t => if le a b then bestAux a t else bestAux b t

/-- Лексикографический минимум списка кандидатов. -/
def best : List RVec → Option RVec
  | [] => none
  | a :: t => some (bestAux a t)

theorem bestAux_mem : ∀ (l : List RVec) (a : RVec), bestAux a l ∈ a :: l := by
  intro l
  induction l with
  | nil => intro a; simp [bestAux]
  | cons b t ih =>
      intro a
      by_cases h : le a b
      · have := ih a
        rw [bestAux, if_pos h]
        rcases List.mem_cons.mp this with h' | h'
        · simp [h']
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')
      · have := ih b
        rw [bestAux, if_neg h]
        rcases List.mem_cons.mp this with h' | h'
        · simp [h']
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')

theorem bestAux_le : ∀ (l : List RVec) (a : RVec),
    le (bestAux a l) a ∧ ∀ b ∈ l, le (bestAux a l) b := by
  intro l
  induction l with
  | nil => intro a; exact ⟨le_refl' a, by simp⟩
  | cons b t ih =>
      intro a
      by_cases h : le a b
      · obtain ⟨h₁, h₂⟩ := ih a
        rw [bestAux, if_pos h]
        refine ⟨h₁, ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact le_trans' h₁ h
        · exact h₂ c hc'
      · obtain ⟨h₁, h₂⟩ := ih b
        have hba : le b a := by
          rcases le_total' a b with hab | hba
          · exact absurd hab h
          · exact hba
        rw [bestAux, if_neg h]
        refine ⟨le_trans' h₁ hba, ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact h₁
        · exact h₂ c hc'

/-- Выбранный ремонт действительно является одним из кандидатов. -/
theorem best_mem {l : List RVec} {a : RVec} (h : best l = some a) : a ∈ l := by
  cases l with
  | nil => exact absurd h (by simp [best])
  | cons x t =>
      have hax : a = bestAux x t := by simpa [best] using h.symm
      exact hax ▸ bestAux_mem t x

/-- Выбранный ремонт не хуже любого кандидата: оптимизатор действительно
минимизирует целевой вектор. -/
theorem best_le {l : List RVec} {a : RVec} (h : best l = some a) :
    ∀ b ∈ l, le a b := by
  cases l with
  | nil => exact absurd h (by simp [best])
  | cons x t =>
      have hax : a = bestAux x t := by simpa [best] using h.symm
      intro b hb
      obtain ⟨h₁, h₂⟩ := bestAux_le t x
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hax ▸ h₁
      · exact hax ▸ h₂ b hb'

/-- Непустой список кандидатов всегда даёт выбор. -/
theorem best_isSome (a : RVec) (l : List RVec) : (best (a :: l)).isSome := rfl

end RVec

/-! ## LAW-018 — Repair Soundness -/

/-- Все предусловия цепочки доказаны по шагам (и все авторизации получены). -/
def chainEnabled : List Op → KState → Prop
  | [], _ => True
  | o :: t, st => execAllowed st o ∧ chainEnabled t (o.exec st)

/-- План ремонта: починенная цепочка операторов и её целевой вектор. -/
structure RepairPlan where
  /-- Починенная цепочка операторов. -/
  chain : List Op
  /-- Целевой вектор плана. -/
  vec : RVec
  deriving Inhabited

/-- План корректен, если починенная цепочка исполняется из состояния `s`
(все предусловия и авторизации доказаны по шагам) и достигает цели. -/
def RepairPlan.sound (p : RepairPlan) (s : KState) (goal : Pred) : Prop :=
  chainEnabled p.chain s ∧ eval (execChain p.chain s) goal = .TRUE_KNOWN

/-- **LAW-018 (Repair Soundness).**  Оптимизатор выбирает план из числа
кандидатов, и если все кандидаты корректны, то выбранный план корректен и
лексикографически минимален.  Выбор определяется доказанным критерием минимальности, а не отдельным
примером. -/
theorem law018_repair_sound (s : KState) (goal : Pred)
    (plans : List RepairPlan) (hsound : ∀ p ∈ plans, p.sound s goal)
    {v : RVec} (hbest : RVec.best (plans.map RepairPlan.vec) = some v) :
    ∃ p ∈ plans, p.vec = v ∧ p.sound s goal ∧
      ∀ q ∈ plans, RVec.le v q.vec := by
  have hmem : v ∈ plans.map RepairPlan.vec := RVec.best_mem hbest
  obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hmem
  refine ⟨p, hp, hpv, hsound p hp, ?_⟩
  intro q hq
  exact RVec.best_le hbest q.vec (List.mem_map_of_mem hq)

end Polymath.OSA4
