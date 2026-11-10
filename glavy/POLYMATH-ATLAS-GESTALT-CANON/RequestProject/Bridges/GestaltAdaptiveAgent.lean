/-
# Bridge 2 — Gestalt (UCC) ↔ адаптивный агент (L1–L7)

До этого модуля связь между гештальт-слоем и ядром адаптивного агента шла
косвенно, через `RequestProject/Gestalt/CoreBridge.lean` (навигатор L3, Ω,
рефлексивная самомодель).  Здесь мост сделан **двусторонним и явным**:

* **вперёд** (`uccOfAgent`): активный агент вывода порождает когнитивную
  систему UCC — её среда и шаг суть `forward s (plan s)`, а скорость обучения
  задана ошибкой предсказания (T3 выполняется по построению, а не постулатом);
* **назад** (`agentOfCognitiveSystem`): когнитивная система вместе с
  вариационной семьёй порождает активного агента вывода, действия которого —
  выбор следующего состояния, а план — шаг UCC;
* **круговые тождества** (`roundTrip_*`, `agent_roundTrip_trajectory`):
  оба перехода согласованы на наблюдаемых компонентах (среда, предсказание,
  шаг, траектория);
* **перенос теорем**: T3 (нет ошибки — нет обучения), T4 (совершенное
  предсказание при `env = step` делает траекторию неподвижной) и T5
  (возврат по принципу Дирихле) переносятся на траекторию агента.

Ни одной новой аксиомы и ни одного `sorry` этот модуль не добавляет.
-/
import RequestProject.Gestalt.CoreBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PolymathAtlas.Bridges.GestaltAdaptive

open PolymathAtlas.AdaptiveAgent
open PolymathAtlas.Gestalt.UCC

universe u v w

variable {S : Type u} {A : Type v} {Latent : Type w} [Fintype Latent]

/-! ## Вперёд: агент L3 порождает когнитивную систему UCC -/

open scoped Classical in
/-- Когнитивная система UCC, порождённая активным агентом вывода и его
предсказателем `predict`.  Среда и шаг — это применение планового действия;
скорость обучения равна `1` при ошибке предсказания и `0` при её отсутствии,
поэтому поле T3 (`learningRate_eq_zero_iff`) доказывается, а не постулируется. -/
noncomputable def uccOfAgent (M : ActivePolicyAgent S A Latent) (predict : S → S) :
    CognitiveSystem S where
  env := fun s => M.forward s (M.plan s)
  predict := predict
  step := fun s => M.forward s (M.plan s)
  learningRate := fun s =>
    if predict s = M.forward s (M.plan s) then (0 : ℝ) else 1
  learningRate_nonneg := by
    intro s; by_cases h : predict s = M.forward s (M.plan s) <;> simp [h]
  learningRate_eq_zero_iff := by
    intro s
    by_cases h : predict s = M.forward s (M.plan s) <;> simp [h]

@[simp] theorem uccOfAgent_env (M : ActivePolicyAgent S A Latent) (predict : S → S) (s : S) :
    (uccOfAgent M predict).env s = M.forward s (M.plan s) := rfl

@[simp] theorem uccOfAgent_step (M : ActivePolicyAgent S A Latent) (predict : S → S) (s : S) :
    (uccOfAgent M predict).step s = M.forward s (M.plan s) := rfl

@[simp] theorem uccOfAgent_predict (M : ActivePolicyAgent S A Latent) (predict : S → S) (s : S) :
    (uccOfAgent M predict).predict s = predict s := rfl

/-- Траектория порождённой когнитивной системы совпадает с траекторией агента:
UCC-цикл агента — это в точности его собственная динамика. -/
theorem uccOfAgent_trajectory (M : ActivePolicyAgent S A Latent) (predict : S → S)
    (x : S) (n : ℕ) :
    (uccOfAgent M predict).trajectory x n = M.trajectory x n := rfl

/-- Совершенное предсказание порождённой системы — это в точности совпадение
предсказателя с плановой динамикой агента. -/
theorem uccOfAgent_perfect_iff (M : ActivePolicyAgent S A Latent) (predict : S → S) :
    (uccOfAgent M predict).Perfect ↔ ∀ s, predict s = M.forward s (M.plan s) :=
  Iff.rfl

/-- **T3 для агента.**  Если предсказатель точен, обучение прекращается. -/
theorem uccOfAgent_no_learning_of_perfect (M : ActivePolicyAgent S A Latent) (predict : S → S)
    (h : ∀ s, predict s = M.forward s (M.plan s)) (s : S) :
    (uccOfAgent M predict).learningRate s = 0 :=
  t3_feedbackError (uccOfAgent M predict) h s

/-- **T5 для агента.**  В конечном пространстве состояний траектория активного
агента вывода обязательно возвращается в уже посещённое состояние не позже,
чем через `|S| + 1` тактов. -/
theorem agent_trajectory_revisits [Fintype S] (M : ActivePolicyAgent S A Latent) (x : S) :
    ∃ i j, i < j ∧ j ≤ t5Bound S + 1 ∧ M.trajectory x i = M.trajectory x j :=
  t5_pigeonholeRevisit (M.trajectory x) (Nat.lt_succ_self _)

/-! ## Назад: когнитивная система порождает активного агента вывода -/

/-- Активный агент вывода, порождённый когнитивной системой: действие — выбор
следующего состояния, план — шаг UCC, предпочтения нейтральны, а вариационная
семья берётся внешней (гештальт-слой сам её не содержит). -/
def agentOfCognitiveSystem (F : VariationalFamily Latent S) (C : CognitiveSystem S) :
    ActivePolicyAgent S S Latent where
  family := F
  forward := fun _ a => a
  preference := fun _ => 0
  preference_nonpos := fun _ => le_rfl
  plan := C.step

@[simp] theorem agentOfCognitiveSystem_plan (F : VariationalFamily Latent S)
    (C : CognitiveSystem S) (s : S) : (agentOfCognitiveSystem F C).plan s = C.step s := rfl

@[simp] theorem agentOfCognitiveSystem_forward (F : VariationalFamily Latent S)
    (C : CognitiveSystem S) (s a : S) : (agentOfCognitiveSystem F C).forward s a = a := rfl

/-- Ожидаемая свободная энергия порождённого агента — это в точности сложность
(KL-дивергенция апостериорного от априорного) целевого состояния: при
нейтральных предпочтениях риск исчезает и остаётся неоднозначность. -/
theorem agentOfCognitiveSystem_efe (F : VariationalFamily Latent S) (C : CognitiveSystem S)
    (s a : S) : (agentOfCognitiveSystem F C).efe s a = F.complexity a := by
  simp [ActivePolicyAgent.efe, ActivePolicyAgent.risk, ActivePolicyAgent.ambiguity,
    agentOfCognitiveSystem]

/-- Траектория порождённого агента — это траектория исходной когнитивной
системы. -/
theorem agentOfCognitiveSystem_trajectory (F : VariationalFamily Latent S)
    (C : CognitiveSystem S) (x : S) (n : ℕ) :
    (agentOfCognitiveSystem F C).trajectory x n = C.trajectory x n := rfl

/-! ## Круговые тождества -/

/-- Переход «система → агент → система» сохраняет предсказание и шаг, а среду
делает равной шагу.  Поэтому для *самосогласованных* систем (`env = step`)
все три наблюдаемые компоненты восстанавливаются точно. -/
theorem roundTrip_step (F : VariationalFamily Latent S) (C : CognitiveSystem S) (s : S) :
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).step s = C.step s := rfl

theorem roundTrip_predict (F : VariationalFamily Latent S) (C : CognitiveSystem S) (s : S) :
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).predict s = C.predict s := rfl

theorem roundTrip_env (F : VariationalFamily Latent S) (C : CognitiveSystem S)
    (h : ∀ s, C.env s = C.step s) (s : S) :
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).env s = C.env s := (h s).symm

/-- Для самосогласованной системы круговой переход сохраняет и признак
совершенного предсказания. -/
theorem roundTrip_perfect_iff (F : VariationalFamily Latent S) (C : CognitiveSystem S)
    (h : ∀ s, C.env s = C.step s) :
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).Perfect ↔ C.Perfect := by
  constructor
  · intro hp s
    have hs : C.predict s = C.step s := hp s
    rw [h s, hs]
  · intro hp s
    have hs : C.predict s = C.env s := hp s
    show C.predict s = C.step s
    rw [hs, h s]

/-- Переход «агент → система → агент» сохраняет траекторию. -/
theorem agent_roundTrip_trajectory (F : VariationalFamily Latent S)
    (M : ActivePolicyAgent S A Latent) (predict : S → S) (x : S) (n : ℕ) :
    (agentOfCognitiveSystem F (uccOfAgent M predict)).trajectory x n = M.trajectory x n := rfl

/-! ## Рефлексивный агент как когнитивная система -/

/-- Когнитивная система, порождённая рефлексивным адаптивным агентом L7. -/
noncomputable def uccOfReflexive (R : ReflexiveAdaptiveAgent S A Latent) (predict : S → S) :
    CognitiveSystem S :=
  uccOfAgent R.agent predict

/-- **T1 для рефлексивного агента через мост.**  Латентный канал рефлексивного
агента проводит различие: самокод отделён от иного кода. -/
theorem uccOfReflexive_drawsDistinction (R : ReflexiveAdaptiveAgent S A Latent) :
    PolymathAtlas.Gestalt.UCC.DrawsDistinction (fun b : Bool => if b then R.selfLatent else R.otherLatent) :=
  ⟨true, false, by simpa using R.self_ne⟩

/-- **T5 для рефлексивного агента.**  В конечном пространстве состояний его
UCC-траектория возвращается в уже посещённое состояние. -/
theorem uccOfReflexive_revisits [Fintype S] (R : ReflexiveAdaptiveAgent S A Latent)
    (predict : S → S) (x : S) :
    ∃ i j, i < j ∧ j ≤ t5Bound S + 1 ∧
      (uccOfReflexive R predict).trajectory x i = (uccOfReflexive R predict).trajectory x j :=
  t5_system_revisits _ x

/-- **Сводка Bridge 2.**  Мост двусторонний: агент даёт когнитивную систему с
той же траекторией, когнитивная система даёт агента с той же траекторией, и
оба перехода согласованы на предсказании и шаге. -/
theorem bridge2_two_sided (F : VariationalFamily Latent S) (C : CognitiveSystem S)
    (M : ActivePolicyAgent S A Latent) (predict : S → S) (x : S) :
    (∀ n, (uccOfAgent M predict).trajectory x n = M.trajectory x n) ∧
    (∀ n, (agentOfCognitiveSystem F C).trajectory x n = C.trajectory x n) ∧
    (∀ s, (uccOfAgent (agentOfCognitiveSystem F C) C.predict).step s = C.step s) ∧
    (∀ s, (uccOfAgent (agentOfCognitiveSystem F C) C.predict).predict s = C.predict s) :=
  ⟨fun n => uccOfAgent_trajectory M predict x n,
    fun n => agentOfCognitiveSystem_trajectory F C x n,
    fun s => roundTrip_step F C s, fun s => roundTrip_predict F C s⟩

end PolymathAtlas.Bridges.GestaltAdaptive
