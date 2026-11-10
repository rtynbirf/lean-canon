import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RSIA_Agent
import RequestProject.Atlas.UAM_RSIA_Environment

set_option autoImplicit false

/-!
# RSIA — выполнение действий (Задача A, Phase 1)

Агенты действуют на стигмергическую среду. Каждое действие производит
шаг следа (`StigmergicTrace.step`). Последовательность действий
накапливает след через `StigmergicTrace.append`.
-/

namespace UAM_RSIA

universe u

/-- Длина стигмергического следа = число шагов. -/
def StigmergicTrace.length {α : Type u} : StigmergicTrace α → Nat
  | .empty => 0
  | .step _ _ _ rest => rest.length + 1

/-- Пустой след имеет длину 0. -/
@[simp] theorem StigmergicTrace.length_empty {α : Type u} :
    (StigmergicTrace.empty : StigmergicTrace α).length = 0 := rfl

/-- Длина шага. -/
@[simp] theorem StigmergicTrace.length_step {α : Type u}
    (agentId : AgentId) (before after : UAM_Free.FreeMonoid α)
    (rest : StigmergicTrace α) :
    (StigmergicTrace.step agentId before after rest).length = rest.length + 1 :=
  rfl

/-- Длина конкатенации следов складывается. -/
theorem StigmergicTrace.length_append {α : Type u}
    (t₁ t₂ : StigmergicTrace α) :
    (t₁.append t₂).length = t₁.length + t₂.length := by
  induction t₁ with
  | empty => simp [StigmergicTrace.append]
  | step id bef aft rest ih =>
    simp only [StigmergicTrace.append, StigmergicTrace.length_step, ih]
    rw [Nat.add_assoc, Nat.add_comm t₂.length 1, ← Nat.add_assoc]

/-- Выполнить одно действие: агент `agentId` применяет слово `σ` к среде `e`.
    Результат: обновлённая среда и одношаговый след. -/
def executeStep (α : Type u) (e : Environment α) (agentId : AgentId)
    (σ : UAM_Free.FreeMonoid α) : Environment α × StigmergicTrace α :=
  let newCurrent := e.apply σ
  (⟨newCurrent, e.apply⟩, .step agentId e.current newCurrent .empty)

/-- Один шаг накопления: применить действие и дописать шаг к следу. -/
def executeStepAux (α : Type u)
    (p : Environment α × StigmergicTrace α)
    (q : AgentId × UAM_Free.FreeMonoid α) :
    Environment α × StigmergicTrace α :=
  let r := executeStep α p.1 q.1 q.2
  (r.1, p.2.append r.2)

/-- Выполнить последовательность действий, накапливая след. -/
def executeSteps (α : Type u) (e : Environment α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α)) :
    Environment α × StigmergicTrace α :=
  steps.foldl (executeStepAux α) (e, .empty)

/-- После шага среда содержит результат `apply`. -/
theorem executeStep_current (α : Type u) (e : Environment α)
    (agentId : AgentId) (σ : UAM_Free.FreeMonoid α) :
    (executeStep α e agentId σ).1.current = e.apply σ := rfl

/-- Одношаговый след имеет длину 1. -/
theorem executeStep_trace_length (α : Type u) (e : Environment α)
    (agentId : AgentId) (σ : UAM_Free.FreeMonoid α) :
    (executeStep α e agentId σ).2.length = 1 := rfl

/-- Пустой список действий = тождественное выполнение. -/
theorem executeSteps_nil (α : Type u) (e : Environment α) :
    executeSteps α e [] = (e, .empty) := rfl

/-- Обобщённая лемма: длина накопленного следа = длина исходного следа плюс
    число шагов. -/
theorem executeStepAux_foldl_length (α : Type u)
    (steps : List (AgentId × UAM_Free.FreeMonoid α)) :
    ∀ (e : Environment α) (t : StigmergicTrace α),
      (steps.foldl (executeStepAux α) (e, t)).2.length
        = t.length + steps.length := by
  induction steps with
  | nil => intro e t; simp
  | cons hd tl ih =>
    intro e t
    simp only [List.foldl_cons]
    rw [ih]
    simp only [executeStepAux, StigmergicTrace.length_append,
      executeStep_trace_length, List.length_cons]
    rw [Nat.add_assoc, Nat.add_comm tl.length 1, ← Nat.add_assoc]

/-- Длина следа после выполнения = количеству шагов. -/
theorem executeSteps_trace_length (α : Type u) (e : Environment α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α)) :
    (executeSteps α e steps).2.length = steps.length := by
  simp only [executeSteps]
  rw [executeStepAux_foldl_length]
  simp

end UAM_RSIA
