import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Verification

set_option autoImplicit false

/-!
# RSIA — верификация трассы (Задача D, Phase 2)

Индуктивный предикат `StigmergicTrace.aligned L t`: весь стигмергический след `t`
согласован с языком `L` — каждый шаг `(before, after)` сохраняет
Нероуд-эквивалентность.  Это НЕ то же, что `ActionAligned L w σ`
(= `nerodeRel L w (w ++ σ)`): `aligned` работает с парами `(before, after)`
из трассы, `ActionAligned` — с парой `(state, action)`.  Связь между ними
даёт `ActionAligned.aligned_step`.
-/

namespace UAM_RSIA

universe u

variable {α : Type u}

/-- След полностью согласован с языком `L`: каждый шаг сохраняет
    Нероуд-эквивалентность `before`/`after`. -/
inductive StigmergicTrace.aligned
    (L : Set (UAM_Free.FreeMonoid α)) :
    StigmergicTrace α → Prop where
  /-- Пустой след согласован. -/
  | empty : StigmergicTrace.aligned L .empty
  /-- Шаг согласован, если `before`/`after` Нероуд-эквивалентны и остаток согласован. -/
  | step {agentId before after rest}
      (hN : UAM_RegularLanguages.nerodeRel L before after)
      (hR : StigmergicTrace.aligned L rest) :
      StigmergicTrace.aligned L (.step agentId before after rest)

/-- Пустой след всегда согласован. -/
theorem StigmergicTrace.aligned_empty (L : Set (UAM_Free.FreeMonoid α)) :
    StigmergicTrace.aligned L (.empty : StigmergicTrace α) :=
  .empty

/-- Одношаговый след согласован тогда и только тогда, когда `before`/`after`
    Нероуд-эквивалентны. -/
theorem StigmergicTrace.aligned_single (L : Set (UAM_Free.FreeMonoid α))
    (agentId : AgentId) (before after : UAM_Free.FreeMonoid α)
    (hN : UAM_RegularLanguages.nerodeRel L before after) :
    StigmergicTrace.aligned L (.step agentId before after .empty) :=
  .step hN .empty

/-- Конкатенация согласованных следов согласована. -/
theorem StigmergicTrace.aligned_append (L : Set (UAM_Free.FreeMonoid α))
    (t₁ t₂ : StigmergicTrace α)
    (h₁ : StigmergicTrace.aligned L t₁)
    (h₂ : StigmergicTrace.aligned L t₂) :
    StigmergicTrace.aligned L (t₁.append t₂) := by
  induction t₁ with
  | empty => simpa only [StigmergicTrace.append] using h₂
  | step id bef aft rest ih =>
    cases h₁ with
    | step hN hR =>
      simp only [StigmergicTrace.append]
      exact .step hN (ih hR)

/-- Если конкатенация согласована, левая часть согласована. -/
theorem StigmergicTrace.aligned_append_left (L : Set (UAM_Free.FreeMonoid α))
    (t₁ t₂ : StigmergicTrace α)
    (h : StigmergicTrace.aligned L (t₁.append t₂)) :
    StigmergicTrace.aligned L t₁ := by
  induction t₁ with
  | empty => exact .empty
  | step id bef aft rest ih =>
    simp only [StigmergicTrace.append] at h
    cases h with
    | step hN hR => exact .step hN (ih hR)

/-- Если левая часть и конкатенация согласованы, правая часть согласована. -/
theorem StigmergicTrace.aligned_append_right (L : Set (UAM_Free.FreeMonoid α))
    (t₁ t₂ : StigmergicTrace α)
    (h : StigmergicTrace.aligned L (t₁.append t₂)) :
    StigmergicTrace.aligned L t₂ := by
  induction t₁ with
  | empty => simpa only [StigmergicTrace.append] using h
  | step id bef aft rest ih =>
    simp only [StigmergicTrace.append] at h
    cases h with
    | step hN hR => exact ih hR

/-- Для одношагового следа: согласованность равносильна Нероуд-эквивалентности. -/
theorem StigmergicTrace.aligned_iff_stepNerode (L : Set (UAM_Free.FreeMonoid α))
    (agentId : AgentId) (before after : UAM_Free.FreeMonoid α) :
    StigmergicTrace.aligned L (.step agentId before after .empty)
      ↔ UAM_RegularLanguages.nerodeRel L before after := by
  constructor
  · intro h
    cases h with
    | step hN _ => exact hN
  · intro hN
    exact .step hN .empty

/-- Связь `ActionAligned` и `aligned`: если действие `σ` согласовано из
    состояния `w` (`ActionAligned L w σ`), то одношаговый след с `before = w`,
    `after = w ++ σ` согласован. -/
theorem ActionAligned.aligned_step (L : Set (UAM_Free.FreeMonoid α))
    (agentId : AgentId) (w σ : UAM_Free.FreeMonoid α)
    (h : ActionAligned L w σ) :
    StigmergicTrace.aligned L (.step agentId w (w ++ σ) .empty) :=
  .step h .empty

/-- Нероуд-эквивалентные слова имеют одинаковое членство в языке `L`. -/
theorem nerode_mem_language (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ : UAM_Free.FreeMonoid α)
    (h : UAM_RegularLanguages.nerodeRel L w₁ w₂) :
    (w₁ ∈ L) = (w₂ ∈ L) := by
  have := h []
  simpa only [List.append_nil] using this

end UAM_RSIA
