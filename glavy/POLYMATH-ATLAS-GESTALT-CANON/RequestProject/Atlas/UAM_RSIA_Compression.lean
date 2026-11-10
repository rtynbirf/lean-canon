import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_MinimalDFA
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Verification
import RequestProject.Atlas.UAM_RSIA_Session
import RequestProject.Atlas.UAM_RSIA_VerifyTrace
import RequestProject.Atlas.UAM_RSIA_VerifiedConstruction
import RequestProject.Atlas.UAM_RSIA_AntiEntropy

set_option autoImplicit false

/-!
# RSIA — компрессия (Задача F, Phase 3)

Phase 3 сжимает верифицированный результат Construction на двух уровнях:

* **Уровень слов.** *Nerode-сохраняющее* сжатие `compress` (каждое слово `w`
  Нероуд-эквивалентно своему сжатию `compress w`) сохраняет согласованность
  стигмергической трассы (`StigmergicTrace.aligned`) и членство в языке.
* **Уровень DFA.** Аттрактор сессии минимизируется факторизацией по отношению
  Нероуда на состояниях (`UAM_MinimalDFA.minimalDFA`): получаем приведённый DFA,
  распознающий тот же язык.

Всё дискретно — никакого анализа.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- Сжатие `compress` *сохраняет Нероуд-класс* относительно языка `L`, если
    каждое слово `w` Нероуд-эквивалентно своему сжатию `compress w`.  Это
    дискретное условие «сжатие без потери информации о принадлежности `L`». -/
def NerodePreserving (L : Set (UAM_Free.FreeMonoid α))
    (compress : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) : Prop :=
  ∀ w, UAM_RegularLanguages.nerodeRel L w (compress w)

/-- Nerode-сохраняющее сжатие не меняет членство слова в языке. -/
theorem nerodePreserving_mem_language (L : Set (UAM_Free.FreeMonoid α))
    (compress : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hNP : NerodePreserving L compress) (w : UAM_Free.FreeMonoid α) :
    (w ∈ L) = (compress w ∈ L) :=
  nerode_mem_language L w (compress w) (hNP w)

/-- Симметричная форма: сжатие Нероуд-эквивалентно исходному слову. -/
theorem nerodePreserving_symm_step (L : Set (UAM_Free.FreeMonoid α))
    (compress : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hNP : NerodePreserving L compress) (w : UAM_Free.FreeMonoid α) :
    UAM_RegularLanguages.nerodeRel L (compress w) w :=
  UAM_RegularLanguages.nerodeRel_symm L w (compress w) (hNP w)

/-- Применение сжатия `compress` к каждому шагу трассы (к `before` и `after`). -/
def StigmergicTrace.compressMap
    (compress : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) :
    StigmergicTrace α → StigmergicTrace α
  | .empty => .empty
  | .step id bef aft rest =>
      .step id (compress bef) (compress aft)
        (StigmergicTrace.compressMap compress rest)

/-- Сжатие пустой трассы — пустая трасса. -/
theorem StigmergicTrace.compressMap_empty
    (compress : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) :
    StigmergicTrace.compressMap compress (.empty : StigmergicTrace α) = .empty :=
  rfl

/-- Сжатие шага: сжимаются `before`/`after`, остаток сжимается рекурсивно. -/
theorem StigmergicTrace.compressMap_step
    (compress : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (id : AgentId) (bef aft : UAM_Free.FreeMonoid α)
    (rest : StigmergicTrace α) :
    StigmergicTrace.compressMap compress (.step id bef aft rest)
      = .step id (compress bef) (compress aft)
          (StigmergicTrace.compressMap compress rest) :=
  rfl

/-- **Ключевая теорема Phase 3.** Nerode-сохраняющее сжатие сохраняет
    согласованность трассы: если трасса `t` согласована с `L`, то её сжатие
    `t.compressMap compress` также согласовано.

    Доказательство — индукция по `t`; на шаге собираем цепочку Нероуд:
    `compress bef ~ bef ~ aft ~ compress aft`. -/
theorem StigmergicTrace.aligned_compressMap
    (L : Set (UAM_Free.FreeMonoid α))
    (compress : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hNP : NerodePreserving L compress)
    (t : StigmergicTrace α)
    (h : StigmergicTrace.aligned L t) :
    StigmergicTrace.aligned L (StigmergicTrace.compressMap compress t) := by
  induction t with
  | empty => exact .empty
  | step id bef aft rest ih =>
    cases h with
    | step hN hR =>
      rw [StigmergicTrace.compressMap_step]
      refine .step ?_ (ih hR)
      -- compress bef ~ bef ~ aft ~ compress aft
      have h1 : UAM_RegularLanguages.nerodeRel L (compress bef) bef :=
        nerodePreserving_symm_step L compress hNP bef
      have h2 : UAM_RegularLanguages.nerodeRel L (compress bef) aft :=
        UAM_RegularLanguages.nerodeRel_trans L (compress bef) bef aft h1 hN
      exact UAM_RegularLanguages.nerodeRel_trans L (compress bef) aft (compress aft)
        h2 (hNP aft)

/-! ### §. DFA-уровень: минимизация аттрактора -/

/-- Минимальный аттрактор сессии: аттрактор (канонический DFA языка протокола),
    минимизированный факторизацией по отношению Нероуда на состояниях. -/
noncomputable def Session.minimalAttractor (s : Session α) :
    UAM_DFAEval.DFA α
      (Quotient (UAM_DFAHomomorphism.stateNerodeSetoid s.attractor)) :=
  UAM_MinimalDFA.minimalDFA s.attractor

/-- Минимальный аттрактор распознаёт язык протокола сессии. -/
theorem Session.minimalAttractor_language (s : Session α) :
    (s.minimalAttractor).language = s.protocolLanguage := by
  rw [Session.minimalAttractor, UAM_MinimalDFA.minimalDFA_language,
    Session.attractor_language]

/-- Минимальный аттрактор приведён: нет двух различных Нероуд-эквивалентных
    состояний. -/
theorem Session.minimalAttractor_reduced (s : Session α)
    (S₁ S₂ : Quotient (UAM_DFAHomomorphism.stateNerodeSetoid s.attractor))
    (h : UAM_DFAHomomorphism.stateNerodeRel (s.minimalAttractor) S₁ S₂) :
    S₁ = S₂ :=
  UAM_MinimalDFA.minimalDFA_reduced s.attractor S₁ S₂ h

/-! ### §. Антиэнтропийный цикл с сохранением Нероуд-класса -/

/-- Nerode-сохраняющий цикл сжатия относительно языка `L`: функция сжатия,
    которая одновременно уменьшает представление и сохраняет Нероуд-класс. -/
structure NerodePreservingCycle (α : Type u)
    (L : Set (UAM_Free.FreeMonoid α)) where
  /-- Функция сжатия состояния. -/
  compress : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α
  /-- Сжатие сохраняет Нероуд-класс относительно `L`. -/
  preserving : NerodePreserving L compress

/-- Nerode-сохраняющий цикл не меняет членство слова в языке. -/
theorem NerodePreservingCycle.preserves_language
    {L : Set (UAM_Free.FreeMonoid α)}
    (C : NerodePreservingCycle α L) (w : UAM_Free.FreeMonoid α) :
    (w ∈ L) = (C.compress w ∈ L) :=
  nerodePreserving_mem_language L C.compress C.preserving w

/-- Nerode-сохраняющий цикл сохраняет согласованность трассы. -/
theorem NerodePreservingCycle.preserves_aligned
    {L : Set (UAM_Free.FreeMonoid α)}
    (C : NerodePreservingCycle α L) (t : StigmergicTrace α)
    (h : StigmergicTrace.aligned L t) :
    StigmergicTrace.aligned L (StigmergicTrace.compressMap C.compress t) :=
  StigmergicTrace.aligned_compressMap L C.compress C.preserving t h

end UAM_RSIA
