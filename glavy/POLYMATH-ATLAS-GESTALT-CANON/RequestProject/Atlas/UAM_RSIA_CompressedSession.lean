import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_DFAEval
import RequestProject.Atlas.UAM_DFAHomomorphism
import RequestProject.Atlas.UAM_MinimalDFA
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Session
import RequestProject.Atlas.UAM_RSIA_VerifyTrace
import RequestProject.Atlas.UAM_RSIA_VerifiedConstruction
import RequestProject.Atlas.UAM_RSIA_Compression

set_option autoImplicit false

/-!
# RSIA — сжатая сессия (Задача G, Phase 3)

`CompressedSession` — итог фазы Compression: верифицированный результат
Construction (`VerifiedConstruction`) вместе с *минимизированным* аттрактором
(приведённый DFA языка протокола) и доказательством, что он распознаёт тот же
язык.  Файл также содержит мост в фазу 4 (Arbitration).
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- Сжатая сессия: верифицированный результат Construction, минимизированный
    аттрактор (приведённый DFA) и доказательство совпадения языка. -/
structure CompressedSession (α : Type u) where
  /-- Верифицированный результат фазы Construction/Verification. -/
  verified : VerifiedConstruction α
  /-- Сжатый (минимизированный) DFA-аттрактор. -/
  compressedDFA : UAM_DFAEval.DFA α
      (Quotient (UAM_DFAHomomorphism.stateNerodeSetoid verified.session.attractor))
  /-- Сжатый DFA распознаёт язык протокола сессии. -/
  language_eq : compressedDFA.language = verified.protocolLanguage

/-- Построить сжатую сессию из верифицированного результата: минимизировать его
    аттрактор через `Session.minimalAttractor`. -/
noncomputable def VerifiedConstruction.toCompressedSession
    (v : VerifiedConstruction α) : CompressedSession α where
  verified := v
  compressedDFA := v.session.minimalAttractor
  language_eq := v.session.minimalAttractor_language

/-- Сжатый DFA сжатой сессии распознаёт язык протокола. -/
theorem CompressedSession.compressedDFA_language (cs : CompressedSession α) :
    cs.compressedDFA.language = cs.verified.protocolLanguage :=
  cs.language_eq

/-- Сжатый DFA приведён: нет двух различных Нероуд-эквивалентных состояний. -/
theorem CompressedSession.compressedDFA_reduced
    (cs : CompressedSession α)
    (S₁ S₂ : Quotient
      (UAM_DFAHomomorphism.stateNerodeSetoid cs.verified.session.attractor))
    (h : UAM_DFAHomomorphism.stateNerodeRel
        cs.verified.session.minimalAttractor S₁ S₂) :
    S₁ = S₂ :=
  cs.verified.session.minimalAttractor_reduced S₁ S₂ h

/-- Сжатие трассы верифицированного результата Nerode-сохраняющим циклом. -/
def CompressedSession.compressTrace (cs : CompressedSession α)
    (C : NerodePreservingCycle α cs.verified.protocolLanguage) :
    StigmergicTrace α :=
  StigmergicTrace.compressMap C.compress cs.verified.trace

/-- Сжатие трассы сохраняет её согласованность с языком протокола. -/
theorem CompressedSession.compressTrace_aligned (cs : CompressedSession α)
    (C : NerodePreservingCycle α cs.verified.protocolLanguage) :
    StigmergicTrace.aligned cs.verified.protocolLanguage
      (cs.compressTrace C) :=
  C.preserves_aligned cs.verified.trace cs.verified.aligned

/-- Пустое сжатие трассы (пустая трасса всегда согласована). -/
theorem CompressedSession.compressTrace_empty (cs : CompressedSession α)
    (C : NerodePreservingCycle α cs.verified.protocolLanguage)
    (h : cs.verified.trace = .empty) :
    cs.compressTrace C = .empty := by
  rw [CompressedSession.compressTrace, h, StigmergicTrace.compressMap_empty]

/-! ### §. Мост в фазу 4 (Arbitration) -/

/-- Мост в фазу 4: перевести сессию сжатого результата в фазу Arbitration.
    Протокол, среда и агенты сохраняются, меняется лишь фаза. -/
def CompressedSession.toArbitration (cs : CompressedSession α) : Session α :=
  { cs.verified.session with phase := .arbitration }

/-- После `toArbitration` сессия находится в фазе Arbitration. -/
theorem CompressedSession.toArbitration_phase (cs : CompressedSession α) :
    (cs.toArbitration).phase = .arbitration :=
  rfl

/-- `toArbitration` не меняет протокол сессии. -/
theorem CompressedSession.toArbitration_protocol (cs : CompressedSession α) :
    (cs.toArbitration).protocol = cs.verified.session.protocol :=
  rfl

/-- `toArbitration` не меняет язык протокола. -/
theorem CompressedSession.toArbitration_protocolLanguage
    (cs : CompressedSession α) :
    (cs.toArbitration).protocolLanguage = cs.verified.protocolLanguage :=
  rfl

end UAM_RSIA
