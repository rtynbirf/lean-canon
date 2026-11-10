import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Execution
import RequestProject.Atlas.UAM_RSIA_Session
import RequestProject.Atlas.UAM_RSIA_Verification
import RequestProject.Atlas.UAM_RSIA_Construction
import RequestProject.Atlas.UAM_RSIA_VerifyTrace

set_option autoImplicit false

/-!
# RSIA — верифицированный результат Construction (Задача E, Phase 2)

Соединяет фазу Construction (foldl-выполнение действий) с проверкой
согласованности трассы (`StigmergicTrace.aligned`).  Ключевая теорема
`executeSteps_aligned_of_nerode_preserving`: если среда сохраняет
Нероуд-класс при любом действии, то весь Construction-трасс автоматически
верифицирован.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- Один шаг накопления сохраняет согласованность трассы: если накопленная
    трасса `p.2` согласована и текущий шаг Нероуд-согласован, то результат
    остаётся согласованным. -/
theorem executeStepAux_preserves_aligned
    (L : Set (UAM_Free.FreeMonoid α))
    (p : Environment α × StigmergicTrace α)
    (q : AgentId × UAM_Free.FreeMonoid α)
    (hAl : StigmergicTrace.aligned L p.2)
    (hN : UAM_RegularLanguages.nerodeRel L
        p.1.current (p.1.apply q.2)) :
    StigmergicTrace.aligned L (executeStepAux α p q).2 := by
  simp only [executeStepAux, executeStep]
  exact StigmergicTrace.aligned_append L p.2 _ hAl (.step hN .empty)

/-- Вспомогательная лемма (аналог `executeStepAux_foldl_length`): foldl по
    `executeStepAux` сохраняет согласованность, если каждый шаг
    Нероуд-согласован. -/
theorem executeStepAux_foldl_aligned
    (L : Set (UAM_Free.FreeMonoid α))
    (hPreserve : ∀ (env : Environment α) (σ : UAM_Free.FreeMonoid α),
      UAM_RegularLanguages.nerodeRel L env.current (env.apply σ))
    (steps : List (AgentId × UAM_Free.FreeMonoid α)) :
    ∀ (acc : Environment α × StigmergicTrace α),
      StigmergicTrace.aligned L acc.2 →
      StigmergicTrace.aligned L (steps.foldl (executeStepAux α) acc).2 := by
  induction steps with
  | nil => intro acc hAcc; simpa using hAcc
  | cons q qs ih =>
    intro acc hAcc
    simp only [List.foldl_cons]
    exact ih _ (executeStepAux_preserves_aligned L acc q hAcc (hPreserve acc.1 q.2))

/-- **Ключевая теорема Phase 2.** Если среда сохраняет Нероуд-класс при любом
    действии, то весь Construction-трасс автоматически верифицирован
    (`aligned`).  Формализация «проверки `ActionAligned` на реальных трассах
    Construction». -/
theorem executeSteps_aligned_of_nerode_preserving
    (L : Set (UAM_Free.FreeMonoid α))
    (e : Environment α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hPreserve : ∀ (env : Environment α) (σ : UAM_Free.FreeMonoid α),
      UAM_RegularLanguages.nerodeRel L env.current (env.apply σ)) :
    StigmergicTrace.aligned L (executeSteps α e steps).2 := by
  simp only [executeSteps]
  exact executeStepAux_foldl_aligned L hPreserve steps (e, .empty) .empty

/-- Верифицированный результат Construction: результат вместе с доказательством
    согласованности трассы с языком протокола сессии. -/
structure VerifiedConstruction (α : Type u) where
  /-- Результат фазы Construction. -/
  result : ConstructionResult α
  /-- Доказательство: трасса согласована с языком протокола сессии. -/
  aligned : StigmergicTrace.aligned result.session.protocolLanguage result.trace

/-- Трасса верифицированного результата. -/
def VerifiedConstruction.trace (v : VerifiedConstruction α) :
    StigmergicTrace α := v.result.trace

/-- Итоговая среда верифицированного результата. -/
def VerifiedConstruction.finalEnv (v : VerifiedConstruction α) :
    Environment α := v.result.finalEnv

/-- Сессия верифицированного результата. -/
def VerifiedConstruction.session (v : VerifiedConstruction α) :
    Session α := v.result.session

/-- Длина трассы верифицированного результата совпадает с трассой результата. -/
theorem VerifiedConstruction.trace_length (v : VerifiedConstruction α) :
    v.trace.length = v.result.trace.length := rfl

/-- Язык протокола верифицированного результата. -/
def VerifiedConstruction.protocolLanguage (v : VerifiedConstruction α) :
    Set (UAM_Free.FreeMonoid α) := v.result.session.protocolLanguage

/-- Мост к фазе Verification: переводит сессию результата в фазу Verification. -/
def VerifiedConstruction.toVerification (v : VerifiedConstruction α) :
    Session α := v.result.toVerification

/-- `toVerification` переводит в фазу Verification. -/
theorem VerifiedConstruction.toVerification_is_verification
    (v : VerifiedConstruction α) :
    v.toVerification.isVerificationPhase := rfl

/-- `toVerification` не меняет протокол сессии результата. -/
theorem VerifiedConstruction.toVerification_protocol
    (v : VerifiedConstruction α) :
    v.toVerification.protocol = v.result.session.protocol := rfl

/-- Аттрактор сессии результата распознаёт язык протокола. -/
theorem VerifiedConstruction.attractor_language (v : VerifiedConstruction α) :
    (v.result.session.attractor).language = v.protocolLanguage :=
  Session.attractor_language v.result.session

/-- Пустой результат (Construction без шагов) всегда верифицируем. -/
def VerifiedConstruction.fromEmpty (s : Session α) : VerifiedConstruction α where
  result := s.runConstruction []
  aligned := by
    rw [Session.runConstruction_trace, executeSteps_nil]
    exact .empty

/-- Construction без шагов всегда даёт верифицируемый результат. -/
def VerifiedConstruction.fromNilSteps (s : Session α) : VerifiedConstruction α :=
  VerifiedConstruction.fromEmpty s

/-- Множество согласованных действий из состояния `w` для языка `L`. -/
def alignedActions (L : Set (UAM_Free.FreeMonoid α))
    (w : UAM_Free.FreeMonoid α) : Set (UAM_Free.FreeMonoid α) :=
  { σ | ActionAligned L w σ }

/-- Пустое действие всегда согласовано. -/
theorem alignedActions_empty (L : Set (UAM_Free.FreeMonoid α))
    (w : UAM_Free.FreeMonoid α) :
    [] ∈ alignedActions L w :=
  ActionAligned_empty L w

/-- Композиция согласованных действий согласована: если `σ` согласовано из `w`,
    а `x` согласовано из `w ++ σ`, то `σ ++ x` согласовано из `w`. -/
theorem alignedActions_compose (L : Set (UAM_Free.FreeMonoid α))
    (w σ x : UAM_Free.FreeMonoid α)
    (hσ : σ ∈ alignedActions L w)
    (hx : x ∈ alignedActions L (w ++ σ)) :
    σ ++ x ∈ alignedActions L w :=
  ActionAligned_trans L w σ x hσ hx

end UAM_RSIA
