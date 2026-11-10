import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_MyhillNerode
import RequestProject.Atlas.UAM_RSIA_Protocol

set_option autoImplicit false

/-!
# RSIA — аттрактор протокола (Задача E)
-/

namespace UAM_RSIA

open Classical

universe u

/-- Аттрактор протокола `P` — канонический DFA языка протокола.
    Целевой язык `L = Protocol.language P`.  Аттрактор единствен и минимален
    по теории Майхилла–Нероуда. -/
noncomputable def Protocol.attractor (α : Type u) (P : Protocol α) :
    UAM_DFAEval.DFA α (UAM_MyhillNerode.NerodeClass (P.language)) :=
  UAM_MyhillNerode.canonicalDFA (P.language)

/-- Аттрактор распознаёт язык протокола. -/
theorem Protocol.attractor_language (α : Type u) (P : Protocol α) :
    (P.attractor α).language = P.language :=
  UAM_MyhillNerode.canonicalDFA_language (P.language)

end UAM_RSIA
