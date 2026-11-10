import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_MyhillNerode

set_option autoImplicit false

/-!
# RSIA — целевой язык и аттрактор (Задача 0.0)

Этот файл решает блокер «кто задаёт `L`»: целевой язык выводится из протокола
(см. `UAM_RSIA_Protocol` / `UAM_RSIA_Attractor`), а аттрактор — это канонический
DFA этого языка.  Здесь мы фиксируем базовые определения на уровне произвольного
языка `L`.
-/

namespace UAM_RSIA

open Classical

universe u

/-- Целевой язык протокола: множество всех слов, допустимых протоколом.
    Формально — просто множество слов свободного моноида. -/
def TargetLanguage (α : Type u) := Set (UAM_Free.FreeMonoid α)

/-- Аттрактор для целевого языка `L` — это канонический DFA
    (`UAM_MyhillNerode.canonicalDFA`).  Аттрактор единствен
    (минимальный DFA, теория Майхилла–Нероуда) и минимален по числу состояний. -/
noncomputable def rsiaAttractor (α : Type u) (L : TargetLanguage α) :
    UAM_DFAEval.DFA α (UAM_MyhillNerode.NerodeClass L) :=
  UAM_MyhillNerode.canonicalDFA L

/-- Аттрактор распознаёт целевой язык. -/
theorem rsiaAttractor_language (α : Type u) (L : TargetLanguage α) :
    (rsiaAttractor α L).language = L :=
  UAM_MyhillNerode.canonicalDFA_language L

end UAM_RSIA
