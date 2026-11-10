import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RSIA_Agent

set_option autoImplicit false

/-!
# RSIA — протоколы (Задача C)
-/

namespace UAM_RSIA

universe u

/-- Правило протокола: пара «текущее состояние — допустимое следующее состояние». -/
def ProtocolRule (α : Type u) :=
  UAM_Free.FreeMonoid α × UAM_Free.FreeMonoid α

/-- Протокол: набор допустимых переходов. -/
structure Protocol (α : Type u) where
  /-- Множество допустимых правил протокола. -/
  rules : Set (ProtocolRule α)

/-- Слово допустимо протоколом, если каждое его пошаговое расширение
    соответствует некоторому правилу. -/
inductive ProtocolCompliance {α : Type u} (P : Protocol α) :
    UAM_Free.FreeMonoid α → Prop where
  /-- Пустое слово всегда допустимо. -/
  | empty : ProtocolCompliance P []
  /-- Расширение допустимого слова на один символ по правилу протокола. -/
  | step {w : UAM_Free.FreeMonoid α} {a : α} (h : ProtocolCompliance P w)
      (h_rule : (w, a :: w) ∈ P.rules) :
      ProtocolCompliance P (a :: w)

/-- Язык протокола = множество всех допустимых слов.  Это и есть целевой
    язык `L`: аттрактор протокола — канонический DFA этого языка. -/
def Protocol.language {α : Type u} (P : Protocol α) :
    Set (UAM_Free.FreeMonoid α) :=
  { w | ProtocolCompliance P w }

end UAM_RSIA
