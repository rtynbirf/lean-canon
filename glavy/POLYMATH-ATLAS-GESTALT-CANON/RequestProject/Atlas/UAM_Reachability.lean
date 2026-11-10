import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe

/-!
# UAM — Layer 1: Достижимость (Reachability)

Канонические определения множеств достижимости `reach` (правое) и
`reachLeft` (левое). `reach a` — множество правых кратных `a`,
`reachLeft a` — множество левых кратных `a`.
-/

namespace UAM_Reachability
universe u

open UAM_Directionality

/-- Правая достижимость: множество правых кратных `a`. -/
def reach {M : Type u} [Monoid M] (a : M) : Set M := {b | algLe a b}

/-- Левая достижимость: множество левых кратных `a`. -/
def reachLeft {M : Type u} [Monoid M] (a : M) : Set M := {b | ∃ c : M, c * a = b}

end UAM_Reachability
