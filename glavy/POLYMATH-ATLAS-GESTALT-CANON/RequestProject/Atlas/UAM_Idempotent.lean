import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# UAM — Layer 0: Идемпотенты (Idempotent)

Каноническое определение идемпотентного элемента.
-/

namespace UAM_Idempotent
universe u

/-- Элемент идемпотентен, если `a * a = a`. -/
def IsIdempotent {M : Type u} [Monoid M] (a : M) : Prop := a * a = a

end UAM_Idempotent
