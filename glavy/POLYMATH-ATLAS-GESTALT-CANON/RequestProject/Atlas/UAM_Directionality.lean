import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# UAM — Layer 0: Направленность (Directionality)

Каноническое определение алгебраического предпорядка `algLe`.
`algLe a b` означает, что `b` достижимо из `a` умножением справа:
существует `c` такое, что `a * c = b`.
-/

namespace UAM_Directionality
universe u

/-- Алгебраический предпорядок: `b` — правое кратное `a`. -/
def algLe {M : Type u} [Monoid M] (a b : M) : Prop := ∃ c : M, a * c = b

end UAM_Directionality
