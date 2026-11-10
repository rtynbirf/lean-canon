import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_SelfReference
import RequestProject.Atlas.UAM_RSIA_Witness_Halting

set_option autoImplicit false

/-!
# Run 33 Track B: a conditional self-reference witness

The bridge exposes every hypothesis of the existing second-incompleteness
statement.  The operational system remains an explicit parameter of the proposition-level toy.
-/

namespace UAM_RSIA

open Arithmetic_Godel2

universe u
variable {α : Type u}

/-- A proposition-level toy attached to an operational system. -/
structure ToySelfRefModel (α : Type u) where
  system : HierarchicalParallelSystem α
  godelSentence : Prop
  toyConsistency : Prop
  toyConsistent : toyConsistency

/-- A bridge to the project's abstract derivability conditions. -/
structure ToySelfRefEmbedding (α : Type u) (toy : ToySelfRefModel α) where
  derivability : DerivabilityConditions
  fixedPoint : DerivabilityConditions.IsGodelSentence derivability
    toy.godelSentence
  consistent : DerivabilityConditions.Consistent derivability
  consistency_eq :
    DerivabilityConditions.ConsistencyStatement derivability =
      toy.toyConsistency
  formalMind : RSIAIsFormalMind toy.system

/-- The bridged theory cannot prove its internal consistency statement. -/
theorem toy_selfref_barrier_under_embedding
    (toy : ToySelfRefModel α)
    (emb : ToySelfRefEmbedding α toy) :
    ¬ emb.derivability.Provable
      (DerivabilityConditions.ConsistencyStatement emb.derivability) := by
  exact DerivabilityConditions.second_incompleteness emb.derivability
    toy.godelSentence emb.fixedPoint emb.consistent

/-- A concrete proposition-level toy, parameterized by an operational system. -/
def toySelfRefFin4 (system : HierarchicalParallelSystem (Fin 4)) :
    ToySelfRefModel (Fin 4) where
  system := system
  godelSentence := True
  toyConsistency := True
  toyConsistent := True.intro


end UAM_RSIA
