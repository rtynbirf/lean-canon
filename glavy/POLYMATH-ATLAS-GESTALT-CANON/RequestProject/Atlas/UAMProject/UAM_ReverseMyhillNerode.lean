import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Free
import RequestProject.Atlas.UAMProject.UAM_Congruence
import RequestProject.Atlas.UAMProject.UAM_Morphism
import RequestProject.Atlas.UAMProject.UAM_DFAEval
import RequestProject.Atlas.UAMProject.UAM_RegularLanguages
import RequestProject.Atlas.UAMProject.UAM_Action
import RequestProject.Atlas.UAMProject.UAM_TransitionMonoid

namespace UAMP_ReverseMyhillNerode
universe u

open UAMP_Morphism UAMP_DFAEval UAMP_TransitionMonoid UAMP_Congruence
open UAMP_RegularLanguages hiding DFA evalFrom eval accepts language

variable {α Q : Type u} [DecidableEq Q] (A : DFA α Q)

/-- The action homomorphism's kernel is contained in the syntactic relation
of the DFA's language. -/
theorem actionHom_kernel_subset_syntacticRel :
    ∀ u v : UAMP_Free.FreeMonoid α, (actionHom A).toFun u = (actionHom A).toFun v →
      syntacticRel (language A) u v := by
  intro u v h a b
  have key : eval A (a ++ u) = eval A (a ++ v) := by
    rw [eval_concat, eval_concat]
    exact congrFun h (eval A a)
  have hb : eval A (a ++ u ++ b) = eval A (a ++ v ++ b) := by
    rw [eval_concat A (a ++ u) b, eval_concat A (a ++ v) b, key]
  show eval A (a ++ u ++ b) ∈ A.F ↔ eval A (a ++ v ++ b) ∈ A.F
  rw [hb]

/-- Surjection from the free monoid onto the syntactic monoid -/
def syntacticSurjection :
    MonoidMorphism (UAMP_Free.FreeMonoid α) (SyntacticMonoid (language A)) :=
  syntacticMorphism (language A)

/-- Syntactic morphism is surjective -/
theorem syntacticSurjection_surjective :
    Function.Surjective (syntacticSurjection A).toFun :=
  fun q => Quotient.inductionOn q (fun w => ⟨w, rfl⟩)

/-- Обратная теорема Майхилла–Нероуда: если язык распознаётся ДКА с конечным
множеством состояний, то его синтаксический моноид конечен.
(В архиве доказательство отсутствовало.) -/
theorem finite_syntacticMonoid_of_dfa [Finite Q] :
    Finite (SyntacticMonoid (language A)) := by
  have hwd : ∀ u v : UAMP_Free.FreeMonoid α,
      (congruenceSetoid (actionCongruence A)).r u v →
      mk (syntacticCongruence (language A)) u = mk (syntacticCongruence (language A)) v :=
    fun u v h => Quotient.sound (actionHom_kernel_subset_syntacticRel A u v h)
  refine Finite.of_surjective
    (@Quotient.lift (UAMP_Free.FreeMonoid α) (SyntacticMonoid (language A))
      (congruenceSetoid (actionCongruence A))
      (fun w => mk (syntacticCongruence (language A)) w) hwd) ?_
  intro y
  induction y using Quotient.inductionOn with
  | _ w => exact ⟨Quotient.mk _ w, rfl⟩

end UAMP_ReverseMyhillNerode
