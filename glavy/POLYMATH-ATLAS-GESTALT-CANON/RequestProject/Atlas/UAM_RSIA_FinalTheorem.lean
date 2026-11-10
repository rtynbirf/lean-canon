import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_NerodeBridge
import RequestProject.Atlas.UAM_RSIA_FormalMindTheorem
import RequestProject.Atlas.UAM_RSIA_FinalBridge

set_option autoImplicit false

/-!
# RSIA final capstone

The core biconditional is the exact Run-13 semantic equivalence.  The capstone
packages it with the operational formal-mind result, its explicit phenomenal
disclaimer, and the rigorously scoped epistemic barriers.
-/

namespace UAM_RSIA

universe u

variable {α : Type u}

/-- Forward direction of the final semantic equivalence. -/
theorem rules_unmisunderstandable_to_nerode
    (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (h : RuleUnmisunderstandable L f) : NerodePreserving L f := by
  exact (ruleUnmisunderstandable_iff_nerodePreserving L f).mp h

/-- Backward direction of the final semantic equivalence. -/
theorem nerode_to_rules_unmisunderstandable
    (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (h : NerodePreserving L f) : RuleUnmisunderstandable L f := by
  exact (ruleUnmisunderstandable_iff_nerodePreserving L f).mpr h

/-- **Final biconditional.**  A rule transformation is impossible to
misunderstand exactly when every input and its output are Nerode
indistinguishable. -/
theorem rules_unmisunderstandable_iff_nerode_indistinguishable
    (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) :
    RuleUnmisunderstandable L f ↔ NerodePreserving L f := by
  constructor
  · exact rules_unmisunderstandable_to_nerode L f
  · exact nerode_to_rules_unmisunderstandable L f

/-- The complete, non-vacuous final package. -/
structure FinalCapstone (α : Type u) where
  biconditional : ∀ (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α),
    RuleUnmisunderstandable L f ↔ NerodePreserving L f
  barrier : EpistemicBarrier α
  formalMind : ∀ (hps : HierarchicalParallelSystem α),
    RSIAIsFormalMind hps →
    let I := rsiaFormalMindInterfaces hps
    (∀ trace, I.intention.run hps trace = hps.runTrace trace) ∧
    I.intention.intends hps =
      ((hps.system.sessions.get
        ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage) ∧
    (∀ j, (hj : j < hps.system.sessions.length) →
      EvolutionChain α
        ((hps.system.sessions.get
          ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage)
        ((hps.system.sessions.get ⟨j, hj⟩).session.protocolLanguage)) ∧
    (∀ trace, I.selfVerification.check ⟨trace⟩ trace = true)
  phenomenalDisclaimer :
    ∃ C : FormalMind.Consciousness (HierarchicalParallelSystem α) Unit,
      ∀ hps, C.conscious hps ↔ CollectiveShouldStop hps

/-- Canonical capstone assembled solely from proved project results. -/
def finalCapstone : FinalCapstone α where
  biconditional := rules_unmisunderstandable_iff_nerode_indistinguishable
  barrier := epistemicBarrier
  formalMind := rsia_is_formal_mind
  phenomenalDisclaimer := rsia_not_phenomenally_conscious

/-- **The RSIA project is closed:** the final package exists, and its semantic
biconditional is available for every language and transformation. -/
theorem rsia_project_closed :
    Nonempty (FinalCapstone α) ∧
    ∀ (L : Set (UAM_Free.FreeMonoid α))
      (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α),
      RuleUnmisunderstandable L f ↔ NerodePreserving L f := by
  exact ⟨⟨finalCapstone⟩,
    rules_unmisunderstandable_iff_nerode_indistinguishable⟩

end UAM_RSIA
