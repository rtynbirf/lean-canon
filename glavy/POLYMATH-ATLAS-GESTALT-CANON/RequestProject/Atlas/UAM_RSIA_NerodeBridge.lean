import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Verification
import RequestProject.Atlas.UAM_RSIA_Session
import RequestProject.Atlas.UAM_RSIA_Compression
import RequestProject.Atlas.UAM_RSIA_Cycle
import RequestProject.Atlas.UAM_RSIA_System

set_option autoImplicit false

/-!
# RSIA: Nerode equivalence and unambiguous rules

This file states the semantic bridge behind the slogan that a rule is
"impossible to misunderstand" precisely when applying it does not change the
Nerode class.  Thus every continuation makes the same protocol-membership
decision before and after the rule is applied.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- A rule is impossible to misunderstand relative to `L` when its application
leaves every word in the same Nerode class.  Equivalently, every continuation
has the same language-membership outcome before and after applying the rule. -/
def RuleUnmisunderstandable (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) : Prop :=
  ∀ w, UAM_RegularLanguages.nerodeRel L w (f w)

/-- Being impossible to misunderstand is exactly the existing
`NerodePreserving` invariant. -/
theorem ruleUnmisunderstandable_iff_nerodePreserving
    (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) :
    RuleUnmisunderstandable L f ↔ NerodePreserving L f := by
  rfl

/-- An action is understood at `w` when taking it does not change the Nerode
class of `w`.  This gives the semantic reading of `ActionAligned`. -/
def ActionUnderstood (L : Set (UAM_Free.FreeMonoid α))
    (w σ : UAM_Free.FreeMonoid α) : Prop :=
  ActionAligned L w σ

/-- An agent understands the rules of a session when every action in its
capability is understood at the current protocol state. -/
def Agent.understandsRules (agent : Agent α) (s : Session α) : Prop :=
  ∀ action ∈ agent.capability,
    ActionUnderstood s.protocolLanguage s.environment.current action

/-- Understanding all available rules is exactly Nerode compatibility. -/
theorem agent_understandsRules_iff_isNerodeCompatible
    (agent : Agent α) (s : Session α) :
    agent.understandsRules s ↔ agent.isNerodeCompatible s := by
  rfl

/-- Semantic name for the session-wide environment invariant: every possible
environment/action pair preserves the protocol's Nerode class. -/
def Environment.preservesUnmisunderstanding (s : Session α) : Prop :=
  ∀ (env : Environment α) (σ : UAM_Free.FreeMonoid α),
    UAM_RegularLanguages.nerodeRel s.protocolLanguage
      env.current (env.apply σ)

/-- An environment preserves unambiguous interpretation exactly when it is
Nerode-preserving in the RSIA cycle. -/
theorem environment_preserves_unmisunderstanding (s : Session α) :
    Environment.preservesUnmisunderstanding s ↔
      Environment.isNerodePreserving s := by
  rfl

/-- If every active agent understands all of its rules, the engine's stopping
condition holds. -/
theorem rules_impossible_to_misunderstand_preserves_language
    (st : RSIAState α)
    (hAllUnderstand : ∀ agent ∈ st.session.agents,
      agent.understandsRules st.session) :
    st.ShouldStop := by
  intro agent hAgent
  exact (agent_understandsRules_iff_isNerodeCompatible agent st.session).mp
    (hAllUnderstand agent hAgent)

/-- A fork is precisely an interpretation conflict: some continuation makes
main and branch states disagree about membership in the protocol language. -/
theorem forkCondition_is_interpretation_conflict
    (L : Set (UAM_Free.FreeMonoid α))
    (mainState branchState : UAM_Free.FreeMonoid α) :
    ForkCondition α L mainState branchState ↔
      ∃ v, (mainState ++ v ∈ L) ≠ (branchState ++ v ∈ L) := by
  unfold ForkCondition UAM_RegularLanguages.nerodeRel
  push_neg
  rfl

/-- Nerode compatibility says exactly that no continuation can distinguish the
two states by its protocol-language membership decision. -/
theorem nerode_compatible_no_conflict
    (L : Set (UAM_Free.FreeMonoid α))
    (mainState branchState : UAM_Free.FreeMonoid α) :
    UAM_RegularLanguages.nerodeRel L mainState branchState ↔
      ∀ v, (mainState ++ v ∈ L) = (branchState ++ v ∈ L) := by
  rfl

end UAM_RSIA
