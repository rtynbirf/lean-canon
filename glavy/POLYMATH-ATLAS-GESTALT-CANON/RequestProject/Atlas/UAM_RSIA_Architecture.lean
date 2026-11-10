import Mathlib

set_option autoImplicit false

namespace UAM_RSIA.Architecture

/- Architectural inventory of every non-aggregator Lean module in `RequestProject`.
   Entries are module filenames; comments record purpose, declarations, direct imports, and status. -/

/-- Layer 1; 4 modules. -/
abbrev Layer1_Base_Foundations : Array String := #[
  -- File: Arithmetic_Foundations.lean
  -- Purpose: foundational model and constitutional vocabulary; key declarations: Term, Formula, godelNumber, godelNumber_injective, ArithmetizedSyntax, DiagonalTheory.
  -- Imports from: ReclaimedTheorems.lean.
  -- Imported by: Arithmetic_Godel2.lean, Arithmetic_Rice.lean, Arithmetic_Simulation.lean, Arithmetic_Truth.lean.
  -- Status: ACTIVE.
  "Arithmetic_Foundations.lean",
  -- File: ModelLadder.lean
  -- Purpose: foundational model and constitutional vocabulary; key declarations: State, L0State, L0Transform, L0Action, L0Consciousness, L0Qualia.
  -- Imports from: UAM_Action.lean, UAM_MonoidAction.lean, UAM_Morphism.lean, UAM_Congruence.lean, UAM_Ideal.lean, UAM_Cayley.lean, FormalMindEngineering.lean, FormalMind_Interrelations.lean, UAM_ActionModelBridge.lean, UnifiedModel.lean.
  -- Imported by: GreenAnatomy.lean.
  -- Status: ACTIVE.
  "ModelLadder.lean",
  -- File: ReclaimedTheorems.lean
  -- Purpose: foundational model and constitutional vocabulary; key declarations: ArithmetizedSyntax, diagonal_lemma, DiagonalTheory, DefinesTruth, truth_undefinability, DerivabilityConditions.
  -- Imports from: IdealAI_Countermodels.lean.
  -- Imported by: Arithmetic_Foundations.lean.
  -- Status: ACTIVE.
  "ReclaimedTheorems.lean",
  -- File: Stubs_Core.lean
  -- Purpose: foundational model and constitutional vocabulary; key declarations: CannotDistinguish, CannotDistinguishAGI, CannotDistinguishHuman, CrossVerification, CurrentMode, FactCheck.
  -- Imports from: IdealAI.lean.
  -- Imported by: FormalMind_Interrelations.lean, Stubs_OpenProblems.lean.
  -- Status: ACTIVE (historical name; imported by downstream modules).
  "Stubs_Core.lean"
]

/-- Layer 2; 7 modules. -/
abbrev Layer2_Arithmetic : Array String := #[
  -- File: Arithmetic_Godel2.lean
  -- Purpose: arithmetic, computability, or ideal-system theory; key declarations: DerivabilityConditions, Consistent, ConsistencyStatement, IsGodelSentence, second_incompleteness.
  -- Imports from: Arithmetic_Foundations.lean.
  -- Imported by: UAM_RSIA_SelfReference.lean.
  -- Status: ACTIVE.
  "Arithmetic_Godel2.lean",
  -- File: Arithmetic_Rice.lean
  -- Purpose: arithmetic, computability, or ideal-system theory; key declarations: ProgramExtEq, PartialComputableEnumeration, ExtensionalProperty, SemanticallyNontrivial, rice_theorem.
  -- Imports from: Arithmetic_Foundations.lean.
  -- Imported by: ActionBridges.lean, UAM_RSIA_HaltingBarrier.lean, UAM_RSIA_PhenomenalUnprovability.lean, UAM_RSIA_Undecidability.lean, UAM_RSIA_Witness_Fin4.lean.
  -- Status: ACTIVE.
  "Arithmetic_Rice.lean",
  -- File: Arithmetic_Simulation.lean
  -- Purpose: arithmetic, computability, or ideal-system theory; key declarations: every_observer_test_agrees, simulation_indistinguishability.
  -- Imports from: Arithmetic_Foundations.lean, IdealAI_Countermodels.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "Arithmetic_Simulation.lean",
  -- File: Arithmetic_Truth.lean
  -- Purpose: arithmetic, computability, or ideal-system theory; key declarations: DefinesTruth, tarski_undefinability.
  -- Imports from: Arithmetic_Foundations.lean.
  -- Imported by: UAM_RSIA_PhenomenalUnprovability.lean.
  -- Status: ACTIVE.
  "Arithmetic_Truth.lean",
  -- File: IdealAI.lean
  -- Purpose: arithmetic, computability, or ideal-system theory; key declarations: ComputeMode, InteractionMode, TransparencyLevel, Vocabulary, CreativeRecombination, SemanticGraph.
  -- Imports from: FormalMindEngineering.lean.
  -- Imported by: FormalMind_Interrelations.lean, Stubs_Core.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "IdealAI.lean",
  -- File: IdealAI_Countermodels.lean
  -- Purpose: arithmetic, computability, or ideal-system theory; key declarations: System, Phi, Integrated, phi_implies_integration, PersistentSelf, IsCopy.
  -- Imports from: Mathlib or no project-local modules.
  -- Imported by: Arithmetic_Simulation.lean, ReclaimedTheorems.lean.
  -- Status: ACTIVE.
  "IdealAI_Countermodels.lean",
  -- File: Stubs_OpenProblems.lean
  -- Purpose: arithmetic, computability, or ideal-system theory; key declarations: AccessConsciousness, CognitiveLoad, PhenomenalConsciousness, Relation, OpenAxiomSet, OpenAxiomSet.consciousness.
  -- Imports from: Stubs_Core.lean.
  -- Imported by: FormalMind_Interrelations.lean.
  -- Status: ACTIVE (historical name; imported by downstream modules).
  "Stubs_OpenProblems.lean"
]

/-- Layer 3; 4 modules. -/
abbrev Layer3_FormalMind : Array String := #[
  -- File: FormalMindEngineering.lean
  -- Purpose: formal-mind concepts and bridges; key declarations: Concept, Concept.rank, Concept.dependencies, dependency_rank_lt, Approximation, Approximation.Equivalent.
  -- Imports from: Mathlib or no project-local modules.
  -- Imported by: ActionBridges.lean, FormalMindInterrelationships.lean, FormalMind_Interrelations.lean, IdealAI.lean, ModelLadder.lean, UAMFormalMindBridge.lean, UAM_ActionModelBridge.lean, UAM_RSIA_CognitiveBridge.lean, UAM_RSIA_CognitiveSynthesis.lean, UAM_RSIA_FormalMindTheorem.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "FormalMindEngineering.lean",
  -- File: FormalMindInterrelationships.lean
  -- Purpose: formal-mind concepts and bridges; key declarations: ConceptModel, DependsOn, dependsOn_rank_lt, realized_of_dependsOn, no_concept_dependency_cycle, allConcepts.
  -- Imports from: FormalMindEngineering.lean.
  -- Imported by: UAMFormalMindBridge.lean, UnifiedModel.lean.
  -- Status: SUSPECTED_DUPLICATE (name overlap; distinct declarations).
  "FormalMindInterrelationships.lean",
  -- File: FormalMind_Interrelations.lean
  -- Purpose: formal-mind concepts and bridges; key declarations: Knowledge, ConfidenceCalibrated, uncertainty, uncertainty_eq_zero_of_confidence_one, metacognition_strengthens_consciousness, creativity_understanding_value.
  -- Imports from: FormalMindEngineering.lean, IdealAI.lean, Stubs_Core.lean, Stubs_OpenProblems.lean.
  -- Imported by: ModelLadder.lean, UAM_RSIA_FormalMindTheorem.lean, UnifiedModel.lean.
  -- Status: SUSPECTED_DUPLICATE (name overlap; distinct declarations).
  "FormalMind_Interrelations.lean",
  -- File: UAMFormalMindBridge.lean
  -- Purpose: formal-mind concepts and bridges; key declarations: SubjectActionModel, one_preserves_state, sequential_actions, ExtensionalEquality, extensionalEquality_iff_kernel, extensionalEquality_context.
  -- Imports from: FormalMindEngineering.lean, FormalMindInterrelationships.lean, UAM_MonoidAction.lean, UAM_Congruence.lean, UAM_Ideal.lean, UAM_Cayley.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAMFormalMindBridge.lean"
]

/-- Layer 4; 57 modules. -/
abbrev Layer4_UAM_Core : Array String := #[
  -- File: ActionBridges.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: StateLabeling, labelingKernel, labelingKernel_refl, labelingKernel_symm, labelingKernel_trans, labelingActionCongruence.
  -- Imports from: UAM_Green.lean, UAM_MonoidAction.lean, UAM_Submonoid.lean, UAM_Congruence.lean, UAM_Ideal.lean, UAM_Semilattice.lean, UnifiedModel.lean, UAM_Idempotent.lean, Arithmetic_Rice.lean, FormalMindEngineering.lean, UAM_ActionCongruence.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "ActionBridges.lean",
  -- File: GreenAnatomy.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: State, funImage, funKernel, funKernel_id_eq_diagonal, funKernel_constant_eq_total, funImage_id_eq_full.
  -- Imports from: ModelLadder.lean, UAM_Green.lean, UAM_Idempotent.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "GreenAnatomy.lean",
  -- File: UAM_Action.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: instMonoid, mul_def, mul_apply, one_def, one_apply.
  -- Imports from: Mathlib or no project-local modules.
  -- Imported by: ModelLadder.lean, UAM_AutomatonStops.lean, UAM_DFAHomomorphism.lean, UAM_MonoidAction.lean, UAM_TransitionMonoid.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "UAM_Action.lean",
  -- File: UAM_ActionCongruence.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: ActionCongruence, mkActionCongruence, actionCongruenceSetoid, ActionQuotient, quotientProj, inducedAction.
  -- Imports from: UAM_MonoidAction.lean.
  -- Imported by: ActionBridges.lean.
  -- Status: ACTIVE.
  "UAM_ActionCongruence.lean",
  -- File: UAM_ActionModelBridge.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: ActionModel, one_preserves_state, sequential_actions, Reachable, orbit_eq_reachable, action_preserves_proposed_goal.
  -- Imports from: FormalMindEngineering.lean, UAM_MonoidAction.lean, UAM_Congruence.lean, UAM_Ideal.lean, UAM_Semilattice.lean, UAM_Directionality.lean, UAM_Cayley.lean, UAM_Morphism.lean.
  -- Imported by: ModelLadder.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "UAM_ActionModelBridge.lean",
  -- File: UAM_AutomatonStops.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IdempotentAction, repeatedWord, StabilizesAt, dfa_transition_monoid_has_idempotent, actionHom_repeatedWord, action_stabilizes.
  -- Imports from: UAM_Idempotent.lean, UAM_Directionality.lean, UAM_Reachability.lean, UAM_Cayley.lean, UAM_Morphism.lean, UAM_Action.lean, UAM_DFAEval.lean, UAM_TransitionMonoid.lean, UAM_Beginning.lean, UAM_FiniteSemigroup.lean, UAM_RegularLanguages.lean, UAM_ReverseMyhillNerode.lean.
  -- Imported by: UAM_Thesis.lean.
  -- Status: ACTIVE.
  "UAM_AutomatonStops.lean",
  -- File: UAM_Beginning.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsBeginningStructure, IsInfiniteFlow, cayley_kills_beginning, finite_forces_idempotent, finite_beginning_impossible, no_beginning_has_local_unit.
  -- Imports from: UAM_Idempotent.lean, UAM_Directionality.lean, UAM_Reachability.lean, UAM_Cayley.lean, UAM_Morphism.lean, UAM_Submonoid.lean, UAM_FiniteSemigroup.lean.
  -- Imported by: UAM_AutomatonStops.lean, UAM_Thesis.lean.
  -- Status: ACTIVE.
  "UAM_Beginning.lean",
  -- File: UAM_BigPicture.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: uam_closed_under_constructions, unity_of_layers.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Reachability.lean, UAM_Green.lean, UAM_Group.lean, UAM_Submonoid.lean, UAM_HClass.lean, UAM_Regular.lean, UAM_Schutzenberger.lean, UAM_ReesMatrix.lean, UAM_Congruence.lean, UAM_Morphism.lean, UAM_Ideal.lean, UAM_Inverse.lean, UAM_Free.lean, UAM_Semilattice.lean, UAM_DirectProduct.lean, UAM_Presentation.lean, UAM_CompletelyRegular.lean, UAM_Extension.lean, UAM_Representation.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_BigPicture.lean",
  -- File: UAM_Cayley.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: Transform, instMonoid, rho, rho_one, rho_injective, cayley_embedding.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Group.lean, UAM_Morphism.lean.
  -- Imported by: ModelLadder.lean, UAMFormalMindBridge.lean, UAM_ActionModelBridge.lean, UAM_AutomatonStops.lean, UAM_Beginning.lean, UAM_MonoidAction.lean, UAM_Thesis.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "UAM_Cayley.lean",
  -- File: UAM_Center.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsCentral, center, centralizer, mem_center_iff, one_central, mul_central.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Group.lean, UAM_Submonoid.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_Center.lean",
  -- File: UAM_CognitiveDFA.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: CognitiveModel, cognitiveToDFA, cognitive_evalFrom, cognitive_model_dfa_equiv, cognitiveOfUnified, cognitiveOfUnified_transition.
  -- Imports from: UAM_Free.lean, UAM_DFAEval.lean, UAM_MonoidAction.lean, UnifiedModel.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_CognitiveDFA.lean",
  -- File: UAM_CompletelyRegular.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsCompletelyRegular, IsCompletelyRegularSemigroup, completely_regular_imp_regular, unit_completely_regular, idempotent_completely_regular, regular_zero_completely_regular.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Regular.lean, UAM_Group.lean, UAM_Green.lean, UAM_HClass.lean, UAM_Semilattice.lean.
  -- Imported by: UAM_BigPicture.lean.
  -- Status: ACTIVE.
  "UAM_CompletelyRegular.lean",
  -- File: UAM_Congruence.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsCongruence, congruenceSetoid, QuotientMonoid, mk, instMonoid, mk_mul.
  -- Imports from: UAM_Directionality.lean, UAM_Green.lean, UAM_Idempotent.lean.
  -- Imported by: ActionBridges.lean, ModelLadder.lean, UAMFormalMindBridge.lean, UAM_ActionModelBridge.lean, UAM_BigPicture.lean, UAM_DFAEval.lean, UAM_Extension.lean, UAM_Ideal.lean, UAM_MonoidAction.lean, UAM_Morphism.lean, UAM_Presentation.lean, UAM_PresentationMorphism.lean, UAM_RegularLanguages.lean, UAM_ReverseMyhillNerode.lean, UAM_TransitionMonoid.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "UAM_Congruence.lean",
  -- File: UAM_DFAEval.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: DFA, evalFrom, eval, accepts, language, evalFrom_nil.
  -- Imports from: UAM_Free.lean, UAM_Congruence.lean, UAM_Morphism.lean.
  -- Imported by: UAM_AutomatonStops.lean, UAM_CognitiveDFA.lean, UAM_DFAHomomorphism.lean, UAM_EpsilonNFA.lean, UAM_Kleene.lean, UAM_KleeneCounterexample.lean, UAM_NFA.lean, UAM_RSIA_CompressedSession.lean, UAM_RegularLanguages.lean, UAM_ReverseMyhillNerode.lean, UAM_Thompson.lean, UAM_TransitionMonoid.lean.
  -- Status: ACTIVE.
  "UAM_DFAEval.lean",
  -- File: UAM_DFAHomomorphism.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: DFAHom, evalFrom_map, language_eq, stateNerodeRel, stateNerodeRel_refl, stateNerodeRel_symm.
  -- Imports from: UAM_Free.lean, UAM_DFAEval.lean, UAM_RegularLanguages.lean, UAM_Action.lean, UAM_TransitionMonoid.lean, UAM_ReverseMyhillNerode.lean.
  -- Imported by: UAM_MinimalDFA.lean, UAM_RSIA_CompressedSession.lean.
  -- Status: ACTIVE.
  "UAM_DFAHomomorphism.lean",
  -- File: UAM_D_eq_J.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: finite_sandwich_data, sandwich_gives_D, J_eq_implies_D_eq_finite, D_eq_iff_J_eq_finite.
  -- Imports from: UAM_Green.lean, UAM_FiniteSemigroup.lean, UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Reachability.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_D_eq_J.lean",
  -- File: UAM_DirectProduct.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: DirectProduct, prod_one_eq, prod_mul_eq, prod_fst_mul, fstMorphism, sndMorphism.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Morphism.lean.
  -- Imported by: UAM_BigPicture.lean.
  -- Status: ACTIVE.
  "UAM_DirectProduct.lean",
  -- File: UAM_Directionality.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: algLe.
  -- Imports from: Mathlib or no project-local modules.
  -- Imported by: UAM_ActionModelBridge.lean, UAM_AutomatonStops.lean, UAM_Beginning.lean, UAM_BigPicture.lean, UAM_Cayley.lean, UAM_Center.lean, UAM_CompletelyRegular.lean, UAM_Congruence.lean, UAM_D_eq_J.lean, UAM_DirectProduct.lean, UAM_Extension.lean, UAM_FiniteSemigroup.lean, UAM_Free.lean, UAM_Group.lean, UAM_Ideal.lean, UAM_InfiniteBeginning.lean, UAM_Inverse.lean, UAM_Morphism.lean, UAM_Presentation.lean, UAM_Reachability.lean, UAM_RectangularBand.lean, UAM_Regular.lean, UAM_Representation.lean, UAM_Schutzenberger.lean, UAM_SemidirectProduct.lean, UAM_Semilattice.lean, UAM_Submonoid.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "UAM_Directionality.lean",
  -- File: UAM_EpsilonNFA.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: EpsilonNFA, epsStep, epsilonClosure, subset_closure, closure_mono, closure_idem.
  -- Imports from: UAM_Free.lean, UAM_DFAEval.lean, UAM_NFA.lean.
  -- Imported by: UAM_Kleene.lean, UAM_Thompson.lean.
  -- Status: ACTIVE.
  "UAM_EpsilonNFA.lean",
  -- File: UAM_Extension.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsExtension, extension_ideal_nonempty, extension_embedding_mem, extension_ideal_absorbs_image, extension_comp_constant, rees_factor_zero_class.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Regular.lean, UAM_Ideal.lean, UAM_Congruence.lean, UAM_Morphism.lean.
  -- Imported by: UAM_BigPicture.lean.
  -- Status: ACTIVE.
  "UAM_Extension.lean",
  -- File: UAM_FiniteSemigroup.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: pow_periodic, pow_add_mul_period, exists_idempotent_pow, exists_idempotent.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Reachability.lean.
  -- Imported by: UAM_AutomatonStops.lean, UAM_Beginning.lean, UAM_D_eq_J.lean, UAM_Thesis.lean, UAM_TrivialSettling.lean.
  -- Status: ACTIVE.
  "UAM_FiniteSemigroup.lean",
  -- File: UAM_Free.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: FreeMonoid, empty, concat, of, instMonoid, empty_ne_of.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Morphism.lean.
  -- Imported by: UAM_BigPicture.lean, UAM_CognitiveDFA.lean, UAM_DFAEval.lean, UAM_DFAHomomorphism.lean, UAM_EpsilonNFA.lean, UAM_InfiniteBeginning.lean, UAM_Kleene.lean, UAM_NFA.lean, UAM_Presentation.lean, UAM_PresentationMorphism.lean, UAM_RSIA_Agent.lean, UAM_RSIA_AntiEntropy.lean, UAM_RSIA_Arbitration.lean, UAM_RSIA_Attractor.lean, UAM_RSIA_Branch.lean, UAM_RSIA_CompressedSession.lean, UAM_RSIA_Compression.lean, UAM_RSIA_Construction.lean, UAM_RSIA_Cycle.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Execution.lean, UAM_RSIA_Exit.lean, UAM_RSIA_Iteration.lean, UAM_RSIA_Necessity.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_Parallel.lean, UAM_RSIA_PhaseRing.lean, UAM_RSIA_PhenomenalUnprovability.lean, UAM_RSIA_Protocol.lean, UAM_RSIA_ProtocolHierarchy.lean, UAM_RSIA_Session.lean, UAM_RSIA_System.lean, UAM_RSIA_TargetLanguage.lean, UAM_RSIA_Undecidability.lean, UAM_RSIA_Verification.lean, UAM_RSIA_VerifiedConstruction.lean, UAM_RSIA_VerifyTrace.lean, UAM_RSIA_Witness_Fin4.lean, UAM_RegularExpression.lean, UAM_RegularLanguages.lean, UAM_Representation.lean, UAM_ReverseMyhillNerode.lean, UAM_SemidirectProduct.lean, UAM_Thesis.lean, UAM_Thompson.lean, UAM_TransitionMonoid.lean.
  -- Status: ACTIVE.
  "UAM_Free.lean",
  -- File: UAM_Green.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: R_eq, L_eq, H_eq, TransitiveClosure, D_eq, R_subset_D.
  -- Imports from: UAM_Reachability.lean, UAM_PrincipalIdeals.lean.
  -- Imported by: ActionBridges.lean, GreenAnatomy.lean, UAM_BigPicture.lean, UAM_CompletelyRegular.lean, UAM_Congruence.lean, UAM_D_eq_J.lean, UAM_Group.lean, UAM_HClass.lean, UAM_InfiniteBeginning.lean, UAM_Inverse.lean, UAM_RectangularBand.lean, UAM_Schutzenberger.lean, UAM_Submonoid.lean.
  -- Status: ACTIVE.
  "UAM_Green.lean",
  -- File: UAM_Group.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsUnit, IsGroup, inv_unique, inv_inv, inv_mul, one_isUnit.
  -- Imports from: UAM_Directionality.lean, UAM_Green.lean.
  -- Imported by: UAM_BigPicture.lean, UAM_Cayley.lean, UAM_Center.lean, UAM_CompletelyRegular.lean, UAM_Inverse.lean, UAM_Morphism.lean, UAM_Regular.lean, UAM_TrivialSettling.lean.
  -- Status: ACTIVE.
  "UAM_Group.lean",
  -- File: UAM_HClass.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: HClass, self_mem_reach, self_mem_reachLeft, R_eq_refl, R_eq_symm, R_eq_trans.
  -- Imports from: UAM_Green.lean, UAM_Idempotent.lean.
  -- Imported by: UAM_BigPicture.lean, UAM_CompletelyRegular.lean, UAM_Schutzenberger.lean.
  -- Status: ACTIVE.
  "UAM_HClass.lean",
  -- File: UAM_Ideal.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsLeftIdeal, IsRightIdeal, IsIdeal, left_ideal_mul_mem, right_ideal_mul_mem, ideal_mul_mem.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Regular.lean, UAM_Congruence.lean, UAM_PrincipalIdeals.lean.
  -- Imported by: ActionBridges.lean, ModelLadder.lean, UAMFormalMindBridge.lean, UAM_ActionModelBridge.lean, UAM_BigPicture.lean, UAM_Extension.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "UAM_Ideal.lean",
  -- File: UAM_Idempotent.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsIdempotent.
  -- Imports from: Mathlib or no project-local modules.
  -- Imported by: ActionBridges.lean, GreenAnatomy.lean, UAM_AutomatonStops.lean, UAM_Beginning.lean, UAM_BigPicture.lean, UAM_Cayley.lean, UAM_Center.lean, UAM_CompletelyRegular.lean, UAM_Congruence.lean, UAM_D_eq_J.lean, UAM_DirectProduct.lean, UAM_Extension.lean, UAM_FiniteSemigroup.lean, UAM_Free.lean, UAM_HClass.lean, UAM_Ideal.lean, UAM_InfiniteBeginning.lean, UAM_Inverse.lean, UAM_Morphism.lean, UAM_Presentation.lean, UAM_RectangularBand.lean, UAM_Regular.lean, UAM_Representation.lean, UAM_Schutzenberger.lean, UAM_SemidirectProduct.lean, UAM_Semilattice.lean, UAM_Thesis.lean, UAM_TrivialSettling.lean.
  -- Status: ACTIVE.
  "UAM_Idempotent.lean",
  -- File: UAM_InfiniteBeginning.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsWeakBeginningStructure, empty_word_idempotent, not_idempotent_of_ne, free_monoid_weak_beginning, free_reach_ne_singleton, free_reach_empty_is_univ.
  -- Imports from: UAM_Idempotent.lean, UAM_Directionality.lean, UAM_Reachability.lean, UAM_Green.lean, UAM_Free.lean.
  -- Imported by: UAM_Thesis.lean.
  -- Status: ACTIVE.
  "UAM_InfiniteBeginning.lean",
  -- File: UAM_Inverse.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsInverse, IsInverseSemigroup, isInverse_symm, isInverse_idempotent_left, isInverse_idempotent_right, isInverse_idempotent_pair.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Regular.lean, UAM_Group.lean, UAM_Green.lean.
  -- Imported by: UAM_BigPicture.lean, UAM_Representation.lean, UAM_Semilattice.lean.
  -- Status: ACTIVE.
  "UAM_Inverse.lean",
  -- File: UAM_Kleene.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsRegularLanguage, isRegular_of_regExp, isRegular_empty_set, isRegular_empty_str, isRegular_atom, isRegular_union.
  -- Imports from: UAM_Free.lean, UAM_DFAEval.lean, UAM_NFA.lean, UAM_RegularExpression.lean, UAM_RegularLanguages.lean, UAM_EpsilonNFA.lean.
  -- Imported by: UAM_KleeneComplete.lean, UAM_KleeneCounterexample.lean.
  -- Status: ACTIVE.
  "UAM_Kleene.lean",
  -- File: UAM_KleeneComplete.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: regexToDFA, regexToDFA_language, transitionRegex, baseRegex, pathRegex, dfaRegex.
  -- Imports from: UAM_Thompson.lean, UAM_Kleene.lean, UAM_KleeneCounterexample.lean.
  -- Imported by: UAM_RSIA_Kleene.lean.
  -- Status: ACTIVE.
  "UAM_KleeneComplete.lean",
  -- File: UAM_KleeneCounterexample.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: RegExp.support, mem_support_of_mem_language, nat_univ_not_regular, universalNatDFA, universalNatDFA_language, unrestricted_kleene_statement_false.
  -- Imports from: UAM_Kleene.lean, UAM_DFAEval.lean.
  -- Imported by: UAM_KleeneComplete.lean.
  -- Status: ACTIVE.
  "UAM_KleeneCounterexample.lean",
  -- File: UAM_MinimalDFA.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: minimalDFA, minimalDFA_language, minimalDFA_reduced, instFintypeMinimalStates, myhillNerode_backward, myhillNerode_forward.
  -- Imports from: UAM_RegularLanguages.lean, UAM_ReverseMyhillNerode.lean, UAM_DFAHomomorphism.lean.
  -- Imported by: UAM_RSIA_CompressedSession.lean, UAM_RSIA_Compression.lean.
  -- Status: ACTIVE.
  "UAM_MinimalDFA.lean",
  -- File: UAM_MonoidAction.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: MonoidAction, act_mul_apply, toMorphism, canonical, canonical_eq_cayley, orbit.
  -- Imports from: UAM_Action.lean, UAM_Morphism.lean, UAM_Cayley.lean, UAM_TransitionMonoid.lean, UAM_Congruence.lean.
  -- Imported by: ActionBridges.lean, ModelLadder.lean, UAMFormalMindBridge.lean, UAM_ActionCongruence.lean, UAM_ActionModelBridge.lean, UAM_CognitiveDFA.lean, UAM_SemidirectProduct.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "UAM_MonoidAction.lean",
  -- File: UAM_Morphism.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: MonoidMorphism, kernel, range, map_idempotent, map_isUnit, comp.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Group.lean, UAM_Regular.lean, UAM_Congruence.lean.
  -- Imported by: ModelLadder.lean, UAM_ActionModelBridge.lean, UAM_AutomatonStops.lean, UAM_Beginning.lean, UAM_BigPicture.lean, UAM_Cayley.lean, UAM_DFAEval.lean, UAM_DirectProduct.lean, UAM_Extension.lean, UAM_Free.lean, UAM_MonoidAction.lean, UAM_Presentation.lean, UAM_PresentationMorphism.lean, UAM_RegularLanguages.lean, UAM_Representation.lean, UAM_ReverseMyhillNerode.lean, UAM_SemidirectProduct.lean, UAM_Thesis.lean, UAM_TransitionMonoid.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "UAM_Morphism.lean",
  -- File: UAM_MyhillNerode.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: languageNerodeSetoid, NerodeClass, nerodeRel_append_left, nerodeTransition, canonicalDFA, canonicalDFA_evalFrom.
  -- Imports from: UAM_RegularLanguages.lean.
  -- Imported by: UAM_RSIA_Attractor.lean, UAM_RSIA_Session.lean, UAM_RSIA_TargetLanguage.lean, UAM_RSIA_Verification.lean.
  -- Status: ACTIVE.
  "UAM_MyhillNerode.lean",
  -- File: UAM_NFA.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: NFA, stepSet, evalSet, reachableFrom, reachable, nfaAccepts.
  -- Imports from: UAM_Free.lean, UAM_DFAEval.lean.
  -- Imported by: UAM_EpsilonNFA.lean, UAM_Kleene.lean.
  -- Status: ACTIVE.
  "UAM_NFA.lean",
  -- File: UAM_Presentation.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: Relation, congruencesContaining, normalClosure, PresentedMonoid, normalClosure_minimal, normalClosure_contains_R.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Free.lean, UAM_Congruence.lean, UAM_Morphism.lean.
  -- Imported by: UAM_BigPicture.lean, UAM_PresentationMorphism.lean.
  -- Status: ACTIVE.
  "UAM_Presentation.lean",
  -- File: UAM_PresentationMorphism.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: letterMap, inducedRaw, inducedRaw_kills, presentedMap, presentedMap_mk, presentedMap_of.
  -- Imports from: UAM_Free.lean, UAM_Congruence.lean, UAM_Morphism.lean, UAM_Presentation.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_PresentationMorphism.lean",
  -- File: UAM_PrincipalIdeals.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: principalLeft, principalRight, principalIdeal.
  -- Imports from: Mathlib or no project-local modules.
  -- Imported by: UAM_Green.lean, UAM_Ideal.lean.
  -- Status: ACTIVE.
  "UAM_PrincipalIdeals.lean",
  -- File: UAM_Reachability.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: reach, reachLeft.
  -- Imports from: UAM_Directionality.lean.
  -- Imported by: UAM_AutomatonStops.lean, UAM_Beginning.lean, UAM_BigPicture.lean, UAM_D_eq_J.lean, UAM_FiniteSemigroup.lean, UAM_Green.lean, UAM_InfiniteBeginning.lean.
  -- Status: ACTIVE.
  "UAM_Reachability.lean",
  -- File: UAM_RectangularBand.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: RectangularBand, instMul, mul_def, instSemigroup, sg_idempotent, rectangular_identity.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Green.lean, UAM_Regular.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_RectangularBand.lean",
  -- File: UAM_ReesMatrix.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: ReesMatrix, zero, mul, zero_mul, mul_zero, mul_none.
  -- Imports from: Mathlib or no project-local modules.
  -- Imported by: UAM_BigPicture.lean.
  -- Status: ACTIVE.
  "UAM_ReesMatrix.lean",
  -- File: UAM_Regular.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsZero, IsRegular, regulars, rightStabilizer, leftStabilizer, unit_is_regular.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Group.lean.
  -- Imported by: UAM_BigPicture.lean, UAM_CompletelyRegular.lean, UAM_Extension.lean, UAM_Ideal.lean, UAM_Inverse.lean, UAM_Morphism.lean, UAM_RectangularBand.lean, UAM_Schutzenberger.lean.
  -- Status: ACTIVE.
  "UAM_Regular.lean",
  -- File: UAM_RegularExpression.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: RegExp, languageOf, nil_mem_empty_str, nil_mem_star, of_mem_atom, concat_mem.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean.
  -- Imported by: UAM_Kleene.lean, UAM_Thompson.lean.
  -- Status: ACTIVE.
  "UAM_RegularExpression.lean",
  -- File: UAM_RegularLanguages.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsRightInvariant, StabilizedBy, kernel_right_invariant, nerodeRel, nerodeRel_refl, nerodeRel_symm.
  -- Imports from: UAM_Free.lean, UAM_Congruence.lean, UAM_Morphism.lean, UAM_DFAEval.lean.
  -- Imported by: UAM_AutomatonStops.lean, UAM_DFAHomomorphism.lean, UAM_Kleene.lean, UAM_MinimalDFA.lean, UAM_MyhillNerode.lean, UAM_RSIA_Arbitration.lean, UAM_RSIA_Attractor.lean, UAM_RSIA_Branch.lean, UAM_RSIA_CompressedSession.lean, UAM_RSIA_Compression.lean, UAM_RSIA_Cycle.lean, UAM_RSIA_Exit.lean, UAM_RSIA_Iteration.lean, UAM_RSIA_Necessity.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_System.lean, UAM_RSIA_TargetLanguage.lean, UAM_RSIA_Undecidability.lean, UAM_RSIA_Verification.lean, UAM_RSIA_VerifiedConstruction.lean, UAM_RSIA_VerifyTrace.lean, UAM_RSIA_Witness_Fin4.lean, UAM_RegularExpression.lean, UAM_ReverseMyhillNerode.lean.
  -- Status: ACTIVE.
  "UAM_RegularLanguages.lean",
  -- File: UAM_Representation.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: PartialBij, ext, inj_on_dom, idOn, idAll, inv.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Inverse.lean, UAM_Morphism.lean, UAM_Free.lean.
  -- Imported by: UAM_BigPicture.lean.
  -- Status: ACTIVE.
  "UAM_Representation.lean",
  -- File: UAM_ReverseMyhillNerode.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: instMonoidStateEnd, phi, phi_eq_imp_syntacticRel, kerInjection, kerInjection_injective, instFintypeKerQuotient.
  -- Imports from: UAM_Free.lean, UAM_Congruence.lean, UAM_Morphism.lean, UAM_DFAEval.lean, UAM_RegularLanguages.lean.
  -- Imported by: UAM_AutomatonStops.lean, UAM_DFAHomomorphism.lean, UAM_MinimalDFA.lean.
  -- Status: ACTIVE.
  "UAM_ReverseMyhillNerode.lean",
  -- File: UAM_Schutzenberger.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: D_rel, DClass, IsRegularSemigroup, D_rel_refl, D_rel_symm, D_rel_trans.
  -- Imports from: UAM_Directionality.lean, UAM_Green.lean, UAM_Idempotent.lean, UAM_HClass.lean, UAM_Regular.lean.
  -- Imported by: UAM_BigPicture.lean.
  -- Status: ACTIVE.
  "UAM_Schutzenberger.lean",
  -- File: UAM_SemidirectProduct.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: ScalarAction, act, act_one_left, act_mul_left, act_mul_right, act_one_right.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Morphism.lean, UAM_Free.lean, UAM_MonoidAction.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_SemidirectProduct.lean",
  -- File: UAM_Semilattice.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: IsCommutative, IsSemilattice, commutative_one, commutative_idempotent_absorb, semilattice_idempotent, semilattice_commutative.
  -- Imports from: UAM_Directionality.lean, UAM_Idempotent.lean, UAM_Inverse.lean.
  -- Imported by: ActionBridges.lean, UAM_ActionModelBridge.lean, UAM_BigPicture.lean, UAM_CompletelyRegular.lean, UnifiedModel.lean.
  -- Status: ACTIVE.
  "UAM_Semilattice.lean",
  -- File: UAM_Submonoid.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: Submonoid, mem_one, mem_mul, trivial, top, inter.
  -- Imports from: UAM_Directionality.lean, UAM_Green.lean.
  -- Imported by: ActionBridges.lean, UAM_Beginning.lean, UAM_BigPicture.lean, UAM_Center.lean, UAM_TransitionMonoid.lean.
  -- Status: ACTIVE.
  "UAM_Submonoid.lean",
  -- File: UAM_Thesis.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: thesis.
  -- Imports from: UAM_Idempotent.lean, UAM_Beginning.lean, UAM_AutomatonStops.lean, UAM_InfiniteBeginning.lean, UAM_Cayley.lean, UAM_Morphism.lean, UAM_Free.lean, UAM_FiniteSemigroup.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_Thesis.lean",
  -- File: UAM_Thompson.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: ThompsonState, instDecidableEqThompsonState, ThompsonState.all, ThompsonState.mem_all, instFintypeThompsonState, thompsonTransition.
  -- Imports from: UAM_Free.lean, UAM_RegularExpression.lean, UAM_EpsilonNFA.lean, UAM_DFAEval.lean.
  -- Imported by: UAM_KleeneComplete.lean.
  -- Status: ACTIVE.
  "UAM_Thompson.lean",
  -- File: UAM_TransitionMonoid.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: actionHom, TransitionMonoid, actionHom_eq_iff, kerInjection, kerInjection_injective, instFintypeKerQuotient.
  -- Imports from: UAM_Free.lean, UAM_Congruence.lean, UAM_Morphism.lean, UAM_Submonoid.lean, UAM_DFAEval.lean, UAM_Action.lean.
  -- Imported by: UAM_AutomatonStops.lean, UAM_DFAHomomorphism.lean, UAM_MonoidAction.lean.
  -- Status: ACTIVE.
  "UAM_TransitionMonoid.lean",
  -- File: UAM_TrivialSettling.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: HasOnlyTrivialIdempotent, HasNonTrivialIdempotent, trivial_idempotent_one, only_trivial_iff_not_nontrivial, group_has_only_trivial_idempotent, only_trivial_idempotent_of_subgroup.
  -- Imports from: UAM_Idempotent.lean, UAM_Group.lean, UAM_FiniteSemigroup.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_TrivialSettling.lean",
  -- File: UnifiedModel.lean
  -- Purpose: UAM algebra, automata, languages, and bridges; key declarations: State, Transform, initial, next, mentalAction, consciousness.
  -- Imports from: UAM_Action.lean, UAM_MonoidAction.lean, UAM_Morphism.lean, UAM_Congruence.lean, UAM_Ideal.lean, UAM_Cayley.lean, UAM_Semilattice.lean, UAM_Directionality.lean, FormalMindEngineering.lean, FormalMindInterrelationships.lean, FormalMind_Interrelations.lean, UAM_ActionModelBridge.lean, IdealAI.lean.
  -- Imported by: ActionBridges.lean, ModelLadder.lean, UAM_CognitiveDFA.lean.
  -- Status: ACTIVE.
  "UnifiedModel.lean"
]

/-- Layer 5; 39 modules, including the project aggregator. -/
abbrev Layer5_RSIA : Array String := #[
  -- File: UAM_RSIA_Agent.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: AgentId, Agent, Agent.id_ne_of_ne.
  -- Imports from: UAM_Free.lean.
  -- Imported by: UAM_RSIA_Arbitration.lean, UAM_RSIA_Branch.lean, UAM_RSIA_Construction.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Execution.lean, UAM_RSIA_Exit.lean, UAM_RSIA_Protocol.lean, UAM_RSIA_Session.lean, UAM_RSIA_System.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Agent.lean",
  -- File: UAM_RSIA_AntiEntropy.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: IsCompression, AntiEntropyCycle, compress_monotone.
  -- Imports from: UAM_Free.lean.
  -- Imported by: UAM_RSIA_Compression.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_AntiEntropy.lean",
  -- File: UAM_RSIA_Arbitration.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: ArbitrationDecision, removeAgent, removeAgent_id_absent, ForkBranch, CompressedSession.mkForkBranch, ForkBranch.branch_protocolLanguage.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_Agent.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Exit.lean, UAM_RSIA_PhaseRing.lean, UAM_RSIA_Session.lean, UAM_RSIA_CompressedSession.lean.
  -- Imported by: UAM_RSIA_Cycle.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Arbitration.lean",
  -- File: UAM_RSIA_Attractor.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: Protocol.attractor, Protocol.attractor_language.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_MyhillNerode.lean, UAM_RSIA_Protocol.lean.
  -- Imported by: UAM_RSIA_Session.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Attractor.lean",
  -- File: UAM_RSIA_Branch.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: RSIARound.fromExitFork, RSIARound.fromExitFork_language_preserved, RSIARound.fromExitFork_phase, ForkBranch.isNerodePreserving, fork_branch_preserves_source_language, fork_branch_is_construction_phase.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_Agent.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Session.lean, UAM_RSIA_Exit.lean, UAM_RSIA_Cycle.lean, UAM_RSIA_Iteration.lean.
  -- Imported by: UAM_RSIA_ForkTree.lean, UAM_RSIA_Parallel.lean, UAM_RSIA_System.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Branch.lean",
  -- File: UAM_RSIA_CognitiveBridge.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: Session.formalIntention, UnderstandingQuestion, Session.formalUnderstanding, Session.formalUnderstanding_iff, Session.formalUnderstanding_iff_actionAligned, RSIAState.formalSubjectivity.
  -- Imports from: FormalMindEngineering.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_VerifiedConstruction.lean.
  -- Imported by: UAM_RSIA_CognitiveSynthesis.lean, UAM_RSIA_FormalMindTheorem.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_CognitiveBridge.lean",
  -- File: UAM_RSIA_CognitiveSynthesis.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: HierarchicalParallelSystem.formalIntention, DistributedUnderstandingQuestion, HierarchicalParallelSystem.addressedSession, HierarchicalParallelSystem.formalUnderstanding, HierarchicalParallelSystem.formalUnderstanding_iff, HierarchicalParallelSystem.formalSubjectivity.
  -- Imports from: FormalMindEngineering.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_CognitiveBridge.lean, UAM_RSIA_Parallel.lean, UAM_RSIA_ProtocolHierarchy.lean, UAM_RSIA_Coordination.lean.
  -- Imported by: UAM_RSIA_FormalMindTheorem.lean, UAM_RSIA_SelfReference.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_CognitiveSynthesis.lean",
  -- File: UAM_RSIA_CompressedSession.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: CompressedSession, VerifiedConstruction.toCompressedSession, CompressedSession.compressedDFA_language, CompressedSession.compressedDFA_reduced, CompressedSession.compressTrace, CompressedSession.compressTrace_aligned.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_DFAEval.lean, UAM_DFAHomomorphism.lean, UAM_MinimalDFA.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Session.lean, UAM_RSIA_VerifyTrace.lean, UAM_RSIA_VerifiedConstruction.lean, UAM_RSIA_Compression.lean.
  -- Imported by: UAM_RSIA_Arbitration.lean, UAM_RSIA_Cycle.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_CompressedSession.lean",
  -- File: UAM_RSIA_Compression.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: NerodePreserving, nerodePreserving_mem_language, nerodePreserving_symm_step, StigmergicTrace.compressMap, StigmergicTrace.compressMap_empty, StigmergicTrace.compressMap_step.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_MinimalDFA.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Verification.lean, UAM_RSIA_Session.lean, UAM_RSIA_VerifyTrace.lean, UAM_RSIA_VerifiedConstruction.lean, UAM_RSIA_AntiEntropy.lean.
  -- Imported by: UAM_RSIA_CompressedSession.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_System.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Compression.lean",
  -- File: UAM_RSIA_Construction.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: ConstructionResult, Session.runConstruction, Session.runConstruction_finalEnv, Session.runConstruction_trace, Session.runConstruction_session, Session.runConstruction_trace_length.
  -- Imports from: UAM_Free.lean, UAM_RSIA_Agent.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Protocol.lean, UAM_RSIA_PhaseRing.lean, UAM_RSIA_Execution.lean, UAM_RSIA_Session.lean, UAM_RSIA_Verification.lean.
  -- Imported by: UAM_RSIA_Cycle.lean, UAM_RSIA_VerifiedConstruction.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Construction.lean",
  -- File: UAM_RSIA_Coordination.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: EvolutionChain.transport, HierarchicalParallelSystem, HierarchicalStep, HierarchicalParallelSystem.step, HierarchicalParallelSystem.runTrace, HierarchicalParallelSystem.TraceWellFormed.
  -- Imports from: UAM_RSIA_Parallel.lean, UAM_RSIA_ProtocolHierarchy.lean.
  -- Imported by: UAM_RSIA_CognitiveSynthesis.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Coordination.lean",
  -- File: UAM_RSIA_Cycle.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: Environment.isNerodePreserving, Environment.isNerodePreserving_of_protocolLanguage_eq, Session.runRSIACycleContinue, Session.runRSIACycleContinue_preserves_language, Session.runRSIACycleExitClean, Session.runRSIACycleExitClean_preserves_language.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Execution.lean, UAM_RSIA_Session.lean, UAM_RSIA_Construction.lean, UAM_RSIA_VerifiedConstruction.lean, UAM_RSIA_CompressedSession.lean, UAM_RSIA_Arbitration.lean.
  -- Imported by: UAM_RSIA_Branch.lean, UAM_RSIA_Iteration.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_System.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Cycle.lean",
  -- File: UAM_RSIA_Environment.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: Environment, StigmergicTrace, StigmergicTrace.append, StigmergicTrace.append_empty, StigmergicTrace.append_assoc.
  -- Imports from: UAM_Free.lean, UAM_RSIA_Agent.lean.
  -- Imported by: UAM_RSIA_Arbitration.lean, UAM_RSIA_Branch.lean, UAM_RSIA_CompressedSession.lean, UAM_RSIA_Compression.lean, UAM_RSIA_Construction.lean, UAM_RSIA_Cycle.lean, UAM_RSIA_Execution.lean, UAM_RSIA_Iteration.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_Session.lean, UAM_RSIA_System.lean, UAM_RSIA_VerifiedConstruction.lean, UAM_RSIA_VerifyTrace.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Environment.lean",
  -- File: UAM_RSIA_Execution.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: StigmergicTrace.length, StigmergicTrace.length_append, executeStep, executeStepAux, executeSteps, executeStep_current.
  -- Imports from: UAM_Free.lean, UAM_RSIA_Agent.lean, UAM_RSIA_Environment.lean.
  -- Imported by: UAM_RSIA_Construction.lean, UAM_RSIA_Cycle.lean, UAM_RSIA_VerifiedConstruction.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Execution.lean",
  -- File: UAM_RSIA_Exit.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: ExitDeclaration, ForkCondition, ExitStatus, exit_preserves_language.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_Agent.lean.
  -- Imported by: UAM_RSIA_Arbitration.lean, UAM_RSIA_Branch.lean, UAM_RSIA_System.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Exit.lean",
  -- File: UAM_RSIA_FinalBridge.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: EpistemicBarrier, epistemicBarrier, epistemicBarrier_components.
  -- Imports from: UAM_RSIA_Undecidability.lean, UAM_RSIA_SelfReference.lean, UAM_RSIA_HaltingBarrier.lean, UAM_RSIA_PhenomenalUnprovability.lean.
  -- Imported by: UAM_RSIA_FinalTheorem.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_FinalBridge.lean",
  -- File: UAM_RSIA_FinalTheorem.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: rules_unmisunderstandable_to_nerode, nerode_to_rules_unmisunderstandable, rules_unmisunderstandable_iff_nerode_indistinguishable, FinalCapstone, finalCapstone, rsia_project_closed.
  -- Imports from: UAM_RSIA_NerodeBridge.lean, UAM_RSIA_FormalMindTheorem.lean, UAM_RSIA_FinalBridge.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_RSIA_FinalTheorem.lean",
  -- File: UAM_RSIA_ForkTree.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: ForkTree, root, depth, leafCount, forkCount, roundCount.
  -- Imports from: UAM_RSIA_Branch.lean, UAM_RSIA_System.lean.
  -- Imported by: UAM_RSIA_Parallel.lean, UAM_RSIA_ProtocolHierarchy.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_ForkTree.lean",
  -- File: UAM_RSIA_FormalMindTheorem.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: RSIAFormalMindInterfaces, rsiaFormalMindInterfaces, RSIAIsFormalMind, rsia_is_formal_mind, rsiaConsciousness, rsia_not_phenomenally_conscious.
  -- Imports from: FormalMindEngineering.lean, FormalMind_Interrelations.lean, UAM_RSIA_CognitiveBridge.lean, UAM_RSIA_CognitiveSynthesis.lean.
  -- Imported by: UAM_RSIA_FinalTheorem.lean, UAM_RSIA_HaltingBarrier.lean, UAM_RSIA_PhenomenalUnprovability.lean, UAM_RSIA_SelfReference.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_FormalMindTheorem.lean",
  -- File: UAM_RSIA_HaltingBarrier.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: CollectiveShouldStop, HaltingInstance, HaltingInstance.Halts, RSIAHaltingSimulation, halting_problem_undecidable, rsia_shouldStop_undecidable.
  -- Imports from: UAM_RSIA_FormalMindTheorem.lean, UAM_RSIA_Undecidability.lean, UAM_RSIA_SelfReference.lean, Arithmetic_Rice.lean.
  -- Imported by: UAM_RSIA_FinalBridge.lean, UAM_RSIA_PhenomenalUnprovability.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_HaltingBarrier.lean",
  -- File: UAM_RSIA_Iteration.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: RSIARound.output_isNerodePreserving, Session.runNContinueRounds, Session.runNContinueRounds_preserves_language, Session.runNContinueRounds_isNerodePreserving, Session.runNContinueRounds_pos_phase, Session.runExitCleanSequence.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Session.lean, UAM_RSIA_Cycle.lean.
  -- Imported by: UAM_RSIA_Branch.lean, UAM_RSIA_System.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Iteration.lean",
  -- File: UAM_RSIA_Kleene.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: regex_dfa_regex_language, Session.protocolRegex, Session.protocolRegex_language, Session.thompson_kleene_complete, RSIAState.runInstructions_preserves_regex, RSIAState.thompson_kleene_complete.
  -- Imports from: UAM_KleeneComplete.lean, UAM_RSIA_System.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_RSIA_Kleene.lean",
  -- File: UAM_RSIA_Necessity.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: barrier_fails_if_all_preserve, adequate_fails_if_all_preserve, trivial_model_contradicts_barrier.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_Undecidability.lean, UAM_RSIA_Witness_Fin4.lean.
  -- Imported by: Main.lean only.
  -- Status: ACTIVE.
  "UAM_RSIA_Necessity.lean",
  -- File: UAM_RSIA_NerodeBridge.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: RuleUnmisunderstandable, ruleUnmisunderstandable_iff_nerodePreserving, of, ActionUnderstood, Agent.understandsRules, agent_understandsRules_iff_isNerodeCompatible.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Verification.lean, UAM_RSIA_Session.lean, UAM_RSIA_Compression.lean, UAM_RSIA_Cycle.lean, UAM_RSIA_System.lean.
  -- Imported by: UAM_RSIA_CognitiveBridge.lean, UAM_RSIA_CognitiveSynthesis.lean, UAM_RSIA_FinalTheorem.lean, UAM_RSIA_Undecidability.lean, UAM_RSIA_Witness_Fin4.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_NerodeBridge.lean",
  -- File: UAM_RSIA_Parallel.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: SessionLabel, ParallelSystem, ParallelStep, ParallelTrace, RSIAState.runInstruction, ParallelSystem.step.
  -- Imports from: UAM_Free.lean, UAM_RSIA_System.lean, UAM_RSIA_Branch.lean, UAM_RSIA_ForkTree.lean.
  -- Imported by: UAM_RSIA_CognitiveSynthesis.lean, UAM_RSIA_Coordination.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Parallel.lean",
  -- File: UAM_RSIA_PhaseRing.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: Phase, Phase.next, Phase.next_cycle, Phase.next_exists, Phase.next2.
  -- Imports from: UAM_Free.lean.
  -- Imported by: UAM_RSIA_Arbitration.lean, UAM_RSIA_Construction.lean, UAM_RSIA_Session.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_PhaseRing.lean",
  -- File: UAM_RSIA_PhenomenalUnprovability.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: PhenomenalConsciousnessPredicate, ObservationallyIndistinguishable, PhenomenalConsciousnessPredicate.extensional, PhenomenalConsciousnessPredicate.nontrivial, PhenomenalProgramModel, PhenomenalProgramModel.property.
  -- Imports from: UAM_Free.lean, UAM_RSIA_FormalMindTheorem.lean, UAM_RSIA_Undecidability.lean, UAM_RSIA_SelfReference.lean, UAM_RSIA_HaltingBarrier.lean, Arithmetic_Rice.lean, Arithmetic_Truth.lean.
  -- Imported by: UAM_RSIA_FinalBridge.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_PhenomenalUnprovability.lean",
  -- File: UAM_RSIA_Protocol.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: ProtocolRule, Protocol, ProtocolCompliance, Protocol.language.
  -- Imports from: UAM_Free.lean, UAM_RSIA_Agent.lean.
  -- Imported by: UAM_RSIA_Attractor.lean, UAM_RSIA_Construction.lean, UAM_RSIA_ProtocolHierarchy.lean, UAM_RSIA_Session.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Protocol.lean",
  -- File: UAM_RSIA_ProtocolHierarchy.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: Protocol.refinementPreorder, Protocol.languageEquiv, Protocol.languageSetoid, ProtocolQuotient, ProtocolQuotient.language, ProtocolQuotient.partialOrder.
  -- Imports from: UAM_Free.lean, UAM_RSIA_Protocol.lean, UAM_RSIA_ForkTree.lean.
  -- Imported by: UAM_RSIA_CognitiveSynthesis.lean, UAM_RSIA_Coordination.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_ProtocolHierarchy.lean",
  -- File: UAM_RSIA_SelfReference.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: RSIASelfReferenceModel, rsia_cannot_prove_own_consistency, rsia_main_theorem_external_only, rsia_selfReference_external_formalMind.
  -- Imports from: UAM_RSIA_System.lean, UAM_RSIA_CognitiveSynthesis.lean, UAM_RSIA_FormalMindTheorem.lean, Arithmetic_Godel2.lean.
  -- Imported by: UAM_RSIA_FinalBridge.lean, UAM_RSIA_HaltingBarrier.lean, UAM_RSIA_PhenomenalUnprovability.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_SelfReference.lean",
  -- File: UAM_RSIA_Session.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: Session, Session.protocolLanguage, Session.attractor, Session.attractor_language, Agent.canAct, Session.validStep.
  -- Imports from: UAM_Free.lean, UAM_MyhillNerode.lean, UAM_RSIA_Agent.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Protocol.lean, UAM_RSIA_PhaseRing.lean, UAM_RSIA_TargetLanguage.lean, UAM_RSIA_Attractor.lean.
  -- Imported by: UAM_RSIA_Arbitration.lean, UAM_RSIA_Branch.lean, UAM_RSIA_CompressedSession.lean, UAM_RSIA_Compression.lean, UAM_RSIA_Construction.lean, UAM_RSIA_Cycle.lean, UAM_RSIA_Iteration.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_System.lean, UAM_RSIA_VerifiedConstruction.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Session.lean",
  -- File: UAM_RSIA_System.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: RSIAConfig, RSIAConfig.reindex, RSIAConfig.compress_preserves_language, RSIAConfig.compress_monotone, RSIARound.decision, RSIARound.decision_isNerodePreserving.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_Agent.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Session.lean, UAM_RSIA_Exit.lean, UAM_RSIA_Cycle.lean, UAM_RSIA_Iteration.lean, UAM_RSIA_Branch.lean, UAM_RSIA_Compression.lean.
  -- Imported by: UAM_RSIA_ForkTree.lean, UAM_RSIA_Kleene.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_Parallel.lean, UAM_RSIA_SelfReference.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_System.lean",
  -- File: UAM_RSIA_TargetLanguage.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: TargetLanguage, rsiaAttractor, rsiaAttractor_language.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_MyhillNerode.lean.
  -- Imported by: UAM_RSIA_Session.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_TargetLanguage.lean",
  -- File: UAM_RSIA_Undecidability.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: FunctionCode, FunctionCodeModel, extEq, isNerodePreserving, isNerodePreserving_extensional, NerodeCodingAdequate.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_NerodeBridge.lean, Arithmetic_Rice.lean.
  -- Imported by: UAM_RSIA_FinalBridge.lean, UAM_RSIA_HaltingBarrier.lean, UAM_RSIA_Necessity.lean, UAM_RSIA_PhenomenalUnprovability.lean, UAM_RSIA_Witness_Fin4.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Undecidability.lean",
  -- File: UAM_RSIA_Verification.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: ActionAligned, ActionAligned_empty, ActionAligned_self, ActionAligned_trans.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_MyhillNerode.lean.
  -- Imported by: UAM_RSIA_Compression.lean, UAM_RSIA_Construction.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_VerifiedConstruction.lean, UAM_RSIA_VerifyTrace.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Verification.lean",
  -- File: UAM_RSIA_VerifiedConstruction.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: executeStepAux_preserves_aligned, executeStepAux_foldl_aligned, executeSteps_aligned_of_nerode_preserving, VerifiedConstruction, VerifiedConstruction.trace, VerifiedConstruction.finalEnv.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Execution.lean, UAM_RSIA_Session.lean, UAM_RSIA_Verification.lean, UAM_RSIA_Construction.lean, UAM_RSIA_VerifyTrace.lean.
  -- Imported by: UAM_RSIA_CognitiveBridge.lean, UAM_RSIA_CompressedSession.lean, UAM_RSIA_Compression.lean, UAM_RSIA_Cycle.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_VerifiedConstruction.lean",
  -- File: UAM_RSIA_VerifyTrace.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: StigmergicTrace.aligned, StigmergicTrace.aligned_empty, StigmergicTrace.aligned_single, StigmergicTrace.aligned_append, StigmergicTrace.aligned_append_left, StigmergicTrace.aligned_append_right.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_Environment.lean, UAM_RSIA_Verification.lean.
  -- Imported by: UAM_RSIA_CompressedSession.lean, UAM_RSIA_Compression.lean, UAM_RSIA_VerifiedConstruction.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_VerifyTrace.lean",
  -- File: UAM_RSIA_Witness_Fin4.lean
  -- Purpose: RSIA structures, dynamics, bridges, or barriers; key declarations: Fin4Program, Fin4MachineCode, Fin4Step, Fin4Run, Fin4_all_machines_halt, Fin4_machine_0_state.
  -- Imports from: UAM_Free.lean, UAM_RegularLanguages.lean, UAM_RSIA_NerodeBridge.lean, UAM_RSIA_Undecidability.lean, Arithmetic_Rice.lean.
  -- Imported by: UAM_RSIA_Necessity.lean.
  -- Status: ACTIVE.
  "UAM_RSIA_Witness_Fin4.lean",
  -- File: Main.lean
  -- Purpose: project aggregator; imports every active public module and sets global elaboration options.
  -- Imports from: all active modules listed above.
  -- Imported by: build target only.
  -- Status: ACTIVE.
  "Main.lean"
]

/-- Complete partition of the 111 pre-Run-32 project Lean files. -/
abbrev AllFiles : Array String :=
  Layer1_Base_Foundations ++ Layer2_Arithmetic ++ Layer3_FormalMind ++
    Layer4_UAM_Core ++ Layer5_RSIA

/-- Inventory cardinality, recorded without a proof command because this file is documentation-only. -/
abbrev AllFilesCount : Nat := AllFiles.size

end UAM_RSIA.Architecture
