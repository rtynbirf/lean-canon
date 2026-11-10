import Mathlib

set_option autoImplicit false

namespace UAM_RSIA.Glossary

/-- A mechanically sourced glossary. Every location below was extracted from an actual top-level declaration. -/
abbrev Entry := String × String × String × Nat × String

/-- Layer 5: 73 load-bearing terms. -/
abbrev RSIA_Core_Terms : Array Entry := #[
  ("Session", "structure", "UAM_RSIA_Session.lean", 28, "ACTIVE"),
  ("RSIAConfig", "structure", "UAM_RSIA_System.lean", 37, "ACTIVE"),
  ("RSIAState", "structure", "UAM_RSIA_System.lean", 90, "ACTIVE"),
  ("HierarchicalParallelSystem", "structure", "UAM_RSIA_Coordination.lean", 24, "ACTIVE"),
  ("FunctionCodeModel", "structure", "UAM_RSIA_Undecidability.lean", 36, "ACTIVE"),
  ("NerodeCodingAdequate", "def", "UAM_RSIA_Undecidability.lean", 66, "ACTIVE"),
  ("RSIASelfReferenceModel", "structure", "UAM_RSIA_SelfReference.lean", 28, "ACTIVE"),
  ("RSIAHaltingSimulation", "structure", "UAM_RSIA_HaltingBarrier.lean", 43, "ACTIVE"),
  ("PhenomenalProgramModel", "structure", "UAM_RSIA_PhenomenalUnprovability.lean", 54, "ACTIVE"),
  ("EpistemicBarrier", "structure", "UAM_RSIA_FinalBridge.lean", 20, "ACTIVE"),
  ("FinalCapstone", "structure", "UAM_RSIA_FinalTheorem.lean", 48, "ACTIVE"),
  ("rsia_project_closed", "theorem", "UAM_RSIA_FinalTheorem.lean", 79, "ACTIVE"),
  ("rules_unmisunderstandable_iff_nerode_indistinguishable", "theorem", "UAM_RSIA_FinalTheorem.lean", 39, "ACTIVE"),
  ("Agent", "structure", "UAM_RSIA_Agent.lean", 20, "ACTIVE"),
  ("Environment", "structure", "UAM_RSIA_Environment.lean", 16, "ACTIVE"),
  ("Protocol", "structure", "UAM_RSIA_Protocol.lean", 20, "ACTIVE"),
  ("Phase", "inductive", "UAM_RSIA_PhaseRing.lean", 13, "ACTIVE"),
  ("StigmergicTrace", "inductive", "UAM_RSIA_Environment.lean", 23, "ACTIVE"),
  ("VerifiedConstruction", "structure", "UAM_RSIA_VerifiedConstruction.lean", 79, "ACTIVE"),
  ("CompressedSession", "structure", "UAM_RSIA_CompressedSession.lean", 34, "ACTIVE"),
  ("ForkTree", "inductive", "UAM_RSIA_ForkTree.lean", 27, "ACTIVE"),
  ("AntiEntropyCycle", "structure", "UAM_RSIA_AntiEntropy.lean", 21, "ACTIVE"),
  ("ArbitrationDecision", "inductive", "UAM_RSIA_Arbitration.lean", 33, "ACTIVE"),
  ("ForkBranch", "structure", "UAM_RSIA_Arbitration.lean", 58, "ACTIVE"),
  ("ArbitrationVerdict", "structure", "UAM_RSIA_Arbitration.lean", 121, "ACTIVE"),
  ("PhaseRingConsensus", "structure", "UAM_RSIA_Arbitration.lean", 152, "ACTIVE"),
  ("ForkResult", "structure", "UAM_RSIA_Branch.lean", 167, "ACTIVE"),
  ("HierarchicalTraceCertificate", "structure", "UAM_RSIA_CognitiveSynthesis.lean", 146, "ACTIVE"),
  ("NerodePreservingCycle", "structure", "UAM_RSIA_Compression.lean", 138, "ACTIVE"),
  ("ConstructionResult", "structure", "UAM_RSIA_Construction.lean", 25, "ACTIVE"),
  ("HierarchicalParallelSystem.TraceWellFormed", "inductive", "UAM_RSIA_Coordination.lean", 65, "ACTIVE"),
  ("RSIARound", "structure", "UAM_RSIA_Cycle.lean", 102, "ACTIVE"),
  ("ExitDeclaration", "structure", "UAM_RSIA_Exit.lean", 17, "ACTIVE"),
  ("ExitStatus", "inductive", "UAM_RSIA_Exit.lean", 31, "ACTIVE"),
  ("IsLeaf", "inductive", "UAM_RSIA_ForkTree.lean", 78, "ACTIVE"),
  ("WellFormed", "inductive", "UAM_RSIA_ForkTree.lean", 93, "ACTIVE"),
  ("Path", "inductive", "UAM_RSIA_ForkTree.lean", 161, "ACTIVE"),
  ("ProtocolEvolution", "structure", "UAM_RSIA_ForkTree.lean", 221, "ACTIVE"),
  ("DynamicForkTree", "inductive", "UAM_RSIA_ForkTree.lean", 290, "ACTIVE"),
  ("IsStatic", "inductive", "UAM_RSIA_ForkTree.lean", 336, "ACTIVE"),
  ("EvolutionChain", "inductive", "UAM_RSIA_ForkTree.lean", 367, "ACTIVE"),
  ("RSIAFormalMindInterfaces", "structure", "UAM_RSIA_FormalMindTheorem.lean", 19, "ACTIVE"),
  ("HaltingInstance", "structure", "UAM_RSIA_HaltingBarrier.lean", 32, "ACTIVE"),
  ("of", "class", "UAM_RSIA_NerodeBridge.lean", 46, "ACTIVE"),
  ("ParallelSystem", "structure", "UAM_RSIA_Parallel.lean", 22, "ACTIVE"),
  ("ParallelStep", "structure", "UAM_RSIA_Parallel.lean", 28, "ACTIVE"),
  ("ParallelSystem.TraceWellFormed", "inductive", "UAM_RSIA_Parallel.lean", 61, "ACTIVE"),
  ("ProtocolCompliance", "inductive", "UAM_RSIA_Protocol.lean", 26, "ACTIVE"),
  ("RoundInstruction", "inductive", "UAM_RSIA_System.lean", 261, "ACTIVE"),
  ("CheckedForkTransition", "structure", "UAM_RSIA_System.lean", 404, "ACTIVE"),
  ("StigmergicTrace.aligned", "inductive", "UAM_RSIA_VerifyTrace.lean", 28, "ACTIVE"),
  ("ToyFunctionCodeModel", "structure", "UAM_RSIA_Witness_Fin4.lean", 84, "ACTIVE"),
  ("ToyEmbedding", "structure", "UAM_RSIA_Witness_Fin4.lean", 172, "ACTIVE"),
  ("AgentId", "def", "UAM_RSIA_Agent.lean", 16, "ACTIVE"),
  ("IsCompression", "def", "UAM_RSIA_AntiEntropy.lean", 16, "ACTIVE"),
  ("Protocol.attractor", "def", "UAM_RSIA_Attractor.lean", 23, "ACTIVE"),
  ("RSIARound.fromExitFork", "def", "UAM_RSIA_Branch.lean", 32, "ACTIVE"),
  ("Session.formalIntention", "def", "UAM_RSIA_CognitiveBridge.lean", 30, "ACTIVE"),
  ("HierarchicalParallelSystem.formalIntention", "def", "UAM_RSIA_CognitiveSynthesis.lean", 21, "ACTIVE"),
  ("NerodePreserving", "def", "UAM_RSIA_Compression.lean", 40, "ACTIVE"),
  ("EvolutionChain.transport", "def", "UAM_RSIA_Coordination.lean", 16, "ACTIVE"),
  ("Environment.isNerodePreserving", "def", "UAM_RSIA_Cycle.lean", 34, "ACTIVE"),
  ("StigmergicTrace.length", "def", "UAM_RSIA_Execution.lean", 21, "ACTIVE"),
  ("CollectiveShouldStop", "def", "UAM_RSIA_HaltingBarrier.lean", 28, "ACTIVE"),
  ("Session.runNContinueRounds", "def", "UAM_RSIA_Iteration.lean", 38, "ACTIVE"),
  ("Session.protocolRegex", "def", "UAM_RSIA_Kleene.lean", 37, "ACTIVE"),
  ("RuleUnmisunderstandable", "def", "UAM_RSIA_NerodeBridge.lean", 33, "ACTIVE"),
  ("PhenomenalConsciousnessPredicate", "def", "UAM_RSIA_PhenomenalUnprovability.lean", 32, "ACTIVE"),
  ("ProtocolRule", "def", "UAM_RSIA_Protocol.lean", 16, "ACTIVE"),
  ("Protocol.languageEquiv", "def", "UAM_RSIA_ProtocolHierarchy.lean", 28, "ACTIVE"),
  ("TargetLanguage", "def", "UAM_RSIA_TargetLanguage.lean", 25, "ACTIVE"),
  ("ActionAligned", "def", "UAM_RSIA_Verification.lean", 25, "ACTIVE"),
  ("Fin4MachineCode", "def", "UAM_RSIA_Witness_Fin4.lean", 33, "ACTIVE")
]

/-- Layer 4: 54 load-bearing terms. -/
abbrev Layer4_UAM_Core_Terms : Array Entry := #[
  ("DFA", "structure", "UAM_DFAEval.lean", 29, "ACTIVE"),
  ("NFA", "structure", "UAM_NFA.lean", 25, "ACTIVE"),
  ("RegExp", "inductive", "UAM_RegularExpression.lean", 20, "ACTIVE"),
  ("nerodeRel", "def", "UAM_RegularLanguages.lean", 86, "ACTIVE"),
  ("canonicalDFA", "def", "UAM_MyhillNerode.lean", 52, "ACTIVE"),
  ("StateLabeling", "structure", "ActionBridges.lean", 23, "ACTIVE"),
  ("funImage", "def", "GreenAnatomy.lean", 28, "ACTIVE"),
  ("ActionCongruence", "structure", "UAM_ActionCongruence.lean", 13, "ACTIVE"),
  ("ActionModel", "structure", "UAM_ActionModelBridge.lean", 29, "ACTIVE"),
  ("IdempotentAction", "def", "UAM_AutomatonStops.lean", 47, "ACTIVE"),
  ("IsBeginningStructure", "def", "UAM_Beginning.lean", 56, "ACTIVE"),
  ("Transform", "structure", "UAM_Cayley.lean", 37, "ACTIVE"),
  ("IsCentral", "def", "UAM_Center.lean", 28, "ACTIVE"),
  ("CognitiveModel", "structure", "UAM_CognitiveDFA.lean", 19, "ACTIVE"),
  ("IsCompletelyRegular", "def", "UAM_CompletelyRegular.lean", 36, "ACTIVE"),
  ("IsCongruence", "structure", "UAM_Congruence.lean", 22, "ACTIVE"),
  ("DFAHom", "structure", "UAM_DFAHomomorphism.lean", 35, "ACTIVE"),
  ("fstMorphism", "def", "UAM_DirectProduct.lean", 40, "ACTIVE"),
  ("algLe", "def", "UAM_Directionality.lean", 17, "ACTIVE"),
  ("EpsilonNFA", "structure", "UAM_EpsilonNFA.lean", 24, "ACTIVE"),
  ("IsExtension", "structure", "UAM_Extension.lean", 30, "ACTIVE"),
  ("empty", "def", "UAM_Free.lean", 31, "ACTIVE"),
  ("R_eq", "def", "UAM_Green.lean", 20, "ACTIVE"),
  ("IsUnit'", "def", "UAM_Group.lean", 23, "ACTIVE"),
  ("HClass", "def", "UAM_HClass.lean", 25, "ACTIVE"),
  ("IsLeftIdeal", "structure", "UAM_Ideal.lean", 28, "ACTIVE"),
  ("IsIdempotent", "def", "UAM_Idempotent.lean", 15, "ACTIVE"),
  ("IsWeakBeginningStructure", "def", "UAM_InfiniteBeginning.lean", 31, "ACTIVE"),
  ("IsInverse", "def", "UAM_Inverse.lean", 28, "ACTIVE"),
  ("IsRegularLanguage", "def", "UAM_Kleene.lean", 34, "ACTIVE"),
  ("regexToDFA", "def", "UAM_KleeneComplete.lean", 21, "ACTIVE"),
  ("RegExp.support", "def", "UAM_KleeneCounterexample.lean", 19, "ACTIVE"),
  ("minimalDFA", "def", "UAM_MinimalDFA.lean", 31, "ACTIVE"),
  ("MonoidAction", "structure", "UAM_MonoidAction.lean", 24, "ACTIVE"),
  ("MonoidMorphism", "structure", "UAM_Morphism.lean", 24, "ACTIVE"),
  ("languageNerodeSetoid", "def", "UAM_MyhillNerode.lean", 26, "ACTIVE"),
  ("congruencesContaining", "def", "UAM_Presentation.lean", 39, "ACTIVE"),
  ("letterMap", "def", "UAM_PresentationMorphism.lean", 25, "ACTIVE"),
  ("principalLeft", "def", "UAM_PrincipalIdeals.lean", 19, "ACTIVE"),
  ("reach", "def", "UAM_Reachability.lean", 20, "ACTIVE"),
  ("RectangularBand", "structure", "UAM_RectangularBand.lean", 26, "ACTIVE"),
  ("ReesMatrix", "def", "UAM_ReesMatrix.lean", 21, "ACTIVE"),
  ("IsZero", "def", "UAM_Regular.lean", 26, "ACTIVE"),
  ("IsRightInvariant", "def", "UAM_RegularLanguages.lean", 54, "ACTIVE"),
  ("PartialBij", "structure", "UAM_Representation.lean", 40, "ACTIVE"),
  ("phi", "def", "UAM_ReverseMyhillNerode.lean", 69, "ACTIVE"),
  ("D_rel", "def", "UAM_Schutzenberger.lean", 30, "ACTIVE"),
  ("ScalarAction", "structure", "UAM_SemidirectProduct.lean", 31, "ACTIVE"),
  ("IsCommutative", "def", "UAM_Semilattice.lean", 22, "ACTIVE"),
  ("Submonoid", "structure", "UAM_Submonoid.lean", 21, "ACTIVE"),
  ("ThompsonState", "inductive", "UAM_Thompson.lean", 24, "ACTIVE"),
  ("actionHom", "def", "UAM_TransitionMonoid.lean", 38, "ACTIVE"),
  ("HasOnlyTrivialIdempotent", "def", "UAM_TrivialSettling.lean", 32, "ACTIVE"),
  ("initial", "def", "UnifiedModel.lean", 43, "ACTIVE")
]

/-- Layer 3: 4 load-bearing terms. -/
abbrev Layer3_FormalMind_Terms : Array Entry := #[
  ("Concept", "inductive", "FormalMindEngineering.lean", 19, "ACTIVE"),
  ("ConceptModel", "structure", "FormalMindInterrelationships.lean", 16, "SUSPECTED_DUPLICATE (name overlap; distinct declarations)"),
  ("Knowledge", "structure", "FormalMind_Interrelations.lean", 21, "SUSPECTED_DUPLICATE (name overlap; distinct declarations)"),
  ("SubjectActionModel", "structure", "UAMFormalMindBridge.lean", 30, "ACTIVE")
]

/-- Layer 2: 3 load-bearing terms. -/
abbrev Layer2_Arithmetic_Terms : Array Entry := #[
  ("ComputeMode", "inductive", "IdealAI.lean", 16, "ACTIVE"),
  ("System", "structure", "IdealAI_Countermodels.lean", 28, "ACTIVE"),
  ("OpenAxiomSet", "structure", "Stubs_OpenProblems.lean", 23, "ACTIVE (historical name; imported by downstream modules)")
]

/-- Layer 1: 6 load-bearing terms. -/
abbrev Layer1_Base_Terms : Array Entry := #[
  ("ProgramExtEq", "def", "ReclaimedTheorems.lean", 129, "ACTIVE"),
  ("PartialComputableEnumeration", "structure", "ReclaimedTheorems.lean", 137, "ACTIVE"),
  ("Term", "inductive", "Arithmetic_Foundations.lean", 17, "ACTIVE"),
  ("L0Action", "def", "ModelLadder.lean", 47, "ACTIVE"),
  ("ArithmetizedSyntax", "structure", "ReclaimedTheorems.lean", 19, "ACTIVE"),
  ("CannotDistinguish", "def", "Stubs_Core.lean", 20, "ACTIVE (historical name; imported by downstream modules)")
]

/-- Name-level overlaps reviewed during Run 32; these are not declaration aliases. -/
abbrev Suspected_Duplicates : Array (String × String × String) := #[
  ("FormalMindInterrelationships.lean", "FormalMind_Interrelations.lean", "Distinct theories; similar filenames only"),
  ("UAM_DFAEval.DFA", "UAM_RegularLanguages.DFA", "Single definition: the latter imports and opens UAM_DFAEval"),
  ("Stubs_Core.lean", "Stubs_OpenProblems.lean", "Distinct active layers; OpenProblems extends Core")
]

/-- All glossary entries. -/
abbrev AllTerms : Array Entry := RSIA_Core_Terms ++ Layer4_UAM_Core_Terms ++
  Layer3_FormalMind_Terms ++ Layer2_Arithmetic_Terms ++ Layer1_Base_Terms

end UAM_RSIA.Glossary
