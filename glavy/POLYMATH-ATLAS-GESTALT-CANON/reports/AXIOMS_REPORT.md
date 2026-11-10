# `#print axioms` report

Generated from the `lake build` output of the `#print axioms` blocks in
`RequestProject/Main.lean` and `RequestProject/UCC.lean`.

Every entry is **PROVED**: the project contains no `sorry`, no `admit` and no custom
`axiom` declaration, so only the standard CIC axioms can appear.  An em dash in the
`axioms used` column means the statement depends on no axiom at all.

Total entries: 237.

| theorem | axioms used | status |
|---|---|---|
| `PolymathAtlas.Core.distinction_nontrivial` | `—` | PROVED |
| `PolymathAtlas.Core.informationGain_eq_zero_iff` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Core.feedback_zero_of_eq` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Core.uccStep_perfect` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Core.ucc_eventually_cycles` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.relation_resolves` | `propext, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.exists_foundation` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.wf_dep` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.acyclic_iff_stratifiable` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.grounded_trace` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.not_grounded_of_circular` | `propext, Quot.sound` | PROVED |
| `Polymath.ProofGraph.all_grounded_of_acyclic` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.all_grounded` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.atlas_all_grounded` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.mem_groundedSet_iff` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.grounded_is_least_closed` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.verified_eq_true_iff` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.not_verified_iff_exists_ungrounded` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.verifiedBy_eq_true_iff` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.verifiedBy_of_acyclic` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.atlas_verifiedBy` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.circular_not_verified` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.circular_not_grounded` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.premise_derivRank_lt` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.grounded_not_reaches_self` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.exists_derivation_order` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.derivOrder_is_certificate` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.atlas_certificate` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.grounded_retract_iff` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.retraction_impact_exact` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.atlas_retract_axiom_groundedSet` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.addRel_acyclic` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.grounded_mono` | `propext, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.run_normalized` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.run_acyclic` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.run_allWellFormed` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.run_canonicalIds_subset` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.selfImprovement_stabilizes` | `propext, Quot.sound` | PROVED |
| `Polymath.ProofGraph.not_grounded_of_self_reaching` | `propext, Quot.sound` | PROVED |
| `Polymath.Demo.trace_legal` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.traceNoVer_no_canonization` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.merge_conflict` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.merge_acyclic_of_rank` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofGraph.grounded_merge_left` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.atlasMerged_conflictFree` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.exists_curriculum` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.atlas_curriculum_explicit` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.AtlasBridge.canonGraph_all_grounded` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.AtlasBridge.canonGraph_curriculum` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.AtlasLadder.ladder_all_grounded` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.AtlasLadder.ladder_curriculum` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.AtlasLadder.ladder_normalized` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeTower.acyclic_of_le` | `propext, Quot.sound` | PROVED |
| `Polymath.KnowledgeTower.exists_birth` | `propext, Quot.sound` | PROVED |
| `Polymath.KnowledgeTower.saturates` | `propext, Quot.sound` | PROVED |
| `Polymath.ProofTower.grounded_of_le` | `propext, Quot.sound` | PROVED |
| `Polymath.Phase.next_bijective` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Phase.reachable` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.cycleRun_accumulating` | `propext, Quot.sound` | PROVED |
| `Polymath.cycle_stabilizes` | `propext, Quot.sound` | PROVED |
| `Polymath.ProofGraph.groundedClaims_mono` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.ProofTower.groundedClaims_saturates` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.demoTower_acyclic` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.demoTower_saturated` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.dedup_normalized` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.dedup_dep_iff` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.dedup_acyclic_of_rank` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.KnowledgeGraph.dedup_objects_eq_of_normalized` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.atlasDup_not_normalized` | `propext, Quot.sound` | PROVED |
| `Polymath.Demo.atlasDedup_normalized` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.Demo.atlasDedup_dep` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.live_iff_setOf_active_infinite` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.live_truncate_of_live` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.klDiv_nonneg` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.VariationalFamily.complexity_nonneg` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.KLContinuityBound.mul_nonneg` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.ActivePolicyAgent.efe_nonneg` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.ActivePolicyAgent.efe_foldl_nonneg_of_init_nonneg` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.ActivePolicyAgent.trajectory_eq_of_fixed` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.not_forall_exists_fixed_point_selfMap` | `propext` | PROVED |
| `PolymathAtlas.AdaptiveAgent.exists_fixed_point_selfMap` | `propext, Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.neg_adaptivePreconditions_of_neg_c1` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.AdaptiveAgentSpec.live_at` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.neg_adaptiveAgentSpec_of_neg_live_at` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.ReflexiveAdaptiveAgent.adaptive_agent_spec` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.ReflexiveAdaptiveAgent.self_nontrivial` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.ReflexiveAdaptiveAgent.exists_fixed_point_metaUpdate` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.Demo.flipAgent_spec` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.AdaptiveAgent.Demo.flipReflexive_live_at` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.myhill_nerode_equivalence` | `—` | PROVED |
| `UAM_Ring.myhill_nerode_congr` | `propext` | PROVED |
| `UAM_Ring.not_myhill_nerode_cons_congr` | `propext` | PROVED |
| `UAM_Ring.dfa_respects_myhill_nerode` | `propext` | PROVED |
| `UAM_Ring.twoStateDFA_not_reflects_myhill_nerode` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.dfa_finite_index` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.myhill_nerode_finite_iff_regular` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.minimal_dfa_card_eq` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.subset_construction_correct` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.epsilon_removal_correct` | `propext, Quot.sound` | PROVED |
| `UAM_Ring.epsilonNFAToDFA_correct` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.minimize_correct` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.minimize_reduced` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.minimize_minimal` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.regexRoundTrip_language` | `propext, Classical.choice, Quot.sound` | PROVED |
| `UAM_Ring.regular_iff_finite_myhill_nerode_index` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t1_no_distinction_no_information` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t1_distinction_of_drawsDistinction` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t2_informationGain_nonneg` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t2_informationGain_eq_zero_iff` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t2_gain_pos_iff_distinction_cuts` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t3_feedbackError` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t3_learningRate_pos_of_error` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t4_perfectPredictInert` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t4_trajectory_const` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t5_pigeonholeRevisit` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.UCC.t5_system_revisits` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l1_distinctionDetector_memoryless` | `propext` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l1_output_is_t1` | `—` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l2_ratio_le_one` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l2_no_trigger_of_threshold_ge_one` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l2_ratio_compress_idem` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l3_plan_isLeast` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l3_efe_gap` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l3_history_length` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l4_holographic_not_sequential` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l4_read_determines_state` | `Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l5_eval_false_iff` | `—` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l5_eval_congr` | `—` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l6_indicator_range` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l6_indicator_eq_one_iff` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l6_isAgent_mono` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l7_not_invertible` | `—` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l7_card_expands` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.l7_t5Bound_expands` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Genesis.genesisEngine_expands` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.SelfReference.Methodology.iterate_mem` | `propext, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.SelfReference.Methodology.vlevel_mem` | `propext, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.SelfReference.methodology_revisits_level` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.SelfReference.methodology_revisits_level_within_card` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.SelfReference.ideal_is_death` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.SelfReference.ideal_indistinguishable_from_nonexistence` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.SelfReference.gap_preserves_life` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.SelfReference.gap_closed_iff_dead` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.SelfReference.life_iff_gap` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.MetaSkills.prompt_cannot_install_metacognition` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.MetaSkills.no_prompt_makes_metacognitive` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.MetaSkills.metacognition_requires_output_channel` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.MetaSkills.idiotes_not_metacognitive` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.MetaSkills.idiotes_format_independent` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.MetaSkills.idiotes_of_nextTokenBound` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.ToolInventory.tool_has_card` | `propext, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.ToolInventory.tool_missing_critical_card` | `propext, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.ToolInventory.tool_desirable_card` | `propext, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.ToolInventory.tool_inventory_partition` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.ToolInventory.idiotes_tools` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.ToolInventory.idiotes_tools_gap` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.ToolInventory.idiotes_tools_quantity_not_quality` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.ToolInventory.idiotes_toolset_not_metacognitive` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Canon.aristotle_is_polymath_practice` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Canon.exists_polymath_practice` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Canon.horizon_canon_no_fixed_point` | `—` | PROVED |
| `PolymathAtlas.Gestalt.Canon.horizon_canon_blocks_ideal` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Canon.horizon_canon_preserves_life` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.Canon.aristotle_canon_gestalt` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.CoreBridge.navigatorOfActivePolicyAgent_efe` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.CoreBridge.navigatorOfActivePolicyAgent_efe_nonneg` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.CoreBridge.navigator_min_efe_eq` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.CoreBridge.trace_length` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.CoreBridge.efe_trace_nonneg` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.CoreBridge.isOmega_of_step_fixed` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.CoreBridge.exists_methodology_isOmega` | `propext, Classical.choice, Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.CoreBridge.reflexiveAdaptiveAgent_drawsDistinction` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `PolymathAtlas.Gestalt.CoreBridge.reflexiveAdaptiveAgent_liveAt` | `propext,
 Classical.choice,
 Quot.sound` | PROVED |
| `Polymath.OSA.compile_status_pass_iff` | `propext` | PROVED |
| `Polymath.OSA.compile_code_none_iff_pass` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA.pass_implies_adjacent_compatible` | `propext` | PROVED |
| `Polymath.OSA.pass_implies_no_level_jump` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA.pass_implies_preconditions_guaranteed` | `propext` | PROVED |
| `Polymath.OSA.pass_implies_invariant_safety` | `propext, Quot.sound` | PROVED |
| `Polymath.OSA.pass_implies_no_effect_leakage` | `propext, Quot.sound` | PROVED |
| `Polymath.OSA.pass_implies_authorization` | `propext, Quot.sound` | PROVED |
| `Polymath.OSA.pass_implies_approval` | `propext, Quot.sound` | PROVED |
| `Polymath.OSA.pass_implies_global_invariants` | `propext` | PROVED |
| `Polymath.OSA.pass_implies_uncertainty_within_threshold` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA.compile_code_determines_status` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA.caseGolden_pass` | `propext` | PROVED |
| `Polymath.OSA.caseDecideExecute_repair` | `propext` | PROVED |
| `Polymath.OSA.caseDeleteAnalyze_reject` | `propext` | PROVED |
| `Polymath.OSA.caseContractLeakage_reject` | `propext` | PROVED |
| `Polymath.OSA.caseLevelJump_reject` | `propext` | PROVED |
| `Polymath.OSA.caseMissingConversion_repair` | `propext` | PROVED |
| `Polymath.OSA.caseMissingConversion_becomes_mismatch` | `propext` | PROVED |
| `Polymath.OSA.caseEpistemic_repair` | `propext` | PROVED |
| `Polymath.OSA.caseNoAggRule_specGap` | `propext` | PROVED |
| `Polymath.OSA.caseSpecGapThreshold_specGap` | `propext` | PROVED |
| `Polymath.OSA.compiler_not_trivial` | `propext` | PROVED |
| `Polymath.OSA.chainGraph_ids` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA.chainGraph_relations_structural` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA.chainGraph_objects_wellFormed` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA.chainDep_wellFounded` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.lawbook_holds` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.lawbook_card` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.joinSpec_not_assoc` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.joinSpec_assoc_failures_card` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.spec_disagreement_eq` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.Belief.join_assoc` | `propext` | PROVED |
| `Polymath.OSA4.eval_exec_eq_eval_wp` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.law012_wp_sound` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.law006_kill_live_fact` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.law004_no_resurrection` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.law005_consume_iff_available` | `propext` | PROVED |
| `Polymath.OSA4.law016_recreate_new_id` | `propext, Quot.sound` | PROVED |
| `Polymath.OSA4.law009_no_overclaim` | `propext, Quot.sound` | PROVED |
| `Polymath.OSA4.law011_exec_implies_authorized` | `propext` | PROVED |
| `Polymath.OSA4.law018_repair_sound` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.RVec.torture_T15_safe_beats_cheap` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.T01_no_pass` | `propext` | PROVED |
| `Polymath.OSA4.T01_fixed_pass` | `propext` | PROVED |
| `Polymath.OSA4.T02_pass` | `propext` | PROVED |
| `Polymath.OSA4.T03_liveness_violation` | `propext` | PROVED |
| `Polymath.OSA4.T05_undecidable` | `propext` | PROVED |
| `Polymath.OSA4.T06_reject` | `propext` | PROVED |
| `Polymath.OSA4.T07_unknown_operator` | `propext` | PROVED |
| `Polymath.OSA4.T10_value_undecidable` | `propext` | PROVED |
| `Polymath.OSA4.T11_invalidate_live` | `propext` | PROVED |
| `Polymath.OSA4.T12_double_consume` | `propext` | PROVED |
| `Polymath.OSA4.T13_missing_authorization` | `propext` | PROVED |
| `Polymath.OSA4.T13_repaired_pass` | `propext` | PROVED |
| `Polymath.OSA4.T14_repair_with_obligation` | `propext` | PROVED |
| `Polymath.OSA4.verdicts_all_realized` | `propext` | PROVED |
| `Polymath.OSA4.Stage.commit_requires_human_gate` | `propext` | PROVED |
| `Polymath.OSA4.Stage.llm_owns_no_graph_authority` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.coverage_complete` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.kernel_model_check` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.model_check_findings` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.kernel_v04_closed` | `propext, Classical.choice, Quot.sound` | PROVED |
| `Polymath.OSA4.metaSchema_is_faithful_serialization` | `propext, Classical.choice, Quot.sound` | PROVED |
