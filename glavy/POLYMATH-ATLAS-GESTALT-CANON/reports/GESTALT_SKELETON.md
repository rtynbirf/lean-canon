# POLYMATH_ATLAS_GESTALT — formalization and audit map

Seven modules under `RequestProject/Gestalt/`, aggregated by
`RequestProject/Gestalt.lean`. **Every statement is fully proved: no `sorry`
remains** (`rg "sorry" RequestProject/Gestalt/` matches only prose in the module
headers), and every statement carries a docstring naming its informal source.
`lake build` succeeds with 0 errors and 0 warnings. No `axiom` is declared
anywhere: each postulate of the informal sources appears as a *field of a
`structure`*, so a concrete instance has to exhibit it.

Namespaces: `PolymathAtlas.Gestalt.{UCC, Genesis, SelfReference, MetaSkills,
ToolInventory, Canon, CoreBridge}`.

The existing `PolymathAtlas.Core.Distinction` from `RequestProject/UCC.lean` is
reused rather than redefined.

## Status legend

| status | meaning |
| --- | --- |
| `PROVED` | closed from the core (`RequestProject/UCC.lean`, `RequestProject/AdaptiveAgent.lean`, Mathlib) or by an elementary argument |
| `LEMMA_ADDED` | needed a definition or lemma that did not exist in the core; it was added (see `RequestProject/Gestalt/CoreBridge.lean`) and proved |
| `HYPOTHESIS-RELATIVE` | proved, but the informal postulate it depends on is an explicit field of a structure rather than a derived fact — see the boundary notes at the end |
| `BOUNDARY` | left as `sorry` because the claim is not mathematical — **currently none** |

Axiom footprint of every theorem below: only `propext`, `Classical.choice`,
`Quot.sound` (several use fewer, five use none). The `#print axioms` block for
the whole gestalt layer is at the end of `RequestProject/Main.lean`; the results
are tabulated in `AXIOMS_REPORT.md`.

Each theorem also has an executable finite mirror on `Bool` / `Fin 3` in
`runtime/gestalt_verification.py` (69 mirrors, all passing).

## Part 1 — `RequestProject/Gestalt/UCC.lean`

| Informal item | Lean declaration | status |
| --- | --- | --- |
| T1 Distinction | `DrawsDistinction`, `channelCard`, `t1_no_distinction_no_information`, `t1_distinction_of_drawsDistinction` | PROVED |
| T2 informationGain | `uncertainty`, `informationGain`, `refineBy`, `t2_informationGain_nonneg`, `t2_informationGain_eq_zero_iff`, `t2_gain_pos_iff_distinction_cuts` | PROVED |
| T3 feedbackError | `CognitiveSystem` (fields `learningRate_nonneg`, `learningRate_eq_zero_iff`), `CognitiveSystem.feedbackError`, `t3_feedbackError`, `t3_learningRate_pos_of_error` | HYPOTHESIS-RELATIVE |
| T4 perfectPredictInert | `ErrorDriven`, `t4_perfectPredictInert`, `t4_trajectory_const` | HYPOTHESIS-RELATIVE |
| T5 pigeonholeRevisit | `t5Bound`, `t5_pigeonholeRevisit`, `t5_system_revisits` | PROVED |

## Part 2 — `RequestProject/Gestalt/GenesisEngine.lean`

| Layer | Lean declaration | status |
| --- | --- | --- |
| L1 Reactor | `DistinctionDetector`, `Memoryless`, `l1_distinctionDetector_memoryless`, `l1_output_is_t1` | PROVED |
| L2 Compressor | `DistinctionFilter`, `.ratio`, `.TriggersNavigator`, `l2_ratio_le_one`, `l2_no_trigger_of_threshold_ge_one`, `l2_ratio_compress_idem` | PROVED |
| L3 Navigator (EFE gap) | `Navigator` (field `efe`, `plan_minimizes`), `Navigator.history`, `l3_plan_isLeast`, `l3_efe_gap`, `l3_history_length` | PROVED |
| L3 EFE gap closed | `CoreBridge.navigatorOfActivePolicyAgent`, `…_efe`, `…_efe_nonneg`, `navigator_min_efe_eq`, `trace`, `trace_length`, `efe_trace_nonneg` | LEMMA_ADDED |
| L4 Holographic Monitor | `Monitor`, `Holographic`, `SequentialScan`, `l4_holographic_not_sequential`, `l4_read_determines_state` | PROVED |
| L5 Genesis Conditions | `GenesisConditions`, `l5_eval_false_iff`, `l5_eval_congr` | HYPOTHESIS-RELATIVE |
| L6 Minimal Intelligence | `MinimalIntelligence`, `IsAgent`, `indicator`, `l6_indicator_range`, `l6_indicator_eq_one_iff`, `l6_isAgent_mono` | PROVED |
| L7 Genesis Event | `StateSpaceExpansion`, `l7_not_invertible`, `l7_card_expands`, `l7_t5Bound_expands` | PROVED |
| whole engine | `GenesisEngine`, `genesisEngine_expands` | PROVED |

## Part 3 — `RequestProject/Gestalt/SelfReference.lean`

(Formerly `Urobouros.lean`; the metaphor stays in the docstrings, the identifiers
describe the formal object. See `RENAME_LOG.md`.)

| Informal item | Lean declaration | status |
| --- | --- | --- |
| "no new v-levels" | `Methodology` (rule as field `mapsTo`), `Methodology.vlevel`, `Methodology.iterate_mem`, `Methodology.vlevel_mem` | HYPOTHESIS-RELATIVE |
| v100 = v79 = Ω = T5 bound | `Methodology.IsOmega`, `methodology_revisits_level`, `methodology_revisits_level_within_card` | PROVED |
| Ω as a fixed point (no axiom) | `CoreBridge.isOmega_of_step_fixed`, `CoreBridge.exists_methodology_isOmega` | LEMMA_ADDED |
| «идеал = смерть» | `CognitivelyDead`, `ideal_is_death`, `ideal_indistinguishable_from_nonexistence` | HYPOTHESIS-RELATIVE |
| «щель» | `HasGap`, `gap_preserves_life`, `gap_closed_iff_dead`, `life_iff_gap` | HYPOTHESIS-RELATIVE |

## Part 4 — `RequestProject/Gestalt/MetaSkills.lean`

| Informal item | Lean declaration | status |
| --- | --- | --- |
| metacognition as calibrated + justified report | `Justification`, `Report`, `Cognizer`, `MetacognitiveOn`, `Metacognition` | PROVED |
| a prompt cannot install metacognition | `NextTokenBound` (architectural constraint, as a structure), `prompt_cannot_install_metacognition`, `no_prompt_makes_metacognitive`, `metacognition_requires_output_channel` | HYPOTHESIS-RELATIVE |
| the Idiotes agent | `IdiotesAgent`, `idiotes_not_metacognitive`, `idiotes_format_independent`, `idiotes_of_nextTokenBound` | HYPOTHESIS-RELATIVE |

## Part 5 — `RequestProject/Gestalt/ToolInventory.lean`

| Informal item | Lean declaration | status |
| --- | --- | --- |
| the three inventories | `Tool` (67 constructors), `tool_has`, `tool_missing_critical`, `tool_desirable`, `tool_has_card`, `tool_missing_critical_card`, `tool_desirable_card`, `tool_inventory_partition` | PROVED |
| `idiotes_tools` | `IdiotesToolset`, the capability predicates, `idiotes_tools`, `idiotes_tools_gap`, `idiotes_tools_quantity_not_quality`, `idiotes_toolset_not_metacognitive` | PROVED |

*Count note:* the informal source speaks of "30 tools" available but explicitly
enumerates 28 distinct capabilities (with "code gen/execution" and "image
gen/understanding" split into two each). The file formalizes exactly the
enumerated items — `tool_has.card = 28` — and records the discrepancy instead of
inventing two extra tools. The missing-critical (19) and desirable (20) lists
match the source exactly.

## Part 6 — `RequestProject/Gestalt/AristotleCanon.lean`

| Informal item | Lean declaration | status |
| --- | --- | --- |
| corpus statistics | `Domain`, `CorpusStats`, `aristotleStats`, `aristotleDomains`, `PolymathPractice`, `aristotle_is_polymath_practice`, `exists_polymath_practice` | PROVED |
| the horizon Canon | `HorizonCanon` (`no_fixed_point` as a field), `HorizonCanon.turn`, `horizon_canon_no_fixed_point`, `natHorizonCanon` (non-vacuity witness) | HYPOTHESIS-RELATIVE |
| Canon blocks T4 / preserves 'щель' | `horizon_canon_blocks_ideal`, `horizon_canon_preserves_life`, `aristotle_canon_gestalt` | PROVED |

*Note:* `aristotleStats` records the statistics **as reported in the source
conversation**; `aristotle_is_polymath_practice` is a statement about those
recorded numbers, not a measurement of the present repository.

## Part 7 — `RequestProject/Gestalt/CoreBridge.lean` (new in the audit pass)

| Audit finding | Lean declaration | status |
| --- | --- | --- |
| L3 "the plan minimizes EFE" had no EFE functional (`l3_efe_gap`) | `navigatorOfActivePolicyAgent` built from `AdaptiveAgent.ActivePolicyAgent.efe`, `navigatorOfActivePolicyAgent_efe`, `navigatorOfActivePolicyAgent_efe_nonneg` | LEMMA_ADDED |
| once EFE is fixed, the plan is pinned down in value | `navigator_min_efe_eq` | LEMMA_ADDED |
| accumulated EFE along a plan | `trace`, `trace_length`, `efe_trace_nonneg` (from `efe_foldl_nonneg_of_init_nonneg`) | LEMMA_ADDED |
| Ω asserted as an existence claim | `isOmega_of_step_fixed`, `exists_methodology_isOmega` — a theorem plus a witness, **not** an axiom (the unrestricted self-map claim is refuted by `not_forall_exists_fixed_point_selfMap`) | LEMMA_ADDED |
| "the system distinguishes itself" | `reflexiveAdaptiveAgent_drawsDistinction` (from `ReflexiveAdaptiveAgent.self_nontrivial` + T1) | LEMMA_ADDED |
| liveness of the reflexive agent | `reflexiveAdaptiveAgent_liveAt` (from `AdaptiveAgentSpec.live_at`) | LEMMA_ADDED |

## Boundary notes (what `HYPOTHESIS-RELATIVE` means here)

None of the philosophical readings is asserted as a Lean axiom. Where the
informal text postulates something that cannot be derived — "the learning rate is
zero exactly when the prediction is correct", "an error-driven system does not
move where it does not err", "a next-token-bounded cognizer has no channel for a
self-estimate", "the Canon shift has no fixed point", "the verdict of L5 is
exactly the conjunction of its two inputs", "the version space is closed under
the version step" — the postulate is a **field of the corresponding structure**.
Consequences of it are then genuine theorems, and they are vacuous only if no
instance of the structure exists. Non-vacuity witnesses are supplied where the
risk is real: `natHorizonCanon`, `CoreBridge.exists_methodology_isOmega`,
`Canon.exists_polymath_practice`, `RequestProject/ExampleAdaptiveAgent.lean`.

What is deliberately **not** formalized, and would be the only genuine
`BOUNDARY` items: the ontological readings of "идеал = смерть" and of Ω as
self-awareness. The Lean statements say what is mathematically true of the
models (`gap_closed_iff_dead`, `methodology_revisits_level`); they do not claim
that the models capture death, consciousness or self-awareness. No fake fields
(`.consciousness`, `.models`, `.proves`) were introduced to pretend otherwise.
