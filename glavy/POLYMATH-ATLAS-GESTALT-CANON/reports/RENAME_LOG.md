# RENAME_LOG — normalization of POLYMATH-ATLAS names to Mathlib conventions

Slogan of this pass: **names must describe the formal object, not the metaphor.**

Two kinds of work are recorded here:

1. **Renames actually applied** to the Lean sources of this project (section 1).
   Every occurrence was rewritten and the whole project still builds (`lake build`,
   8253 targets, 0 `sorry`).
2. **The normalized naming used for the newly formalized adaptive-agent core**
   (section 2). The metaphorical names in the left column (`Reactor`, `Compressor`,
   `Navigator`, `HolographicMonitor`, `GenesisConditions`, `MinimalIntelligence`,
   `GenesisEvent`, `Alive`, `GenesisOf`, …) are **not used anywhere** in the project;
   the table records the dictionary so that older prose referring to them can be
   translated.

---

## 1. Renames applied to existing Lean sources

All in namespace `Polymath`, files `RequestProject/*.lean` (and `README.md`).

| Old name | New name | Reason |
|----------|----------|--------|
| `KGraph` | `KnowledgeGraph` | Mathlib structures are spelled out in `CamelCase`; a one-letter abbreviation hides the object. |
| `PGraph` | `ProofGraph` | idem. |
| `KObj` | `KnowledgeObject` | idem. |
| `KKind` | `ObjectKind` | it enumerates the kinds of a knowledge object. |
| `Rel` | `KnowledgeRelation` | `Rel` collides with Mathlib's `Rel α β`; the object is a typed edge of the knowledge graph. |
| `RelKind` | `RelationKind` | it enumerates the kinds of a relation. |
| `Tower` | `KnowledgeTower` | descriptive, and parallel to `ProofTower`. |
| `PTower` | `ProofTower` | idem. |
| `KGraph.addObj` | `KnowledgeGraph.addObject` | no abbreviation. |
| `KGraph.addRel` | `KnowledgeGraph.addRelation` | no abbreviation. |
| `KGraph.toPGraph` | `KnowledgeGraph.toProofGraph` | follows the rename of the target type. |

The rename propagates to every derived name automatically, e.g.

* `KGraph.relation_resolves` → `KnowledgeGraph.relation_resolves`
* `PGraph.grounded_trace` → `ProofGraph.grounded_trace`
* `KGraph.dedup_normalized` → `KnowledgeGraph.dedup_normalized`
* `Tower.exists_birth` → `KnowledgeTower.exists_birth`
* `PTower.groundedClaims_saturates` → `ProofTower.groundedClaims_saturates`

Names that were **kept** because they already describe the formal object:
`Maturity`, `Grounded`, `Acyclic`, `Reaches`, `Dep`, `Impact`, `Compatible`,
`Conflict`, `ConflictFree`, `Agree`, `Extends`, `Legal`, `Permitted`, `Role`,
`Agent`, `Action`, `Scale`, `Phase`, `Distinction`, `State`, `Transition`,
`informationGain`, `Model`, `Goal`, `feedbackError`, `uccStep`.

### Archive layer (`RequestProject/Atlas/`)

Two structures shared a name with the namespace they live in, producing names such as
`UnifiedModel.UnifiedModel.consciousness`. Mathlib never repeats the namespace in the
declaration name, so both were renamed (call sites in `ModelLadder.lean` and
`UAM_CognitiveDFA.lean` were updated):

| Old name | New name | Reason |
|----------|----------|--------|
| `UnifiedModel.UnifiedModel` | `UnifiedModel.UnifiedAgentModel` | the namespace must not be repeated in the declaration name; the structure packages the three model layers of one agent |
| `GreenAnatomy.GreenAnatomy` | `GreenAnatomy.GreenStructure` | idem; the structure collects the Green-relation facts available at a ladder size |

`ConstitutionBridges.ConstitutionBridges` was **kept**: its docstring records that this
is a deliberately requested public alias for `BridgePackage`.

## 2. Naming dictionary for the adaptive-agent core (`RequestProject/AdaptiveAgent.lean`)

The seven-layer "Genesis Engine" description was formalized under Mathlib-idiomatic
names. Structures:

| metaphorical name | formal name | what the object is |
|-------------------|-------------|--------------------|
| `Reactor` | `StreamTransformer` | a map `ObservationStream → ObservationStream` preserving liveness |
| `Compressor` | `VariationalFamily` | a positive prior on a finite latent space + a posterior for each observation |
| `Navigator` | `ActivePolicyAgent` | variational family + forward model + preferences + planner |
| `HolographicMonitor` | `MetaOptimizer` | an agent + a self-latent + an endomap of agent space |
| `GenesisConditions` | `AdaptivePreconditions` | the three preconditions C1–C3 |
| `MinimalIntelligence` | `AdaptiveAgentSpec` | the five-condition specification |
| `GenesisEvent` | `ReflexiveAdaptiveAgent` | an agent that is a fixed point of its own meta-update |
| `AliveAt` / `Alive` | `LiveAt` / `Live` | liveness at a time / at all times |
| `GenesisOf` | `SelfMap` (alias `Endomap`) | an endomorphism `α → α` |
| `Tuple` / `Stream` | `Observation` / `ObservationStream` | a channel-indexed real datum / a function `ℕ → Observation` |

Theorems:

| metaphorical name | formal name | statement |
|-------------------|-------------|-----------|
| `genesis_requires_all_three` | `neg_adaptivePreconditions_of_neg_c1` (+ `…_c2`, `…_c3`) | failure of any one precondition refutes the conjunction |
| `efe_is_genesis_threshold` | `ActivePolicyAgent.efe_nonneg` | expected free energy is `≥ 0` |
| `efe_nonneg_fold` / `efe_foldl_ge_init` | `ActivePolicyAgent.efe_foldl_ge_init`, `ActivePolicyAgent.efe_foldl_nonneg_of_init_nonneg` | accumulation never drops below the initial value |
| `minimal_intelligence_implies_alive` | `AdaptiveAgentSpec.live_at` | the specification entails liveness at every time |
| `termination_blocks_intelligence` | `neg_adaptiveAgentSpec_of_neg_live_at` | a dead stream refutes the specification |
| `genesis_event_implies_minimal` | `ReflexiveAdaptiveAgent.adaptive_agent_spec` | reflexive closure entails the specification |
| `l7_implies_recursive_capacity` | `ReflexiveAdaptiveAgent.self_nontrivial` | self-reference forces `Nontrivial Latent` |
| `omega_exists_as_fixed_point` | `exists_fixed_point_selfMap` | Knaster–Tarski for monotone maps on a complete lattice |
| `Omega_exists` (**axiom**) | *removed* | replaced by the theorem above, plus `not_forall_exists_fixed_point_selfMap`, which **refutes** the unrestricted form (`Bool.not` has no fixed point) |

### Axiom status

The project uses **no custom axioms**. Every result depends only on
`propext`, `Classical.choice`, `Quot.sound` (many depend on strictly fewer);
this is checked by the `#print axioms` block at the end of
`RequestProject/Main.lean`.

---

## 3. Gestalt audit pass — renames applied to `RequestProject/Gestalt/`

Section 2 above recorded the metaphorical names as "not used anywhere".  That was
true of the adaptive-agent core, but the gestalt modules had reintroduced three
of them as structure names, and one as a module/namespace name.  They are now
gone from the identifiers; the metaphor is kept only in docstrings, where it
identifies the informal source.

| Old name | New name | Reason |
|----------|----------|--------|
| `Genesis.Reactor` | `Genesis.DistinctionDetector` | the structure is a map from raw input to a set of distinctions; "reactor" names the metaphor, not the object |
| `Genesis.Compressor` | `Genesis.DistinctionFilter` | the structure is an idempotent, subset-valued operator on distinction sets |
| `Genesis.GenesisEvent` | `Genesis.StateSpaceExpansion` | the structure is an injective, non-surjective map `S → S'` |
| `GenesisEngine.genesis` (field) | `GenesisEngine.expansion` | follows the rename of the field's type |
| `Genesis.l1_reactor_memoryless` | `Genesis.l1_distinctionDetector_memoryless` | follows the rename of the structure |
| `RequestProject/Gestalt/Urobouros.lean` | `RequestProject/Gestalt/SelfReference.lean` | file and namespace `PolymathAtlas.Gestalt.Urobouros` → `PolymathAtlas.Gestalt.SelfReference` |
| `urobouros_closure` | `methodology_revisits_level` | `snake_case` theorem naming that states what is proved: the version trajectory revisits an admissible level |
| `urobouros_closure_t5Bound` | `methodology_revisits_level_within_card` | idem, with the bound made explicit |

Names deliberately **kept** in the gestalt layer, because they name the informal
source item and no better formal name exists: `Navigator` (its `efe` field is the
formal content), `Monitor`, `GenesisConditions`, `MinimalIntelligence`,
`GenesisEngine`, `IdiotesAgent`, `HorizonCanon`, `Methodology`.

New names introduced by the audit pass (`RequestProject/Gestalt/CoreBridge.lean`):
`navigatorOfActivePolicyAgent`, `navigatorOfActivePolicyAgent_efe`,
`navigatorOfActivePolicyAgent_efe_nonneg`, `navigator_min_efe_eq`, `trace`,
`trace_length`, `efe_trace_nonneg`, `isOmega_of_step_fixed`,
`exists_methodology_isOmega`, `reflexiveAdaptiveAgent_drawsDistinction`,
`reflexiveAdaptiveAgent_liveAt`.
