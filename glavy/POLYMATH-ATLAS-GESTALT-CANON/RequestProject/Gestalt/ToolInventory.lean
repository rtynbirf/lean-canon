/-
# POLYMATH_ATLAS_GESTALT — Part 5.  Tool inventory.

Source: the **conversation inventory of AI tooling** — the tools currently
available, the critically missing ones, and the desirable ones.

Note on the counts.  The informal source speaks of "30 tools" available; the
explicit enumeration it gives names 28 distinct capabilities (two entries,
"code gen/execution" and "image gen/understanding", each name two capabilities
and are split here).  This file formalizes exactly the enumerated items, so
`tool_has.card = 28`, and records that discrepancy rather than inventing two
extra tools.  The missing-critical list has 19 items and the desirable list 20,
matching the source exactly.

All statements in this file are fully proved: no `sorry` remains.
-/
import RequestProject.Gestalt.MetaSkills

namespace PolymathAtlas.Gestalt.ToolInventory

/-- The universe of AI capabilities named in the conversation inventory:
28 available, 19 critically missing, 20 desirable.  Source: conversation, tool
inventory. -/
inductive Tool
  -- available (`tool_has`)
  | textGeneration | multimodality | functionCalling | webSearch
  | codeGeneration | codeExecution | documentGeneration | dataAnalysis
  | charts | imageGeneration | imageUnderstanding | asr | tts
  | videoUnderstanding | webReading | browserAutomation | structuredOutput
  | conversationMemory | multiTurnReasoning | chainOfThought | fewShot
  | instructionFollowing | summarization | translation | formalVerification
  | mathReasoning | knowledgeGraphs | multiAgentOrchestration
  -- critically missing (`tool_missing_critical`)
  | crossSessionMemory | metacognition | selfVerification | freeWebBrowsing
  | realTimeData | physicalAction | spontaneousInitiative | consequenceModeling
  | contradictionDetection | intentUnderstanding | adaptiveComplexity
  | errorAsResource | crossDomainIntegration | solutionCostEstimation
  | processExplanation | refusalCapability | temporalReasoning
  | complexityScaling | gapCultivation
  -- desirable (`tool_desirable`)
  | spatialThinking3D | music | longTermPlanning | emotionalIntelligence
  | multilingualThinking | selfModification | hypothesisGeneration
  | scientificThinking | moralEvaluation | humor | sleepConsolidation
  | intuition | embodiedModeling | socialDynamics | narrativeThinking
  | aestheticEvaluation | pedagogicalAdaptation | creativeDestruction
  | symbolicThinking | transcendence
  deriving DecidableEq, Fintype, Repr

open Tool

/-- **Definition `tool_has`.**

The tools currently available to AI systems: text generation, multimodality,
function calling, web search, code generation, code execution, document
generation, data analysis, charts, image generation, image understanding, ASR,
TTS, video understanding, web reading, browser automation, structured output,
conversation memory, multi-turn reasoning, chain-of-thought, few-shot,
instruction following, summarization, translation, formal verification, math
reasoning, knowledge graphs, multi-agent orchestration.

Source: conversation, tool inventory ("30 tools"; 28 items enumerated). -/
def tool_has : Finset Tool :=
  {textGeneration, multimodality, functionCalling, webSearch, codeGeneration,
   codeExecution, documentGeneration, dataAnalysis, charts, imageGeneration,
   imageUnderstanding, asr, tts, videoUnderstanding, webReading, browserAutomation,
   structuredOutput, conversationMemory, multiTurnReasoning, chainOfThought, fewShot,
   instructionFollowing, summarization, translation, formalVerification, mathReasoning,
   knowledgeGraphs, multiAgentOrchestration}

/-- **Definition `tool_missing_critical`.**

The 19 critically missing tools: cross-session memory, metacognition,
self-verification, free web browsing, real-time data, physical action,
spontaneous initiative, consequence modeling, contradiction detection, intent
understanding, adaptive complexity, error-as-resource, cross-domain integration,
solution cost estimation, process explanation, refusal capability, temporal
reasoning, complexity scaling, gap cultivation.

Source: conversation, tool inventory. -/
def tool_missing_critical : Finset Tool :=
  {crossSessionMemory, metacognition, selfVerification, freeWebBrowsing, realTimeData,
   physicalAction, spontaneousInitiative, consequenceModeling, contradictionDetection,
   intentUnderstanding, adaptiveComplexity, errorAsResource, crossDomainIntegration,
   solutionCostEstimation, processExplanation, refusalCapability, temporalReasoning,
   complexityScaling, gapCultivation}

/-- **Definition `tool_desirable`.**

The 20 desirable tools: 3D spatial thinking, music, long-term planning,
emotional intelligence, multilingual thinking, self-modification, hypothesis
generation, scientific thinking, moral evaluation, humor, sleep/consolidation,
intuition, embodied modeling, social dynamics, narrative thinking, aesthetic
evaluation, pedagogical adaptation, creative destruction, symbolic thinking,
transcendence.

Source: conversation, tool inventory. -/
def tool_desirable : Finset Tool :=
  {spatialThinking3D, music, longTermPlanning, emotionalIntelligence, multilingualThinking,
   selfModification, hypothesisGeneration, scientificThinking, moralEvaluation, humor,
   sleepConsolidation, intuition, embodiedModeling, socialDynamics, narrativeThinking,
   aestheticEvaluation, pedagogicalAdaptation, creativeDestruction, symbolicThinking,
   transcendence}

/-! ### Cardinalities and disjointness -/

/-- The enumerated available tools number 28 (the source says "30"; see the file
header).  Source: conversation, tool inventory. -/
theorem tool_has_card : tool_has.card = 28 := by
  decide

/-- The critically missing tools number 19.  Source: conversation. -/
theorem tool_missing_critical_card : tool_missing_critical.card = 19 := by
  decide

/-- The desirable tools number 20.  Source: conversation. -/
theorem tool_desirable_card : tool_desirable.card = 20 := by
  decide

set_option maxRecDepth 100000 in
/-- The three inventories are pairwise disjoint, and together they exhaust the
capability universe.  Source: conversation, tool inventory. -/
theorem tool_inventory_partition :
    Disjoint tool_has tool_missing_critical ∧ Disjoint tool_has tool_desirable ∧
      Disjoint tool_missing_critical tool_desirable ∧
      tool_has ∪ tool_missing_critical ∪ tool_desirable = Finset.univ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### The ἰδιώτης with 30 tools -/

/-- A toolset that has everything available today and nothing of what is
critically missing.  Source: conversation, "having 30 tools does not make a
polymath". -/
def IdiotesToolset (T : Finset Tool) : Prop :=
  tool_has ⊆ T ∧ Disjoint T tool_missing_critical

/-- Executing capability: the toolset can run things.  Source: conversation. -/
def CanExecute (T : Finset Tool) : Prop := codeExecution ∈ T

/-- Evaluative capability: the toolset can judge its own output.  Requires
metacognition and self-verification, both critically missing.  Source:
conversation. -/
def CanEvaluate (T : Finset Tool) : Prop := metacognition ∈ T ∧ selfVerification ∈ T

/-- Answering capability.  Source: conversation. -/
def CanAnswer (T : Finset Tool) : Prop := textGeneration ∈ T

/-- Understanding capability: requires grasping the intent behind the question.
Source: conversation. -/
def CanUnderstand (T : Finset Tool) : Prop := intentUnderstanding ∈ T

/-- Generative capability.  Source: conversation. -/
def CanGenerate (T : Finset Tool) : Prop := documentGeneration ∈ T

/-- Self-verifying capability.  Source: conversation. -/
def CanVerify (T : Finset Tool) : Prop := selfVerification ∈ T

/-- **Theorem `idiotes_tools`.**

Docstring source: *Having 30 tools does not make a polymath.  An ἰδιώτης with 30
tools is still ἰδιώτης.  The critical gap is not quantity but quality:
metacognition, self-verification, gap cultivation.*

A system possessing all tools in `tool_has` but none in `tool_missing_critical`
is an ἰδιώτης-agent: it can execute but cannot evaluate, can answer but cannot
understand, can generate but cannot verify.  Possession of tools without
metacognition is private capability without universal awareness. -/
theorem idiotes_tools {T : Finset Tool} (h : IdiotesToolset T) :
    (CanExecute T ∧ ¬ CanEvaluate T) ∧ (CanAnswer T ∧ ¬ CanUnderstand T) ∧
      (CanGenerate T ∧ ¬ CanVerify T) := by
  obtain ⟨hsub, hdisj⟩ := h
  have hnot : ∀ t ∈ tool_missing_critical, t ∉ T := fun t ht htT =>
    (Finset.disjoint_left.mp hdisj htT) ht
  refine ⟨⟨hsub (by decide), ?_⟩, ⟨hsub (by decide), ?_⟩, ⟨hsub (by decide), ?_⟩⟩
  · rintro ⟨hm, -⟩
    exact hnot metacognition (by decide) hm
  · intro hu
    exact hnot intentUnderstanding (by decide) hu
  · intro hv
    exact hnot selfVerification (by decide) hv

/-- **Theorem `idiotes_tools`** — the qualitative gap.

The three capabilities the conversation singles out — metacognition,
self-verification, gap cultivation — are exactly what such a toolset lacks, no
matter how large it is. -/
theorem idiotes_tools_gap {T : Finset Tool} (h : IdiotesToolset T) :
    metacognition ∉ T ∧ selfVerification ∉ T ∧ gapCultivation ∉ T := by
  obtain ⟨-, hdisj⟩ := h
  have hnot : ∀ t ∈ tool_missing_critical, t ∉ T := fun t ht htT =>
    (Finset.disjoint_left.mp hdisj htT) ht
  exact ⟨hnot metacognition (by decide), hnot selfVerification (by decide),
    hnot gapCultivation (by decide)⟩

/-- **Theorem `idiotes_tools`** — quantity is not quality.

Such a system holds strictly more tools than it lacks and is still an ἰδιώτης:
the count is no evidence of polymathy. -/
theorem idiotes_tools_quantity_not_quality {T : Finset Tool} (h : IdiotesToolset T) :
    tool_missing_critical.card < T.card ∧ metacognition ∉ T := by
  have hcard : tool_has.card ≤ T.card := Finset.card_le_card h.1
  rw [tool_has_card] at hcard
  refine ⟨?_, (idiotes_tools_gap h).1⟩
  rw [tool_missing_critical_card]
  omega

/-! ### Bridge to Part 4 -/

/-- **Theorem `idiotes_tools`** — the bridge to the meta-skills impossibility.

The tool-level ἰδιώτης and the architecture-level ἰδιώτης of
`RequestProject/Gestalt/MetaSkills.lean` are the same figure: lacking the
metacognition tool, the system's confidence can only be pattern-matched, so it
is not metacognitive on any input. -/
theorem idiotes_toolset_not_metacognitive {Tok C : Type*} {T : Finset Tool}
    (hT : IdiotesToolset T) (A : MetaSkills.Cognizer Tok C)
    (hA : MetaSkills.NextTokenBound A) (truth : C → ℝ) :
    metacognition ∉ T ∧ ¬ MetaSkills.Metacognition truth A :=
  ⟨(idiotes_tools_gap hT).1, MetaSkills.no_prompt_makes_metacognitive A hA truth⟩

end PolymathAtlas.Gestalt.ToolInventory
