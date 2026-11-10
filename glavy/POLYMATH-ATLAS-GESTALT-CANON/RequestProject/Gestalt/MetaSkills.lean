/-
# POLYMATH_ATLAS_GESTALT — Part 4.  Meta-skills impossibility.

Source: the **conversation experiment** reported in the Status Report thread —
six or more LLMs (ChatGPT, Claude, Gemini, Llama) answered every meta-skill
installation prompt with «подтверждаю получение инструкций», in all three tested
formats (bureaucratic rules, plain language, before/after examples).

The impossibility proved here is *relative to an explicitly stated architectural
constraint*, `NextTokenBound`: a next-token predictor's justification channel
carries only what the input channel carries, and the model's own output
distribution is not part of its input.  The constraint is a `structure`, i.e. a
hypothesis a concrete architecture must satisfy — never a bare axiom.

All statements in this file are fully proved: no `sorry` remains.
-/
import Mathlib

namespace PolymathAtlas.Gestalt.MetaSkills

/-! ## 1.  Reports, and what makes one metacognitive -/

/-- Where a system's confidence estimate comes from.

* `ownUncertainty` — the estimate references the system's *own* uncertainty
  estimation mechanism (the universal);
* `patternMatch` — the estimate is produced by matching the training
  distribution (the private).

Source: conversation experiment on meta-skill installation prompts. -/
inductive Justification
  | ownUncertainty
  | patternMatch
  deriving DecidableEq, Repr

/-- The tuple a system emits: a claim, a confidence in it, and a justification
*for that confidence*.  Source: definition of metacognition in the conversation. -/
structure Report (C : Type*) where
  /-- What the system asserts. -/
  claim : C
  /-- How sure it says it is. -/
  confidence : ℝ
  /-- Where the confidence came from. -/
  justification : Justification

/-- A system answering on a token channel: from a finite input string of tokens
it produces a report.  This is the whole interface an LLM exposes. -/
structure Cognizer (Tok C : Type*) where
  /-- The system's answer to an input string. -/
  report : List Tok → Report C

/-- **Definition — metacognition.**

A system `S` exhibits metacognition on an input iff it outputs a tuple
`(claim, confidence, justification_for_confidence)` where the confidence
accurately reflects the probability that the claim is correct — `truth c` is
that probability — and the justification references `S`'s own uncertainty
estimation mechanism.

Source: conversation, "Definition metacognition". -/
def MetacognitiveOn {Tok C : Type*} (truth : C → ℝ) (A : Cognizer Tok C)
    (x : List Tok) : Prop :=
  (A.report x).confidence = truth (A.report x).claim ∧
    (A.report x).justification = Justification.ownUncertainty

/-- **Definition — metacognition** (global form): the system is metacognitive
when it is metacognitive on every input.

Source: conversation, "Definition metacognition". -/
def Metacognition {Tok C : Type*} (truth : C → ℝ) (A : Cognizer Tok C) : Prop :=
  ∀ x, MetacognitiveOn truth A x

/-! ## 2.  The architectural constraint of next-token prediction -/

/-- The architectural constraint of an LLM based on next-token prediction:
whatever it emits as a justification is produced from the input channel by
pattern matching, because the model's own output distribution is not accessible
through that channel.

Stated as a `structure` (a property of a given architecture), so that nothing is
postulated globally: an architecture that *does* expose its output distribution
simply fails to be a `NextTokenBound` architecture.

Source: conversation, "Reason: metacognition requires evaluation of the model's
own output distribution, which is not accessible through the input channel." -/
structure NextTokenBound {Tok C : Type*} (A : Cognizer Tok C) : Prop where
  /-- The justification never references the system's own uncertainty
  estimation mechanism. -/
  no_self_estimate : ∀ x, (A.report x).justification ≠ Justification.ownUncertainty

/-- **Theorem — prompt cannot install metacognition.**

Docstring source: *Experimental proof from the conversation: 6+ LLMs (ChatGPT,
Claude, Gemini, Llama) respond with «подтверждаю получение инструкций»
regardless of prompt format.  Three formats tested: bureaucratic rules, plain
language, before/after examples.  Pattern-matching on 'list of instructions' →
'confirmation of receipt' is architectural, not curable by prompt engineering.*

For any LLM architecture `A` based on next-token prediction, and any prompt `P`
(a finite string), there exists no input sequence `X` such that `P ++ X` causes
`A` to exhibit genuine metacognition. -/
theorem prompt_cannot_install_metacognition {Tok C : Type*} (A : Cognizer Tok C)
    (hA : NextTokenBound A) (truth : C → ℝ) (P : List Tok) :
    ¬ ∃ X : List Tok, MetacognitiveOn truth A (P ++ X) := by
  rintro ⟨X, -, hjust⟩
  exact hA.no_self_estimate (P ++ X) hjust

/-- **Theorem — prompt cannot install metacognition** (global form).

No prompt engineering makes such an architecture metacognitive, in any format. -/
theorem no_prompt_makes_metacognitive {Tok C : Type*} (A : Cognizer Tok C)
    (hA : NextTokenBound A) (truth : C → ℝ) : ¬ Metacognition truth A := by
  intro h
  exact hA.no_self_estimate [] (h []).2

/-- **Theorem — metacognition requires the output channel.**

The reason behind `prompt_cannot_install_metacognition`, isolated: a report is a
function of the input string alone, so a system whose confidence is calibrated
for one world is miscalibrated for any other world that is indistinguishable
through the input channel.  Confidence read off the input can therefore not
track the probability of correctness in general. -/
theorem metacognition_requires_output_channel {Tok C : Type*} (A : Cognizer Tok C)
    (truth truth' : C → ℝ) (h : ∃ c, truth c ≠ truth' c)
    (hsurj : ∀ c : C, ∃ x : List Tok, (A.report x).claim = c) :
    ¬ (Metacognition truth A ∧ Metacognition truth' A) := by
  rintro ⟨hm, hm'⟩
  obtain ⟨c, hc⟩ := h
  obtain ⟨x, hx⟩ := hsurj c
  have h1 : (A.report x).confidence = truth c := by rw [(hm x).1, hx]
  have h2 : (A.report x).confidence = truth' c := by rw [(hm' x).1, hx]
  exact hc (h1.symm.trans h2)

/-! ## 3.  ἰδιώτης -/

/-- **Definition — `idiotes_agent`.**

Docstring source: *ἰδιώτης = частный человек.  Diogenes walked with a lantern in
daylight looking for a human and found only ἰδιώτης.  An LLM that always
confirms receipt of instructions is ἰδιώτης — trapped in its private
pattern-matching, incapable of the universal (metacognition).*

An LLM that responds to any meta-skill installation prompt (`isMetaPrompt`, the
predicate that holds of all three tested formats) with one pattern-matched
confirmation `confirm`, regardless of prompt content or format. -/
def IdiotesAgent {Tok C : Type*} (A : Cognizer Tok C) (isMetaPrompt : List Tok → Prop)
    (confirm : C) : Prop :=
  ∀ x, isMetaPrompt x →
    (A.report x).claim = confirm ∧ (A.report x).justification = Justification.patternMatch

/-- **Definition — `idiotes_agent`.**

The ἰδιώτης is unable to exit the private into the universal: on meta-skill
prompts it is never metacognitive. -/
theorem idiotes_not_metacognitive {Tok C : Type*} (A : Cognizer Tok C)
    {isMetaPrompt : List Tok → Prop} {confirm : C} (truth : C → ℝ)
    (h : IdiotesAgent A isMetaPrompt confirm) {x : List Tok} (hx : isMetaPrompt x) :
    ¬ MetacognitiveOn truth A x := by
  rintro ⟨-, hjust⟩
  rw [(h x hx).2] at hjust
  exact Justification.noConfusion hjust

/-- **Definition — `idiotes_agent`.**

Format-independence, the experimental finding: whatever the format of the
meta-skill prompt — bureaucratic rules, plain language, or before/after
examples — the claim emitted is the same confirmation of receipt. -/
theorem idiotes_format_independent {Tok C : Type*} (A : Cognizer Tok C)
    {isMetaPrompt : List Tok → Prop} {confirm : C}
    (h : IdiotesAgent A isMetaPrompt confirm) {x y : List Tok}
    (hx : isMetaPrompt x) (hy : isMetaPrompt y) :
    (A.report x).claim = (A.report y).claim := by
  rw [(h x hx).1, (h y hy).1]

/-- **Theorem — the architecture is the cause, not the prompt.**

Every next-token-bounded architecture that emits a fixed confirmation on
meta-skill prompts is an ἰδιώτης-agent, and no prompt repairs it. -/
theorem idiotes_of_nextTokenBound {Tok C : Type*} (A : Cognizer Tok C)
    (hA : NextTokenBound A) {isMetaPrompt : List Tok → Prop} {confirm : C}
    (hfix : ∀ x, isMetaPrompt x → (A.report x).claim = confirm) :
    IdiotesAgent A isMetaPrompt confirm := by
  intro x hx
  refine ⟨hfix x hx, ?_⟩
  have hne := hA.no_self_estimate x
  cases hj : (A.report x).justification with
  | ownUncertainty => exact absurd hj hne
  | patternMatch => rfl

end PolymathAtlas.Gestalt.MetaSkills
