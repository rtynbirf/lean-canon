import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RSIA_System
import RequestProject.Atlas.UAM_RSIA_Branch
import RequestProject.Atlas.UAM_RSIA_ForkTree

set_option autoImplicit false

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- A finite index naming one component of a parallel system. -/
abbrev SessionLabel := Nat

/-- A finite family of independently executing RSIA states. -/
structure ParallelSystem (α : Type u) where
  sessions : List (RSIAState α)
  sessions_nerode : ∀ st ∈ sessions,
    Environment.isNerodePreserving st.session

/-- One addressed instruction in an interleaved execution. -/
structure ParallelStep (α : Type u) where
  label : SessionLabel
  instruction : RoundInstruction α

abbrev ParallelTrace (α : Type u) := List (ParallelStep α)

/-- Execute one instruction in a state. -/
noncomputable def RSIAState.runInstruction (st : RSIAState α)
    (instruction : RoundInstruction α) : RSIAState α :=
  st.runInstructions [instruction]

/-- Execute one addressed step, failing exactly when its label is out of range. -/
noncomputable def ParallelSystem.step (sys : ParallelSystem α)
    (ps : ParallelStep α) : Option (ParallelSystem α) :=
  if h : ps.label < sys.sessions.length then
    let next := (sys.sessions.get ⟨ps.label, h⟩).runInstruction ps.instruction
    some {
      sessions := sys.sessions.set ps.label next
      sessions_nerode := by
        intro st _
        exact st.isNerodePreserving }
  else none

/-- Execute an interleaving; invalid labels are skipped. -/
noncomputable def ParallelSystem.runTrace (sys : ParallelSystem α) :
    ParallelTrace α → ParallelSystem α
  | [] => sys
  | ps :: rest =>
      match sys.step ps with
      | some sys' => sys'.runTrace rest
      | none => sys.runTrace rest

/-- Every addressed step in a trace is valid at the point where it executes. -/
inductive ParallelSystem.TraceWellFormed :
    ParallelSystem α → ParallelTrace α → Prop where
  | nil (sys : ParallelSystem α) : sys.TraceWellFormed []
  | cons (sys : ParallelSystem α) (ps : ParallelStep α)
      (rest : ParallelTrace α) (sys' : ParallelSystem α)
      (hLabel : ps.label < sys.sessions.length)
      (hStep : sys.step ps = some sys')
      (hRest : sys'.TraceWellFormed rest) :
      sys.TraceWellFormed (ps :: rest)

theorem ParallelSystem.step_sessions
    (sys : ParallelSystem α) (ps : ParallelStep α)
    (sys' : ParallelSystem α) (hStep : sys.step ps = some sys') :
    sys'.sessions = sys.sessions.set ps.label
      ((sys.sessions.get ⟨ps.label, by
        unfold ParallelSystem.step at hStep
        split at hStep
        · assumption
        · contradiction⟩).runInstruction ps.instruction) := by
  have hp := congrArg (Option.map ParallelSystem.sessions) hStep
  unfold ParallelSystem.step at hp
  split at hp
  · simpa using hp.symm
  · contradiction

@[simp] theorem ParallelSystem.step_length
    (sys : ParallelSystem α) (ps : ParallelStep α)
    (sys' : ParallelSystem α) (hStep : sys.step ps = some sys') :
    sys'.sessions.length = sys.sessions.length := by
  rw [sys.step_sessions ps sys' hStep, List.length_set]

/-- A valid step leaves every non-addressed component unchanged. -/
theorem ParallelSystem.step_preserves_other_languages
    (sys : ParallelSystem α) (ps : ParallelStep α)
    (sys' : ParallelSystem α) (hStep : sys.step ps = some sys')
    (j : Nat) (hj : j < sys.sessions.length) (hNe : j ≠ ps.label) :
    (sys'.sessions.get ⟨j, sys.step_length ps sys' hStep ▸ hj⟩).session.protocolLanguage =
      (sys.sessions.get ⟨j, hj⟩).session.protocolLanguage := by
  have he : sys'.sessions[j]'(by
      simpa [sys.step_length ps sys' hStep] using hj) =
      sys.sessions[j]'hj := by
    simp [sys.step_sessions ps sys' hStep,
      List.getElem_set_of_ne (Ne.symm hNe)]
  exact congrArg (fun st => st.session.protocolLanguage) he

/-- The addressed state changes, but its protocol language does not. -/
theorem ParallelSystem.step_preserves_own_language
    (sys : ParallelSystem α) (ps : ParallelStep α)
    (sys' : ParallelSystem α) (hStep : sys.step ps = some sys')
    (hLabel : ps.label < sys.sessions.length) :
    (sys'.sessions.get ⟨ps.label, sys.step_length ps sys' hStep ▸ hLabel⟩).session.protocolLanguage =
      (sys.sessions.get ⟨ps.label, hLabel⟩).session.protocolLanguage := by
  have he : sys'.sessions[ps.label]'(by
      simpa [sys.step_length ps sys' hStep] using hLabel) =
      (sys.sessions[ps.label]'hLabel).runInstruction ps.instruction := by
    simp [sys.step_sessions ps sys' hStep]
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rw [he]
  exact (sys.sessions.get ⟨ps.label, hLabel⟩).main_theorem [ps.instruction]

/-- Every successful addressed step preserves every component language. -/
theorem ParallelSystem.step_preserves_language
    (sys : ParallelSystem α) (ps : ParallelStep α)
    (sys' : ParallelSystem α) (hStep : sys.step ps = some sys')
    (j : Nat) (hj : j < sys.sessions.length) :
    (sys'.sessions.get ⟨j, sys.step_length ps sys' hStep ▸ hj⟩).session.protocolLanguage =
      (sys.sessions.get ⟨j, hj⟩).session.protocolLanguage := by
  by_cases h : j = ps.label
  · subst j
    exact sys.step_preserves_own_language ps sys' hStep hj
  · exact sys.step_preserves_other_languages ps sys' hStep j hj h

/-- Interleaved execution never changes the number of components. -/
theorem ParallelSystem.runTrace_length (sys : ParallelSystem α)
    (trace : ParallelTrace α) (hWF : sys.TraceWellFormed trace) :
    (sys.runTrace trace).sessions.length = sys.sessions.length := by
  induction hWF with
  | nil => rfl
  | cons sys ps rest sys' hLabel hStep hRest ih =>
      simp only [ParallelSystem.runTrace, hStep]
      exact ih.trans (sys.step_length ps sys' hStep)

/-- Tensor stability: every component preserves its own language under any
well-formed interleaving. -/
theorem ParallelSystem.runTrace_preserves_all_languages
    (sys : ParallelSystem α) (trace : ParallelTrace α)
    (hWF : sys.TraceWellFormed trace) (j : Nat)
    (hj : j < sys.sessions.length) :
    ((sys.runTrace trace).sessions.get
      ⟨j, sys.runTrace_length trace hWF ▸ hj⟩).session.protocolLanguage =
      (sys.sessions.get ⟨j, hj⟩).session.protocolLanguage := by
  induction hWF generalizing j with
  | nil => rfl
  | cons sys ps rest sys' hLabel hStep hRest ih =>
      have hrun : sys.runTrace (ps :: rest) = sys'.runTrace rest := by
        simp [ParallelSystem.runTrace, hStep]
      have hlang := (ih (j := j) (by
        rw [sys.step_length ps sys' hStep]
        exact hj)).trans
        (sys.step_preserves_language ps sys' hStep j hj)
      simpa [hrun] using hlang

/-- The equivalent form with a separately supplied length equality. -/
theorem ParallelSystem.runTrace_preserves_languages'
    (sys : ParallelSystem α) (trace : ParallelTrace α)
    (hWF : sys.TraceWellFormed trace)
    (hLen : (sys.runTrace trace).sessions.length = sys.sessions.length)
    (j : Nat) (hj : j < sys.sessions.length) :
    ((sys.runTrace trace).sessions.get ⟨j, hLen ▸ hj⟩).session.protocolLanguage =
      (sys.sessions.get ⟨j, hj⟩).session.protocolLanguage := by
  exact sys.runTrace_preserves_all_languages trace hWF j hj

/-- Project a one-component parallel system to its unique state. -/
noncomputable def ParallelSystem.toSequential (sys : ParallelSystem α)
    (hLen : sys.sessions.length = 1) : RSIAState α :=
  sys.sessions.head (by
    apply List.ne_nil_of_length_pos
    rw [hLen]
    exact Nat.zero_lt_succ 0)

@[simp] theorem ParallelSystem.toSequential_singleton (st : RSIAState α)
    (hNerode : Environment.isNerodePreserving st.session) :
    ({ sessions := [st], sessions_nerode := by
         intro x hx
         simp only [List.mem_singleton] at hx
         rwa [hx] } : ParallelSystem α).toSequential rfl = st := by
  rfl

/-- The unary execution-history forest associated with all components. -/
noncomputable def ParallelSystem.toForkForest (sys : ParallelSystem α) :
    List (ForkTree α) := sys.sessions.map RSIAState.toContinueTree

/-- With no recorded rounds, every component contributes exactly a leaf. -/
theorem ParallelSystem.toForkForest_static_wellFormed
    (sys : ParallelSystem α)
    (hEmpty : ∀ st ∈ sys.sessions, st.rounds = []) :
    ∀ t ∈ sys.toForkForest, ∃ s, t = ForkTree.leaf s ∧ t.WellFormed := by
  intro t ht
  simp only [ParallelSystem.toForkForest, List.mem_map] at ht
  rcases ht with ⟨st, hst, rfl⟩
  refine ⟨st.session, st.toContinueTree_nil (hEmpty st hst), ?_⟩
  rw [st.toContinueTree_nil (hEmpty st hst)]
  exact ForkTree.WellFormed.leaf st.session

end UAM_RSIA
