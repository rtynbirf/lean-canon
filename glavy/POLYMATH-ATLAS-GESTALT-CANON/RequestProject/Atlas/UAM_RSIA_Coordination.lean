import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_Parallel
import RequestProject.Atlas.UAM_RSIA_ProtocolHierarchy

set_option autoImplicit false

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- Transport both endpoints of an evolution chain along language equality. -/
def EvolutionChain.transport
    {L₁ L₂ L₁' L₂' : Set (UAM_Free.FreeMonoid α)}
    (c : EvolutionChain α L₁ L₂) (h₁ : L₁' = L₁) (h₂ : L₂ = L₂') :
    EvolutionChain α L₁' L₂' :=
  EvolutionChain.preserve h₁
    (c.append (EvolutionChain.preserve h₂ (EvolutionChain.nil L₂')))

/-- Parallel execution equipped with a root-to-component evolution chain. -/
structure HierarchicalParallelSystem (α : Type u) where
  system : ParallelSystem α
  rootLabel : SessionLabel
  rootLabel_in_range : rootLabel < system.sessions.length
  chains : ∀ (j : Nat) (hj : j < system.sessions.length),
    EvolutionChain α
      ((system.sessions.get ⟨rootLabel, rootLabel_in_range⟩).session.protocolLanguage)
      ((system.sessions.get ⟨j, hj⟩).session.protocolLanguage)

abbrev HierarchicalStep (α : Type u) := ParallelStep α

/-- Execute one hierarchy-preserving parallel step. -/
noncomputable def HierarchicalParallelSystem.step
    (hps : HierarchicalParallelSystem α) (hs : HierarchicalStep α) :
    Option (HierarchicalParallelSystem α) :=
  match h : hps.system.step hs with
  | none => none
  | some sys' => some {
      system := sys'
      rootLabel := hps.rootLabel
      rootLabel_in_range := by
        rw [hps.system.step_length hs sys' h]
        exact hps.rootLabel_in_range
      chains := by
        intro j hj
        have hjOld : j < hps.system.sessions.length := by
          rwa [hps.system.step_length hs sys' h] at hj
        have hRoot := hps.system.step_preserves_language hs sys' h
          hps.rootLabel hps.rootLabel_in_range
        have hLeaf := hps.system.step_preserves_language hs sys' h j hjOld
        exact (hps.chains j hjOld).transport hRoot hLeaf.symm }

noncomputable def HierarchicalParallelSystem.runTrace
    (hps : HierarchicalParallelSystem α) :
    List (HierarchicalStep α) → HierarchicalParallelSystem α
  | [] => hps
  | hs :: rest =>
      match hps.step hs with
      | some hps' => hps'.runTrace rest
      | none => hps.runTrace rest

inductive HierarchicalParallelSystem.TraceWellFormed :
    HierarchicalParallelSystem α → List (HierarchicalStep α) → Prop where
  | nil (hps : HierarchicalParallelSystem α) : hps.TraceWellFormed []
  | cons (hps : HierarchicalParallelSystem α) (hs : HierarchicalStep α)
      (rest : List (HierarchicalStep α)) (hps' : HierarchicalParallelSystem α)
      (hStep : hps.step hs = some hps')
      (hRest : hps'.TraceWellFormed rest) :
      hps.TraceWellFormed (hs :: rest)

/-- The hierarchy wrapper changes no session data beyond its underlying step. -/
theorem HierarchicalParallelSystem.step_system
    (hps : HierarchicalParallelSystem α) (hs : HierarchicalStep α)
    (hps' : HierarchicalParallelSystem α) (hStep : hps.step hs = some hps') :
    hps.system.step hs = some hps'.system := by
  unfold HierarchicalParallelSystem.step at hStep
  split at hStep
  · contradiction
  · simp only [Option.some.injEq] at hStep
    subst hps'
    assumption

/-- One hierarchical step preserves the number of sessions. -/
theorem HierarchicalParallelSystem.step_length
    (hps : HierarchicalParallelSystem α) (hs : HierarchicalStep α)
    (hps' : HierarchicalParallelSystem α) (hStep : hps.step hs = some hps') :
    hps'.system.sessions.length = hps.system.sessions.length := by
  exact hps.system.step_length hs hps'.system (hps.step_system hs hps' hStep)

/-- One hierarchical step preserves every component language. -/
theorem HierarchicalParallelSystem.step_preserves_all_languages
    (hps : HierarchicalParallelSystem α) (hs : HierarchicalStep α)
    (hps' : HierarchicalParallelSystem α) (hStep : hps.step hs = some hps')
    (j : Nat) (hj : j < hps.system.sessions.length) :
    (hps'.system.sessions.get
      ⟨j, hps.step_length hs hps' hStep ▸ hj⟩).session.protocolLanguage =
      (hps.system.sessions.get ⟨j, hj⟩).session.protocolLanguage := by
  exact hps.system.step_preserves_language hs hps'.system
    (hps.step_system hs hps' hStep) j hj

/-- Well-formed hierarchical execution preserves session count. -/
theorem HierarchicalParallelSystem.runTrace_length
    (hps : HierarchicalParallelSystem α) (trace : List (HierarchicalStep α))
    (hWF : hps.TraceWellFormed trace) :
    (hps.runTrace trace).system.sessions.length = hps.system.sessions.length := by
  induction hWF with
  | nil => rfl
  | cons hps hs rest hps' hStep hRest ih =>
      have hrun : hps.runTrace (hs :: rest) = hps'.runTrace rest := by
        simp [HierarchicalParallelSystem.runTrace, hStep]
      rw [hrun]
      exact ih.trans (hps.step_length hs hps' hStep)

/-- Every component language is stable throughout a well-formed hierarchical
interleaving. -/
theorem HierarchicalParallelSystem.runTrace_preserves_languages
    (hps : HierarchicalParallelSystem α) (trace : List (HierarchicalStep α))
    (hWF : hps.TraceWellFormed trace) (j : Nat)
    (hj : j < hps.system.sessions.length) :
    ((hps.runTrace trace).system.sessions.get
      ⟨j, hps.runTrace_length trace hWF ▸ hj⟩).session.protocolLanguage =
      (hps.system.sessions.get ⟨j, hj⟩).session.protocolLanguage := by
  induction hWF generalizing j with
  | nil => rfl
  | cons hps hs rest hps' hStep hRest ih =>
      have hrun : hps.runTrace (hs :: rest) = hps'.runTrace rest := by
        simp [HierarchicalParallelSystem.runTrace, hStep]
      have hlang := (ih (j := j) (by
        rw [hps.step_length hs hps' hStep]
        exact hj)).trans
        (hps.step_preserves_all_languages hs hps' hStep j hj)
      simpa [hrun] using hlang

/-- The central diamond invariant: all languages are stable and every final
component still carries a certified chain from the final root. -/
theorem HierarchicalParallelSystem.runTrace_diamond_invariant
    (hps : HierarchicalParallelSystem α) (trace : List (HierarchicalStep α))
    (hWF : hps.TraceWellFormed trace) :
    (∀ j, (hj : j < hps.system.sessions.length) →
      ((hps.runTrace trace).system.sessions.get
        ⟨j, hps.runTrace_length trace hWF ▸ hj⟩).session.protocolLanguage =
        (hps.system.sessions.get ⟨j, hj⟩).session.protocolLanguage) ∧
    (∀ j, (hj : j < (hps.runTrace trace).system.sessions.length) →
      EvolutionChain α
        (((hps.runTrace trace).system.sessions.get
          ⟨(hps.runTrace trace).rootLabel,
            (hps.runTrace trace).rootLabel_in_range⟩).session.protocolLanguage)
        (((hps.runTrace trace).system.sessions.get ⟨j, hj⟩).session.protocolLanguage)) := by
  constructor
  · exact hps.runTrace_preserves_languages trace hWF
  · exact (hps.runTrace trace).chains

/-- The designated root language is stable. -/
theorem HierarchicalParallelSystem.runTrace_preserves_root_language
    (hps : HierarchicalParallelSystem α) (trace : List (HierarchicalStep α))
    (hWF : hps.TraceWellFormed trace) :
    ((hps.runTrace trace).system.sessions.get
      ⟨hps.rootLabel, hps.runTrace_length trace hWF ▸ hps.rootLabel_in_range⟩).session.protocolLanguage =
      (hps.system.sessions.get
        ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage := by
  exact hps.runTrace_preserves_languages trace hWF hps.rootLabel
    hps.rootLabel_in_range

/-- Static hierarchy means observational equality with the designated root. -/
def HierarchicalParallelSystem.IsStatic
    (hps : HierarchicalParallelSystem α) : Prop :=
  ∀ (j : Nat) (hj : j < hps.system.sessions.length),
    (hps.system.sessions.get ⟨j, hj⟩).session.protocolLanguage =
      (hps.system.sessions.get
        ⟨hps.rootLabel, hps.rootLabel_in_range⟩).session.protocolLanguage

end UAM_RSIA
