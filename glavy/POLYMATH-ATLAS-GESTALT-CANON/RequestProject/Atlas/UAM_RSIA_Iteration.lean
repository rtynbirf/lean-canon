import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_Environment
import RequestProject.Atlas.UAM_RSIA_Session
import RequestProject.Atlas.UAM_RSIA_Cycle

set_option autoImplicit false

/-!
# RSIA — iterative cycle composition

This file composes coherent four-phase `RSIARound`s into finite iterations.
Both numerical continue iterations and clean-exit sequences preserve the protocol
language and the Nerode-preserving invariant.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-! ### 1. Transport through one round -/

/-- After one RSIA round, the Nerode-preserving property transfers to its output. -/
theorem RSIARound.output_isNerodePreserving (r : RSIARound α)
    (h : Environment.isNerodePreserving r.input) :
    Environment.isNerodePreserving r.output := by
  exact Environment.isNerodePreserving_of_protocolLanguage_eq
    r.input r.output r.language_preserved.symm h

/-! ### 2. Numerical iteration of continue rounds -/

/-- Run `n` consecutive continue rounds, feeding each output into the next round. -/
noncomputable def Session.runNContinueRounds (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s)
    (n : Nat) : Session α :=
  match n with
  | 0 => s
  | n + 1 =>
      let round := RSIARound.fromContinue s steps hNerode
      Session.runNContinueRounds round.output steps
        (round.output_isNerodePreserving hNerode) n

@[simp] theorem Session.runNContinueRounds_zero (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) :
    s.runNContinueRounds steps hNerode 0 = s := by
  rfl

/-- Every finite continue iteration preserves the initial protocol language. -/
theorem Session.runNContinueRounds_preserves_language (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) (n : Nat) :
    (s.runNContinueRounds steps hNerode n).protocolLanguage =
      s.protocolLanguage := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      let r := RSIARound.fromContinue s steps hNerode
      exact (ih r.output (r.output_isNerodePreserving hNerode)).trans
        r.language_preserved

/-- Every finite continue iteration remains Nerode-preserving. -/
theorem Session.runNContinueRounds_isNerodePreserving (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) (n : Nat) :
    Environment.isNerodePreserving
      (s.runNContinueRounds steps hNerode n) := by
  induction n generalizing s with
  | zero => exact hNerode
  | succ n ih =>
      let r := RSIARound.fromContinue s steps hNerode
      exact ih r.output (r.output_isNerodePreserving hNerode)

/-- After at least one continue round, the session is in Construction. -/
theorem Session.runNContinueRounds_pos_phase (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) (n : Nat) :
    (s.runNContinueRounds steps hNerode (n + 1)).phase =
      .construction := by
  induction n generalizing s with
  | zero =>
      exact (RSIARound.fromContinue s steps hNerode).output_phase
  | succ n ih =>
      let r := RSIARound.fromContinue s steps hNerode
      exact ih r.output (r.output_isNerodePreserving hNerode)

/-! ### 3. Iteration of clean-exit rounds -/

/-- Run one clean-exit round for every declaration in `exits`. -/
noncomputable def Session.runExitCleanSequence (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exits : List (ExitDeclaration α))
    (hNerode : Environment.isNerodePreserving s) : Session α :=
  match exits with
  | [] => s
  | exit :: rest =>
      let round := RSIARound.fromExitClean s steps exit hNerode
      Session.runExitCleanSequence round.output steps rest
        (round.output_isNerodePreserving hNerode)

@[simp] theorem Session.runExitCleanSequence_nil (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) :
    s.runExitCleanSequence steps [] hNerode = s := by
  rfl

/-- A clean-exit sequence preserves the initial protocol language. -/
theorem Session.runExitCleanSequence_preserves_language (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exits : List (ExitDeclaration α))
    (hNerode : Environment.isNerodePreserving s) :
    (s.runExitCleanSequence steps exits hNerode).protocolLanguage =
      s.protocolLanguage := by
  induction exits generalizing s with
  | nil => rfl
  | cons exit rest ih =>
      let r := RSIARound.fromExitClean s steps exit hNerode
      exact (ih r.output (r.output_isNerodePreserving hNerode)).trans
        r.language_preserved

/-- A clean-exit sequence remains Nerode-preserving. -/
theorem Session.runExitCleanSequence_isNerodePreserving (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (exits : List (ExitDeclaration α))
    (hNerode : Environment.isNerodePreserving s) :
    Environment.isNerodePreserving
      (s.runExitCleanSequence steps exits hNerode) := by
  induction exits generalizing s with
  | nil => exact hNerode
  | cons exit rest ih =>
      let r := RSIARound.fromExitClean s steps exit hNerode
      exact ih r.output (r.output_isNerodePreserving hNerode)

/-! ### 4. Indexed continue rounds -/

/-- The round with index `k`, whose input is the session after `k` rounds. -/
noncomputable def RSIARound.nthContinueRound (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s)
    (k : Nat) : RSIARound α :=
  RSIARound.fromContinue
    (s.runNContinueRounds steps hNerode k) steps
    (s.runNContinueRounds_isNerodePreserving steps hNerode k)

@[simp] theorem RSIARound.nthContinueRound_input (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) (k : Nat) :
    (RSIARound.nthContinueRound s steps hNerode k).input =
      s.runNContinueRounds steps hNerode k := by
  rfl

/-- The output of every indexed round has the initial protocol language. -/
theorem RSIARound.nthContinueRound_language (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) (k : Nat) :
    (RSIARound.nthContinueRound s steps hNerode k).output.protocolLanguage =
      s.protocolLanguage := by
  exact (RSIARound.nthContinueRound s steps hNerode k).language_preserved.trans
    (s.runNContinueRounds_preserves_language steps hNerode k)

/-- The output of every indexed round is in Construction. -/
theorem RSIARound.nthContinueRound_phase (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) (k : Nat) :
    (RSIARound.nthContinueRound s steps hNerode k).output.phase =
      .construction := by
  exact (RSIARound.nthContinueRound s steps hNerode k).output_phase

/-! ### 5. Lists of consecutive continue rounds -/

/-- Build the first `n` consecutive continue rounds. -/
noncomputable def RSIARound.fromContinueList (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s)
    (n : Nat) : List (RSIARound α) :=
  match n with
  | 0 => []
  | n + 1 =>
      let round := RSIARound.fromContinue s steps hNerode
      round :: RSIARound.fromContinueList round.output steps
        (round.output_isNerodePreserving hNerode) n

@[simp] theorem RSIARound.fromContinueList_length (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) (n : Nat) :
    (RSIARound.fromContinueList s steps hNerode n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      let r := RSIARound.fromContinue s steps hNerode
      simp only [RSIARound.fromContinueList, List.length_cons]
      rw [ih r.output (r.output_isNerodePreserving hNerode)]

/-- Every round in the list has output language equal to the initial language. -/
theorem RSIARound.fromContinueList_all_preserve_language (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) (n : Nat) :
    ∀ r ∈ RSIARound.fromContinueList s steps hNerode n,
      r.output.protocolLanguage = s.protocolLanguage := by
  induction n generalizing s with
  | zero =>
      intro r hr
      contradiction
  | succ n ih =>
      let first := RSIARound.fromContinue s steps hNerode
      intro r hr
      simp only [RSIARound.fromContinueList, List.mem_cons] at hr
      cases hr with
      | inl h =>
          rw [h]
          exact first.language_preserved
      | inr h =>
          exact (ih first.output (first.output_isNerodePreserving hNerode)
            r h).trans first.language_preserved

/-- The first round in a nonempty list starts at the initial session. -/
theorem RSIARound.fromContinueList_head_input (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) (n : Nat) :
    ((RSIARound.fromContinueList s steps hNerode (n + 1)).get
      ⟨0, by rw [RSIARound.fromContinueList_length]; exact Nat.zero_lt_succ n⟩).input = s := by
  rfl

/-- Adjacent rounds are coherent: the earlier output is the later input.
    Finite indices are used instead of `get!`, since `RSIARound α` has no
    artificial default inhabitant. -/
theorem RSIARound.fromContinueList_coherent (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) (n i : Nat)
    (hi : i + 1 < n) :
    let rounds := RSIARound.fromContinueList s steps hNerode n
    (rounds.get ⟨i, by rw [RSIARound.fromContinueList_length]; exact Nat.lt_of_succ_lt hi⟩).output =
      (rounds.get ⟨i + 1, by rw [RSIARound.fromContinueList_length]; exact hi⟩).input := by
  induction n generalizing s i with
  | zero => exact (Nat.not_lt_zero (i + 1) hi).elim
  | succ n ih =>
      cases i with
      | zero =>
          cases n with
          | zero => exact (Nat.lt_irrefl 1 hi).elim
          | succ n =>
              simp [RSIARound.fromContinueList, RSIARound.fromContinue]
      | succ i =>
          let r := RSIARound.fromContinue s steps hNerode
          exact ih r.output (r.output_isNerodePreserving hNerode) i (Nat.lt_of_succ_lt_succ hi)

end UAM_RSIA
