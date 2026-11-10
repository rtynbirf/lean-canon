import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_RSIA_NerodeBridge
import RequestProject.Atlas.UAM_RSIA_Undecidability
import RequestProject.Atlas.UAM_RSIA_AntiEntropy
import RequestProject.Atlas.UAM_RSIA_Coordination
import RequestProject.Atlas.UAM_RSIA_FormalMindTheorem
import RequestProject.Atlas.Arithmetic_Rice

set_option autoImplicit false

/-!
# Run 31: finite witnesses and a conditional Rice bridge

The finite interpreter below is an executable artifact, not an acceptable
numbering of all partial computable functions.  The final theorem therefore
states the mathematically honest conditional result: a toy model inherits the
Rice barrier when its interpretation agrees with a standard function-code
model.
-/

namespace UAM_RSIA

open Classical
open Arithmetic_Rice

universe u
variable {α : Type u}

/-- A finite machine program.  Instructions `0`, `1`, `2`, and `3` mean halt,
increment, double, and no-op respectively. -/
abbrev Fin4Program := List Nat

/-- Four concrete terminating programs. -/
def Fin4MachineCode : Fin 4 → Fin4Program
  | 0 => [1, 0]
  | 1 => [2, 0]
  | 2 => []
  | 3 => [3, 3, 3, 0]

/-- Structurally recursive execution of a finite program. -/
def Fin4Step : Fin4Program → Nat → Nat × Bool
  | [], s => (s, true)
  | 0 :: _, s => (s, true)
  | 1 :: rest, s => Fin4Step rest (s + 1)
  | 2 :: rest, s => Fin4Step rest (2 * s)
  | 3 :: rest, s => Fin4Step rest s
  | _ :: rest, s => Fin4Step rest s

/-- Run one of the four machines from state zero. -/
def Fin4Run (code : Fin 4) : Nat × Bool :=
  Fin4Step (Fin4MachineCode code) 0

#eval Fin4Run 0
#eval Fin4Run 1
#eval Fin4Run 2
#eval Fin4Run 3

/-- Every concrete machine halts. -/
theorem Fin4_all_machines_halt :
    ∀ code : Fin 4, (Fin4Run code).2 = true := by
  decide

theorem Fin4_machine_0_state : Fin4Run 0 = (1, true) := by
  rfl

theorem Fin4_machine_1_state : Fin4Run 1 = (0, true) := by
  rfl

theorem Fin4_machine_2_state : Fin4Run 2 = (0, true) := by
  rfl

theorem Fin4_machine_3_state : Fin4Run 3 = (0, true) := by
  rfl

/-- The complete concrete execution certificate. -/
theorem Fin4_interpreter_runs :
    ∀ code : Fin 4, (Fin4Run code).2 = true ∧
      (Fin4Run 0).1 = 1 ∧ (Fin4Run 1).1 = 0 ∧
      (Fin4Run 2).1 = 0 ∧ (Fin4Run 3).1 = 0 := by
  decide

/-- A concrete total interpreter with designated identity and empty-word
programs, but without the impossible requirement that a finite toy universe
itself carry an undecidable acceptable enumeration. -/
structure ToyFunctionCodeModel (α : Type u) where
  eval : Nat → UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α
  id_code : Nat
  id_correct : ∀ w, eval id_code w = w
  nil_code : Nat
  nil_correct : ∀ w, eval nil_code w = UAM_Free.FreeMonoid.empty

/-- Nerode preservation for a toy interpreter. -/
def ToyFunctionCodeModel.isNerodePreserving
    (M : ToyFunctionCodeModel α) (L : Set (UAM_Free.FreeMonoid α))
    (code : Nat) : Prop :=
  ∀ w, UAM_RegularLanguages.nerodeRel L w (M.eval code w)

/-- Explicit positive and negative witnesses, plus language nontriviality. -/
def ToyFunctionCodeModel.Adequate
    (M : ToyFunctionCodeModel α) (L : Set (UAM_Free.FreeMonoid α)) : Prop :=
  M.isNerodePreserving L M.id_code ∧
  ¬ M.isNerodePreserving L M.nil_code ∧
  L ≠ ∅ ∧ L ≠ Set.univ

/-- Even codes act identically and odd codes return the empty word. -/
def Fin4ToyEval : Nat → UAM_Free.FreeMonoid (Fin 4) →
    UAM_Free.FreeMonoid (Fin 4) :=
  fun code w => if code % 2 = 0 then w else UAM_Free.FreeMonoid.empty

/-- The concrete toy interpreter over the four-letter alphabet. -/
def toyFin4 : ToyFunctionCodeModel (Fin 4) where
  eval := Fin4ToyEval
  id_code := 0
  id_correct := by
    intro w
    show (if 0 % 2 = 0 then w else UAM_Free.FreeMonoid.empty) = w
    rw [if_pos (by decide : (0 : Nat) % 2 = 0)]
  nil_code := 1
  nil_correct := by
    intro w
    show (if 1 % 2 = 0 then w else UAM_Free.FreeMonoid.empty) =
      UAM_Free.FreeMonoid.empty
    rw [if_neg (by decide : (1 : Nat) % 2 ≠ 0)]

/-- The language of nonempty words over `Fin 4`. -/
def Fin4NonemptyLanguage : Set (UAM_Free.FreeMonoid (Fin 4)) :=
  {w | w ≠ []}

/-- The nonempty-word language is neither empty nor universal. -/
theorem Fin4_L0_nontrivial :
    Fin4NonemptyLanguage ≠ ∅ ∧ Fin4NonemptyLanguage ≠ Set.univ := by
  constructor
  · intro h
    have hmem : [0] ∈ Fin4NonemptyLanguage := by
      intro heq
      contradiction
    rw [h] at hmem
    exact hmem
  · intro h
    have hmem : [] ∈ (Set.univ : Set (UAM_Free.FreeMonoid (Fin 4))) :=
      Set.mem_univ []
    rw [← h] at hmem
    exact hmem rfl

/-- The designated identity code preserves every Nerode class. -/
theorem Fin4_toy_id_preserves :
    toyFin4.isNerodePreserving Fin4NonemptyLanguage toyFin4.id_code := by
  intro w v
  rw [toyFin4.id_correct]

/-- The designated empty-word code fails to preserve the class of `[0]`. -/
theorem Fin4_toy_nil_breaks :
    ¬ toyFin4.isNerodePreserving Fin4NonemptyLanguage toyFin4.nil_code := by
  intro h
  have hrel := h [0] []
  rw [toyFin4.nil_correct] at hrel
  have hleft : [0] ++ [] ∈ Fin4NonemptyLanguage := by
    intro heq
    contradiction
  have hright : ¬ ([] ++ [] ∈ Fin4NonemptyLanguage) := by
    intro heq
    exact heq rfl
  exact hright (hrel.mp hleft)

/-- Concrete adequacy witnesses for the toy model. -/
theorem Fin4_toy_adequate :
    toyFin4.Adequate Fin4NonemptyLanguage := by
  exact ⟨Fin4_toy_id_preserves, Fin4_toy_nil_breaks,
    Fin4_L0_nontrivial.1, Fin4_L0_nontrivial.2⟩

/-- Agreement of a toy interpreter with an acceptable standard numbering.
The additional two fields expose the designated witnesses directly. -/
structure ToyEmbedding (α : Type u) (toy : ToyFunctionCodeModel α) where
  model : FunctionCodeModel α
  eval_agrees : ∀ code w, model.eval code w = toy.eval code w
  id_in_enum : ∀ w, model.eval toy.id_code w = w
  nil_in_enum : ∀ w,
    model.eval toy.nil_code w = UAM_Free.FreeMonoid.empty

/-- A toy model embedded interpretation-preservingly in an acceptable
numbering inherits the Rice barrier. -/
theorem toy_nerode_barrier_under_embedding
    (toy : ToyFunctionCodeModel α) (L : Set (UAM_Free.FreeMonoid α))
    (emb : ToyEmbedding α toy) (hToyAdequate : toy.Adequate L) :
    ¬ ∃ decider : Nat → Bool,
      ∀ code, decider code = true ↔ toy.isNerodePreserving L code := by
  intro hDec
  obtain ⟨decider, hdecider⟩ := hDec
  have hStdAdequate : FunctionCode.NerodeCodingAdequate emb.model L := by
    refine ⟨toy.id_code, toy.nil_code, ?_, ?_⟩
    · intro w v
      rw [emb.id_in_enum]
    · intro hNil
      apply hToyAdequate.2.1
      intro w v
      rw [← emb.eval_agrees]
      exact hNil w v
  apply FunctionCode.nerode_preservation_undecidable emb.model L hStdAdequate
  refine ⟨decider, ?_⟩
  intro code
  constructor
  · intro htrue w v
    have hToy := (hdecider code).mp htrue
    rw [emb.eval_agrees]
    exact hToy w v
  · intro hStd
    apply (hdecider code).mpr
    intro w v
    rw [← emb.eval_agrees]
    exact hStd w v

/-! ## A concrete hierarchical system over four symbols -/

/-- A permissive session whose protocol accepts every word. -/
def fin4PermissiveSession : Session (Fin 4) where
  protocol := Protocol.permissive (Fin 4)
  environment := { current := [], apply := id }
  agents := []
  phase := .construction

/-- Every environment transition preserves the unique Nerode class of the
permissive language. -/
theorem fin4PermissiveSession_nerode :
    Environment.isNerodePreserving fin4PermissiveSession := by
  intro env action continuation
  simp [fin4PermissiveSession, Session.protocolLanguage,
    Protocol.permissive_language]

/-- Head removal preserves Nerode equivalence for the permissive language. -/
theorem fin4DropHead_nerode :
    NerodePreserving fin4PermissiveSession.protocolLanguage
      (dropHeadAntiEntropy (Fin 4)).compress := by
  intro word continuation
  simp [fin4PermissiveSession, Session.protocolLanguage,
    Protocol.permissive_language]

/-- Static configuration using the concrete head-removing anti-entropy cycle. -/
def fin4PermissiveConfig :
    RSIAConfig (Fin 4) fin4PermissiveSession.protocolLanguage where
  steps := []
  antiEntropy := dropHeadAntiEntropy (Fin 4)
  antiEntropy_isNerodePreserving := fin4DropHead_nerode

/-- Initial RSIA state associated with the permissive session. -/
def fin4PermissiveState : RSIAState (Fin 4) :=
  RSIAState.init fin4PermissiveSession fin4PermissiveConfig
    fin4PermissiveSession_nerode

/-- A singleton parallel system carrying the concrete state. -/
def fin4SingletonParallelSystem : ParallelSystem (Fin 4) where
  sessions := [fin4PermissiveState]
  sessions_nerode := by
    intro st hst
    simp only [List.mem_singleton] at hst
    rw [hst]
    exact fin4PermissiveSession_nerode

/-- A concrete hierarchical parallel system over `Fin 4`.  Its sole component
is both root and leaf, so its evolution chain is reflexive. -/
def instHierarchicalParallelSystemFin4 :
    HierarchicalParallelSystem (Fin 4) where
  system := fin4SingletonParallelSystem
  rootLabel := 0
  rootLabel_in_range := by
    simp [fin4SingletonParallelSystem]
  chains := by
    intro j hj
    have hj0 : j = 0 := by
      simpa [fin4SingletonParallelSystem] using hj
    subst j
    exact EvolutionChain.nil _

/-- The hierarchical-system type is constructively inhabited over `Fin 4`. -/
theorem hierarchicalParallelSystemFin4_nonempty :
    Nonempty (HierarchicalParallelSystem (Fin 4)) :=
  ⟨instHierarchicalParallelSystemFin4⟩

/-- The concrete system satisfies the operational formal-mind configuration. -/
theorem instHierarchicalParallelSystemFin4_isFormalMind :
    RSIAIsFormalMind instHierarchicalParallelSystemFin4 := by
  exact ⟨HierarchicalParallelSystem.TraceWellFormed.nil _,
    instHierarchicalParallelSystemFin4.system.sessions_nerode,
    instHierarchicalParallelSystemFin4.chains⟩

end UAM_RSIA
