import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import RequestProject.Atlas.UAM_RSIA_Branch
import RequestProject.Atlas.UAM_RSIA_System

set_option autoImplicit false

/-!
# RSIA fork trees and dynamic protocols

This module replaces a flat fork log by a branching execution history.  It also
records explicit protocol-evolution witnesses at fork nodes.  Ordinary fork
trees retain the original RSIA language invariant; dynamic trees retain a chain
of language relations from their root to every leaf.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-! ## Ordinary fork trees -/

inductive ForkTree (α : Type u) where
  | leaf : Session α → ForkTree α
  | continue : RSIARound α → ForkTree α → ForkTree α
  | fork : ForkResult α → ForkTree α → ForkTree α → ForkTree α

namespace ForkTree

def root : ForkTree α → Session α
  | .leaf s => s
  | .continue r _ => r.input
  | .fork fr _ _ => fr.round.input

@[simp] theorem root_leaf (s : Session α) : (leaf s : ForkTree α).root = s := rfl
@[simp] theorem root_continue (r : RSIARound α) (t : ForkTree α) :
    (ForkTree.continue r t).root = r.input := rfl
@[simp] theorem root_fork (fr : ForkResult α) (t₁ t₂ : ForkTree α) :
    (ForkTree.fork fr t₁ t₂).root = fr.round.input := rfl

def depth : ForkTree α → Nat
  | .leaf _ => 0
  | .continue _ t => t.depth + 1
  | .fork _ t₁ t₂ => max t₁.depth t₂.depth + 1

def leafCount : ForkTree α → Nat
  | .leaf _ => 1
  | .continue _ t => t.leafCount
  | .fork _ t₁ t₂ => t₁.leafCount + t₂.leafCount

def forkCount : ForkTree α → Nat
  | .leaf _ => 0
  | .continue _ t => t.forkCount
  | .fork _ t₁ t₂ => t₁.forkCount + t₂.forkCount + 1

def roundCount : ForkTree α → Nat
  | .leaf _ => 0
  | .continue _ t => t.roundCount + 1
  | .fork _ t₁ t₂ => t₁.roundCount + t₂.roundCount + 1

@[simp] theorem depth_leaf (s : Session α) : (leaf s : ForkTree α).depth = 0 := rfl
@[simp] theorem depth_continue (r : RSIARound α) (t : ForkTree α) :
    (ForkTree.continue r t).depth = t.depth + 1 := rfl
@[simp] theorem leafCount_leaf (s : Session α) :
    (leaf s : ForkTree α).leafCount = 1 := rfl
@[simp] theorem leafCount_continue (r : RSIARound α) (t : ForkTree α) :
    (ForkTree.continue r t).leafCount = t.leafCount := rfl
@[simp] theorem leafCount_fork (fr : ForkResult α) (t₁ t₂ : ForkTree α) :
    (ForkTree.fork fr t₁ t₂).leafCount = t₁.leafCount + t₂.leafCount := rfl

theorem leafCount_pos (t : ForkTree α) : 0 < t.leafCount := by
  induction t <;> simp_all [leafCount]

inductive IsLeaf : ForkTree α → Session α → Prop where
  | leaf (s : Session α) : IsLeaf (.leaf s) s
  | continue (r : RSIARound α) (t : ForkTree α) (s : Session α) :
      IsLeaf t s → IsLeaf (.continue r t) s
  | forkMain (fr : ForkResult α) (t₁ t₂ : ForkTree α) (s : Session α) :
      IsLeaf t₁ s → IsLeaf (.fork fr t₁ t₂) s
  | forkBranch (fr : ForkResult α) (t₁ t₂ : ForkTree α) (s : Session α) :
      IsLeaf t₂ s → IsLeaf (.fork fr t₁ t₂) s

@[simp] theorem IsLeaf.leaf_iff (s : Session α) : IsLeaf (.leaf s) s := .leaf s

theorem IsLeaf.leaf_unique (s s' : Session α) (h : IsLeaf (.leaf s) s') : s' = s := by
  cases h
  rfl

inductive WellFormed : ForkTree α → Prop where
  | leaf (s : Session α) : WellFormed (.leaf s)
  | continue (r : RSIARound α) (t : ForkTree α) :
      r.output = t.root → t.WellFormed → WellFormed (.continue r t)
  | fork (fr : ForkResult α) (t₁ t₂ : ForkTree α) :
      fr.round.output = t₁.root → fr.branch.branch = t₂.root →
      fr.branch.branch.protocolLanguage = fr.round.input.protocolLanguage →
      t₁.WellFormed → t₂.WellFormed → WellFormed (.fork fr t₁ t₂)

/-- Every leaf in a structurally coherent static fork tree recognizes the
same protocol language as the root. -/
theorem WellFormed.leaf_protocolLanguage_eq_root
    (t : ForkTree α) (hWF : t.WellFormed) :
    ∀ s, IsLeaf t s → s.protocolLanguage = t.root.protocolLanguage := by
  induction hWF with
  | leaf s =>
      intro s' hLeaf
      cases hLeaf
      rfl
  | «continue» r t hOut hTree ih =>
      intro s hLeaf
      cases hLeaf with
      | «continue» _ _ _ hSub =>
          exact (ih s hSub).trans (congrArg Session.protocolLanguage hOut.symm |>.trans r.language_preserved)
  | fork fr t₁ t₂ hMain hBranch hLanguage hTree₁ hTree₂ ih₁ ih₂ =>
      intro s hLeaf
      cases hLeaf with
      | forkMain _ _ _ _ hSub =>
          exact (ih₁ s hSub).trans
            (congrArg Session.protocolLanguage hMain.symm |>.trans fr.round.language_preserved)
      | forkBranch _ _ _ _ hSub =>
          exact (ih₂ s hSub).trans
            (congrArg Session.protocolLanguage hBranch.symm |>.trans hLanguage)

def singleton (s : Session α) : ForkTree α := .leaf s

@[simp] theorem singleton_root (s : Session α) : (singleton s).root = s := rfl

theorem singleton_wellFormed (s : Session α) : (singleton s).WellFormed := .leaf s

noncomputable def fromContinueRound (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) : ForkTree α :=
  let r := RSIARound.fromContinue s steps hNerode
  .continue r (.leaf r.output)

theorem fromContinueRound_wellFormed (s : Session α)
    (steps : List (AgentId × UAM_Free.FreeMonoid α))
    (hNerode : Environment.isNerodePreserving s) :
    (fromContinueRound s steps hNerode).WellFormed := by
  apply WellFormed.continue
  · rfl
  · exact WellFormed.leaf _

noncomputable def fromForkResult (fr : ForkResult α) : ForkTree α :=
  .fork fr (.leaf fr.round.output) (.leaf fr.branch.branch)

theorem fromForkResult_wellFormed (fr : ForkResult α)
    (hLanguage : fr.branch.branch.protocolLanguage =
      fr.round.input.protocolLanguage) :
    (fromForkResult fr).WellFormed := by
  apply WellFormed.fork
  · rfl
  · rfl
  · exact hLanguage
  · exact WellFormed.leaf _
  · exact WellFormed.leaf _

inductive Path (α : Type u) where
  | here : Path α
  | main : Path α → Path α
  | branch : Path α → Path α

def replaceAt : ForkTree α → Path α → ForkTree α → Option (ForkTree α)
  | _, .here, t' => some t'
  | .leaf _, .main _, _ => none
  | .leaf _, .branch _, _ => none
  | .continue r t, .main p, t' => (replaceAt t p t').map (.continue r)
  | .continue _ _, .branch _, _ => none
  | .fork fr t₁ t₂, .main p, t' =>
      (replaceAt t₁ p t').map (fun t₁' => .fork fr t₁' t₂)
  | .fork fr t₁ t₂, .branch p, t' =>
      (replaceAt t₂ p t').map (fun t₂' => .fork fr t₁ t₂')

noncomputable def extendWithContinue (t : ForkTree α) (p : Path α)
    (r : RSIARound α) : Option (ForkTree α) :=
  t.replaceAt p (.continue r (.leaf r.output))

def allRounds : ForkTree α → List (RSIARound α)
  | .leaf _ => []
  | .continue r t => r :: t.allRounds
  | .fork fr t₁ t₂ => fr.round :: (t₁.allRounds ++ t₂.allRounds)

/-- Every recorded round in a coherent static tree has the root language at
both endpoints. -/
theorem WellFormed.allRounds_preserve_language (t : ForkTree α)
    (hWF : t.WellFormed) :
    ∀ r ∈ t.allRounds,
      r.input.protocolLanguage = t.root.protocolLanguage ∧
      r.output.protocolLanguage = t.root.protocolLanguage := by
  match hWF with
  | .leaf s =>
    simp [allRounds]
  | .continue r t hEq hRec =>
    simp_all [allRounds]
    refine ⟨?_, ?_⟩
    · rw [hEq.symm, r.language_preserved]
    · intro a ha
      have := allRounds_preserve_language t hRec a ha
      rw [hEq.symm, r.language_preserved] at this
      exact this
  | .fork fr t₁ t₂ hEq1 hEq2 hLang hInd1 hInd2 =>
    simp_all [allRounds]
    refine ⟨?_, ?_⟩
    · rw [hEq1.symm, fr.round.language_preserved]
    · intro a ha
      rcases ha with ha1 | ha2
      · have := allRounds_preserve_language t₁ hInd1 a ha1
        rw [hEq1.symm, fr.round.language_preserved] at this
        exact this
      · have := allRounds_preserve_language t₂ hInd2 a ha2
        rw [hLang] at this
        exact this

end ForkTree

/-! ## Explicit protocol evolutions -/

structure ProtocolEvolution (α : Type u) where
  parent : Protocol α
  child : Protocol α
  relation : Set (UAM_Free.FreeMonoid α) → Set (UAM_Free.FreeMonoid α) → Prop
  holds : relation parent.language child.language

namespace ProtocolEvolution

def parentLanguage (e : ProtocolEvolution α) : Set (UAM_Free.FreeMonoid α) :=
  e.parent.language

def childLanguage (e : ProtocolEvolution α) : Set (UAM_Free.FreeMonoid α) :=
  e.child.language

def identity (P : Protocol α) : ProtocolEvolution α where
  parent := P
  child := P
  relation := fun L₁ L₂ => L₁ = L₂
  holds := rfl

def refinement (P Q : Protocol α) (h : Q.language ⊆ P.language) :
    ProtocolEvolution α where
  parent := P
  child := Q
  relation := fun L₁ L₂ => L₂ ⊆ L₁
  holds := h

def extension (P Q : Protocol α) (h : P.language ⊆ Q.language) :
    ProtocolEvolution α where
  parent := P
  child := Q
  relation := fun L₁ L₂ => L₁ ⊆ L₂
  holds := h

@[simp] theorem identity_language_eq (P : Protocol α) :
    (identity P).parentLanguage = (identity P).childLanguage := rfl

theorem refinement_child_subset (P Q : Protocol α)
    (h : Q.language ⊆ P.language) :
    (refinement P Q h).childLanguage ⊆ (refinement P Q h).parentLanguage := h

theorem extension_parent_subset (P Q : Protocol α)
    (h : P.language ⊆ Q.language) :
    (extension P Q h).parentLanguage ⊆ (extension P Q h).childLanguage := h

def compose (e₁ e₂ : ProtocolEvolution α) (h : e₁.child = e₂.parent) :
    ProtocolEvolution α where
  parent := e₁.parent
  child := e₂.child
  relation := fun L₁ L₃ => ∃ L₂, e₁.relation L₁ L₂ ∧ e₂.relation L₂ L₃
  holds := by
    refine ⟨e₁.child.language, e₁.holds, ?_⟩
    rw [h]
    exact e₂.holds

theorem compose_refinement (P Q R : Protocol α)
    (h₁ : Q.language ⊆ P.language) (h₂ : R.language ⊆ Q.language) :
    (compose (refinement P Q h₁) (refinement Q R h₂) rfl).relation
      P.language R.language := ⟨Q.language, h₁, h₂⟩

theorem compose_extension (P Q R : Protocol α)
    (h₁ : P.language ⊆ Q.language) (h₂ : Q.language ⊆ R.language) :
    (compose (extension P Q h₁) (extension Q R h₂) rfl).relation
      P.language R.language := ⟨Q.language, h₁, h₂⟩

end ProtocolEvolution

/-! ## Dynamic fork trees -/

inductive DynamicForkTree (α : Type u) where
  | leaf : Session α → DynamicForkTree α
  | continue : RSIARound α → DynamicForkTree α → DynamicForkTree α
  | fork : ForkResult α → ProtocolEvolution α →
      DynamicForkTree α → DynamicForkTree α → DynamicForkTree α

namespace DynamicForkTree

def root : DynamicForkTree α → Session α
  | .leaf s => s
  | .continue r _ => r.input
  | .fork fr _ _ _ => fr.round.input

def toForkTree : DynamicForkTree α → ForkTree α
  | .leaf s => .leaf s
  | .continue r t => .continue r t.toForkTree
  | .fork fr _ t₁ t₂ => .fork fr t₁.toForkTree t₂.toForkTree

@[simp] theorem root_toForkTree (t : DynamicForkTree α) :
    t.toForkTree.root = t.root := by cases t <;> rfl

inductive IsLeaf : DynamicForkTree α → Session α → Prop where
  | leaf (s : Session α) : IsLeaf (.leaf s) s
  | continue (r : RSIARound α) (t : DynamicForkTree α) (s : Session α) :
      IsLeaf t s → IsLeaf (.continue r t) s
  | forkMain (fr : ForkResult α) (e : ProtocolEvolution α)
      (t₁ t₂ : DynamicForkTree α) (s : Session α) :
      IsLeaf t₁ s → IsLeaf (.fork fr e t₁ t₂) s
  | forkBranch (fr : ForkResult α) (e : ProtocolEvolution α)
      (t₁ t₂ : DynamicForkTree α) (s : Session α) :
      IsLeaf t₂ s → IsLeaf (.fork fr e t₁ t₂) s

inductive WellFormed : DynamicForkTree α → Prop where
  | leaf (s : Session α) : WellFormed (.leaf s)
  | continue (r : RSIARound α) (t : DynamicForkTree α) :
      t.WellFormed → t.root = r.output → WellFormed (.continue r t)
  | fork (fr : ForkResult α) (e : ProtocolEvolution α)
      (t₁ t₂ : DynamicForkTree α) :
      e.parent = fr.round.input.protocol →
      e.child = fr.branch.branch.protocol →
      t₁.WellFormed → t₁.root = fr.round.output →
      t₂.WellFormed → t₂.root = fr.branch.branch →
      WellFormed (.fork fr e t₁ t₂)

/-- Dynamic trees whose fork branches retain the parent language can be
viewed as ordinary static trees. -/
inductive IsStatic : DynamicForkTree α → Prop where
  | leaf (s : Session α) : IsStatic (.leaf s)
  | continue (r : RSIARound α) (t : DynamicForkTree α) :
      t.IsStatic → IsStatic (.continue r t)
  | fork (fr : ForkResult α) (e : ProtocolEvolution α)
      (t₁ t₂ : DynamicForkTree α) :
      fr.branch.branch.protocolLanguage = fr.round.input.protocolLanguage →
      t₁.IsStatic → t₂.IsStatic → IsStatic (.fork fr e t₁ t₂)

theorem WellFormed.toForkTree_WellFormed (t : DynamicForkTree α)
    (h : t.WellFormed) (hStatic : t.IsStatic) :
    t.toForkTree.WellFormed := by
  induction h with
  | leaf s => exact ForkTree.WellFormed.leaf s
  | «continue» r t hWF hRoot ih =>
      cases hStatic with
      | «continue» _ _ hStatic' =>
          exact ForkTree.WellFormed.continue r t.toForkTree
            (by simpa using hRoot.symm) (ih hStatic')
  | fork fr e t₁ t₂ hParent hChild hWF₁ hRoot₁ hWF₂ hRoot₂ ih₁ ih₂ =>
      cases hStatic with
      | fork _ _ _ _ hLanguage hStatic₁ hStatic₂ =>
          exact ForkTree.WellFormed.fork fr t₁.toForkTree t₂.toForkTree
            (by simpa using hRoot₁.symm) (by simpa using hRoot₂.symm)
            hLanguage (ih₁ hStatic₁) (ih₂ hStatic₂)

end DynamicForkTree

/-- A chain records ordinary language-preserving execution edges and explicit
protocol-evolution edges.  Keeping endpoints as languages avoids identifying
protocol records that happen to recognize the same language. -/
inductive EvolutionChain (α : Type u) :
    Set (UAM_Free.FreeMonoid α) → Set (UAM_Free.FreeMonoid α) → Prop where
  | nil (L : Set (UAM_Free.FreeMonoid α)) : EvolutionChain α L L
  | preserve {L₁ L₂ L₃ : Set (UAM_Free.FreeMonoid α)} :
      L₁ = L₂ → EvolutionChain α L₂ L₃ → EvolutionChain α L₁ L₃
  | evolve (e : ProtocolEvolution α) {L : Set (UAM_Free.FreeMonoid α)} :
      EvolutionChain α e.childLanguage L → EvolutionChain α e.parentLanguage L

namespace DynamicForkTree

/-- Every leaf of a coherent dynamic tree is connected to the root by a chain
of language-preserving execution edges and declared evolution edges. -/
theorem WellFormed.leaf_evolution_chain (t : DynamicForkTree α)
    (hWF : t.WellFormed) :
    ∀ s, IsLeaf t s →
      EvolutionChain α t.root.protocolLanguage s.protocolLanguage := by
  intro s hLeaf
  induction hWF generalizing s with
  | leaf s' =>
    cases hLeaf
    exact EvolutionChain.nil _
  | fork fr e t₁ t₂ hParent hChild hWF₁ hEq₁ hWF₂ hEq₂ ih₁ ih₂ =>
    match hLeaf with
    | .forkMain _ _ _ _ _ hLeaf' =>
      have hChain := ih₁ s hLeaf'
      rw [hEq₁] at hChain
      rw [root]
      exact EvolutionChain.preserve (fr.round.language_preserved.symm) hChain
    | .forkBranch _ _ _ _ _ hLeaf' =>
      have hChain := ih₂ s hLeaf'
      rw [hEq₂] at hChain
      rw [root]
      have hParentLang : fr.round.input.protocolLanguage = e.parentLanguage := by
        simp only [Session.protocolLanguage, ProtocolEvolution.parentLanguage]
        rw [hParent]
      have hChildLang : fr.branch.branch.protocolLanguage = e.childLanguage := by
        simp only [Session.protocolLanguage, ProtocolEvolution.childLanguage]
        rw [hChild]
      rw [hParentLang]
      exact EvolutionChain.evolve e (hChildLang ▸ hChain)
  | _ r t' hWF' hEq ih =>
    match hLeaf with
    | .continue _ _ _ hLeaf' =>
      have hChain := ih s hLeaf'
      rw [hEq] at hChain
      rw [root]
      exact EvolutionChain.preserve (r.language_preserved.symm) hChain

end DynamicForkTree

/-! ## Bridge from the flat state record -/

/-- Turn a chronological list of main-line rounds into a unary tree. -/
def ForkTree.ofRounds : List (RSIARound α) → Session α → ForkTree α
  | [], s => .leaf s
  | r :: rest, _ => .continue r (ofRounds rest r.output)

/-- A view of the main-line round log as a (possibly unchecked) unary tree.
The state record certifies languages of rounds but intentionally does not store
adjacency equalities, so structural `WellFormed` is not claimed for arbitrary
values constructed directly with the public `RSIAState` constructor. -/
noncomputable def RSIAState.toContinueTree (st : RSIAState α) : ForkTree α :=
  ForkTree.ofRounds st.rounds st.session

@[simp] theorem RSIAState.toContinueTree_nil (st : RSIAState α)
    (hRounds : st.rounds = []) : st.toContinueTree = .leaf st.session := by
  simp [toContinueTree, hRounds, ForkTree.ofRounds]

end UAM_RSIA
