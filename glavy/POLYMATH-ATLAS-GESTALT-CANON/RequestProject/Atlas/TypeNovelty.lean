import Mathlib

set_option autoImplicit false

namespace TypeNovelty

/-- An axis is a partition, represented by its equivalence relation. -/
structure Axis (Q : Type*) where
  rel : Q → Q → Prop
  refl' : Reflexive rel
  symm' : Symmetric rel
  trans' : Transitive rel

instance {Q : Type*} : CoeFun (Axis Q) (fun _ => Q → Q → Prop) := ⟨Axis.rel⟩

/-- The common refinement (intersection) of all old axes. -/
def common {Q : Type*} (O : Set (Axis Q)) (p q : Q) : Prop :=
  ∀ a ∈ O, a p q

/-- `a` refines `b`: every pair joined by `a` is also joined by `b`. -/
def Refines {Q : Type*} (a b : Q → Q → Prop) : Prop :=
  ∀ ⦃p q⦄, a p q → b p q

/-- The proposed condition 1. -/
def Cond1 {Q : Type*} (O : Set (Axis Q)) (new : Axis Q) : Prop :=
  ∃ p q, new p q ∧ ∃ a ∈ O, ¬ a p q

/-- The proposed condition 2. -/
def Cond2 {Q : Type*} (O : Set (Axis Q)) (new : Axis Q) : Prop :=
  ∃ p q, common O p q ∧ ¬ new p q

/-- Condition 1 merely says that the new partition does not refine the
intersection of the old partitions. -/
theorem cond1_iff_not_refines_common {Q : Type*} (O : Set (Axis Q)) (new : Axis Q) :
    Cond1 O new ↔ ¬ Refines new (common O) := by
  unfold Cond1 Refines common
  simp [not_forall]

/-- Condition 2 merely says that the common old refinement does not refine
 the new partition. -/
theorem cond2_iff_not_common_refines {Q : Type*} (O : Set (Axis Q)) (new : Axis Q) :
    Cond2 O new ↔ ¬ Refines (common O) new := by
  unfold Cond2 Refines common
  simp [not_forall]

/-- Thus conditions 1+2 characterize incomparability in the refinement
order; they do not by themselves characterize semantic creation of a type. -/
theorem both_iff_incomparable {Q : Type*} (O : Set (Axis Q)) (new : Axis Q) :
    Cond1 O new ∧ Cond2 O new ↔
      ¬ Refines new (common O) ∧ ¬ Refines (common O) new := by
  rw [cond1_iff_not_refines_common, cond2_iff_not_common_refines]

/-- If neither condition holds, the relations are literally equal, not merely
isomorphic. -/
theorem neither_iff_equal_common {Q : Type*} (O : Set (Axis Q)) (new : Axis Q) :
    ¬ Cond1 O new ∧ ¬ Cond2 O new ↔ new.rel = common O := by
  have h1 : ¬ Cond1 O new ↔ Refines new (common O) := by
    rw [cond1_iff_not_refines_common]
    tauto
  have h2 : ¬ Cond2 O new ↔ Refines (common O) new := by
    rw [cond2_iff_not_common_refines]
    tauto
  rw [h1, h2]
  unfold Refines
  constructor
  · intro ⟨hmn, hnm⟩
    funext p q
    exact propext ⟨@hmn p q, @hnm p q⟩
  · intro heq
    exact ⟨fun p q hpq => heq.symm ▸ hpq, fun p q hpq => heq ▸ hpq⟩

/-- The finest possible old partition (equality). -/
def equalityAxis (Q : Type*) : Axis Q where
  rel := Eq
  refl' := fun _ => rfl
  symm' := by
    intro x y h
    exact Eq.symm h
  trans' := by
    intro x y z h₁ h₂
    exact Eq.trans h₁ h₂

/-- The coarsest possible partition (one class). -/
def universalAxis (Q : Type*) : Axis Q where
  rel := fun _ _ => True
  refl' := fun _ => trivial
  symm' := by
    intro x y h
    trivial
  trans' := by
    intro x y z h₁ h₂
    trivial

/-- Contrary to the document's claim, comparison with the finest partition
does not make condition 1 impossible: a coarser new axis witnesses it. -/
theorem finest_does_not_block_cond1 :
    Cond1 ({equalityAxis Bool} : Set (Axis Bool)) (universalAxis Bool) := by
  unfold Cond1
  use true, false
  simp [universalAxis, equalityAxis]

/-- In that same example condition 2 is impossible. -/
theorem finest_blocks_cond2 :
    ¬ Cond2 ({equalityAxis Bool} : Set (Axis Bool)) (universalAxis Bool) := by
  intro ⟨p, q, _, h⟩
  exact h trivial

/-- A genuinely new binary observation added to a previously uninformative
axis is classified by the proposal as condition-2-only (“instance novelty”).
This is a counterexample to necessity under the ordinary operational meaning
of “new axis”. -/
theorem new_observation_is_only_cond2 :
    (¬ Cond1 ({universalAxis Bool} : Set (Axis Bool)) (equalityAxis Bool)) ∧
      Cond2 ({universalAxis Bool} : Set (Axis Bool)) (equalityAxis Bool) := by
  constructor
  · -- ¬ Cond1
    unfold Cond1
    simp [universalAxis, equalityAxis]
  · -- Cond2
    unfold Cond2
    use true, false
    simp [common, universalAxis, equalityAxis]

end TypeNovelty
