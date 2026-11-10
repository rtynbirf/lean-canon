import Mathlib.Tactic
import RequestProject.Atlas.UAM_Thompson
import RequestProject.Atlas.UAM_Kleene
import RequestProject.Atlas.UAM_KleeneCounterexample

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_KleeneComplete

noncomputable section
open Classical

open UAM_RegularExpression UAM_RegularExpression.RegExp
open UAM_RegularLanguages UAM_DFAEval UAM_NFA UAM_EpsilonNFA
open UAM_Thompson UAM_Kleene

universe u

/-- Thompson construction followed by epsilon removal and subset construction. -/
def regexToDFA {α : Type u} (r : RegExp α) [Fintype α] :
    @DFA α (Set (ThompsonState r)) (Classical.decEq _) :=
  ((thompsonNFA r).toNFA).toDFA

/-- The compiled DFA accepts exactly the language denoted by the expression. -/
theorem regexToDFA_language {α : Type u} (r : RegExp α)
    [Fintype α] [DecidableEq α] :
    (regexToDFA r).language = languageOf r := by
  rw [regexToDFA, UAM_NFA.NFA.nfaLanguage_eq_toDFA_language,
    UAM_EpsilonNFA.EpsilonNFA.epsilonLanguage_eq_nfa_language,
    UAM_Thompson.thompson_correct]

/-- A finite union of the one-letter expressions whose transition from `i`
ends at `j`. -/
def transitionRegex {α Q : Type u} [Fintype α] [DecidableEq α] [DecidableEq Q]
    (A : DFA α Q) (i j : Q) : RegExp α :=
  Finset.univ.toList.foldl (fun r a =>
    .alt r (if A.δ i a = j then .atom a else .empty_set)) .empty_set

/-- The initial generalized transition label between two states. -/
def baseRegex {α Q : Type u} [Fintype α] [DecidableEq α] [DecidableEq Q]
    (A : DFA α Q) (i j : Q) : RegExp α :=
  if i = j then .alt .empty_str (transitionRegex (A := A) i j)
  else transitionRegex (A := A) i j

/-- State-elimination recurrence.  `pathRegex A ks i j` describes paths from
`i` to `j` whose intermediate states occur in `ks`. -/
def pathRegex {α Q : Type u} [Fintype α] [DecidableEq α] [DecidableEq Q]
    (A : DFA α Q) : List Q → Q → Q → RegExp α
  | [], i, j => baseRegex A i j
  | k :: ks, i, j =>
      .alt (pathRegex A ks i j)
        (.concat (pathRegex A ks i k)
          (.concat (.star (pathRegex A ks k k)) (pathRegex A ks k j)))

/-- The expression produced by eliminating all states and taking the union of
paths from the initial state to an accepting state. -/
def dfaRegex {α Q : Type u} [Fintype α] [DecidableEq α]
    [Fintype Q] [DecidableEq Q] (A : DFA α Q) : RegExp α :=
  Finset.univ.toList.foldl (fun r q => .alt r
    (if q ∈ A.F then pathRegex A Finset.univ.toList A.q₀ q else .empty_set)) .empty_set

/-
The transition-label expression recognizes exactly the appropriate one-letter words.
-/
private theorem transitionRegex_language {α Q : Type u} [Fintype α] [DecidableEq α]
    [DecidableEq Q] (A : DFA α Q) (i j : Q) :
    languageOf (transitionRegex A i j) =
      {w | ∃ a : α, w = [a] ∧ A.δ i a = j} := by
  unfold transitionRegex
  have h_expand : ∀ (l : List α),
      languageOf (List.foldl (fun r a =>
        r.alt (if A.δ i a = j then atom a else empty_set)) empty_set l) =
        {w : UAM_Free.FreeMonoid α | ∃ a ∈ l, w = [a] ∧ A.δ i a = j} := by
    intro l
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l a ih =>
        rw [List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, languageOf_alt]
        rw [ih]
        by_cases h : A.δ i a = j
        · ext w
          simp only [h, if_pos, languageOf_atom, Set.mem_union,
            Set.mem_setOf_eq, Set.mem_singleton_iff, List.mem_append,
            List.mem_singleton]
          constructor
          · rintro (⟨b, hbl, rfl, hbj⟩ | rfl)
            · exact ⟨b, Or.inl hbl, rfl, hbj⟩
            · exact ⟨a, Or.inr rfl, rfl, h⟩
          · rintro ⟨b, hb | rfl, rfl, hbj⟩
            · exact Or.inl ⟨b, hb, rfl, hbj⟩
            · exact Or.inr rfl
        · rw [if_neg h]
          ext w
          simp only [languageOf_empty_set, Set.mem_union,
            Set.mem_setOf_eq, Set.mem_empty_iff_false, or_false,
            List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨b, hbl, rfl, hbj⟩
            exact ⟨b, Or.inl hbl, rfl, hbj⟩
          · rintro ⟨b, hb | rfl, rfl, hbj⟩
            · exact ⟨b, hb, rfl, hbj⟩
            · exact (h hbj).elim
  rw [h_expand]
  ext w
  simp

/-
A base generalized edge is either an identity epsilon edge or one DFA step.
-/
private theorem baseRegex_language {α Q : Type u} [Fintype α] [DecidableEq α]
    [DecidableEq Q] (A : DFA α Q) (i j : Q) :
    languageOf (baseRegex A i j) =
      {w | (w = [] ∧ i = j) ∨ ∃ a : α, w = [a] ∧ A.δ i a = j} := by
  unfold baseRegex
  by_cases h : i = j
  · rw [if_pos h, languageOf_alt, transitionRegex_language]
    ext w
    simp [h]
  · rw [if_neg h, transitionRegex_language]
    ext w
    simp [h]

/- Relational semantics of the state-elimination recurrence. -/
mutual
  inductive EliminatedPath {α Q : Type u} [DecidableEq Q] (A : DFA α Q) :
      List Q → Q → UAM_Free.FreeMonoid α → Q → Prop
    | base_nil (i : Q) : EliminatedPath A [] i [] i
    | base_atom (i : Q) (a : α) : EliminatedPath A [] i [a] (A.δ i a)
    | old {ks : List Q} (k i j : Q) {w} :
        EliminatedPath A ks i w j → EliminatedPath A (k :: ks) i w j
    | through {ks : List Q} (k i j : Q) {w₁ w₂ w₃} :
        EliminatedPath A ks i w₁ k →
        RepeatedPath A ks k w₂ →
        EliminatedPath A ks k w₃ j →
        EliminatedPath A (k :: ks) i (w₁ ++ w₂ ++ w₃) j

  inductive RepeatedPath {α Q : Type u} [DecidableEq Q] (A : DFA α Q) :
      List Q → Q → UAM_Free.FreeMonoid α → Prop
    | empty (ks : List Q) (k : Q) : RepeatedPath A ks k []
    | word {ks : List Q} {k : Q} {w} :
        EliminatedPath A ks k w k → RepeatedPath A ks k w
    | concat {ks : List Q} {k : Q} {w₁ w₂} :
        RepeatedPath A ks k w₁ → RepeatedPath A ks k w₂ →
        RepeatedPath A ks k (w₁ ++ w₂)
end

private theorem repeatedPath_iff_kleeneStar {α Q : Type u} [DecidableEq Q]
    (A : DFA α Q) (ks : List Q) (k : Q) (w : UAM_Free.FreeMonoid α) :
    RepeatedPath A ks k w ↔ KleeneStar {v | EliminatedPath A ks k v k} w := by
  constructor
  · let rec forward {w : UAM_Free.FreeMonoid α}
        (h : RepeatedPath A ks k w) :
        KleeneStar {v | EliminatedPath A ks k v k} w :=
      match h with
      | .empty _ _ => KleeneStar.empty
      | .word hp => KleeneStar.word _ hp
      | .concat h₁ h₂ => KleeneStar.concat _ _ (forward h₁) (forward h₂)
    exact forward
  · intro h
    induction h with
    | empty => exact RepeatedPath.empty ks k
    | word w hw => exact RepeatedPath.word hw
    | concat w₁ w₂ h₁ h₂ ih₁ ih₂ => exact RepeatedPath.concat ih₁ ih₂

private theorem pathRegex_language_aux {α Q : Type u} [Fintype α] [DecidableEq α]
    [DecidableEq Q] (A : DFA α Q) (ks : List Q) (i j : Q) :
    languageOf (pathRegex A ks i j) = {w | EliminatedPath A ks i w j} := by
  induction' ks with k ks ih generalizing i j;
  · rw [pathRegex, baseRegex_language]
    ext w
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨a, rfl, h⟩)
      · exact EliminatedPath.base_nil i
      · exact h ▸ EliminatedPath.base_atom i a
    · intro hp
      cases hp with
      | base_nil => exact Or.inl ⟨rfl, rfl⟩
      | base_atom i a => exact Or.inr ⟨a, rfl, rfl⟩
  · simp +decide [ pathRegex, languageOf ];
    simp +decide only [ih, languageConcat, kleeneStar];
    ext w; simp;
    constructor;
    · rintro ( h | ⟨ w1, w2, w3, rfl, h1, h2, h3 ⟩ );
      · exact EliminatedPath.old k i j h;
      · convert EliminatedPath.through k i j _ _ _ using 1;
        rw [ List.append_assoc ];
        · exact h1;
        · exact (repeatedPath_iff_kleeneStar A ks k w2).mpr h2;
        · exact h3;
    · rintro ( h | ⟨ w1, w2, w3, hw, hw1, hw2, hw3 ⟩ ) <;> simp_all +decide [ ← List.append_assoc ];
      exact Or.inr ⟨ _, _, _, rfl, by assumption, by exact ( repeatedPath_iff_kleeneStar A ks k _ ).mp ‹_›, by assumption ⟩

private theorem eliminatedPath_sound {α Q : Type u} [DecidableEq Q]
    (A : DFA α Q) {ks : List Q} {i j : Q} {w : UAM_Free.FreeMonoid α}
    (h : EliminatedPath A ks i w j) : A.evalFrom i w = j := by
  apply EliminatedPath.rec
    (motive_1 := fun _ i w j _ => A.evalFrom i w = j)
    (motive_2 := fun _ k w _ => A.evalFrom k w = k)
  · intro i
    rfl
  · intro i a
    rfl
  · intro ks k i j w h ih
    exact ih
  · intro ks k i j w₁ w₂ w₃ h₁ h₂ h₃ ih₁ ih₂ ih₃
    rw [A.evalFrom_concat, A.evalFrom_concat, ih₁, ih₂, ih₃]
  · intro ks k
    rfl
  · intro ks k w h ih
    exact ih
  · intro ks k w₁ w₂ h₁ h₂ ih₁ ih₂
    rw [A.evalFrom_concat, ih₁, ih₂]
  · exact h

private theorem eliminatedPath_lift {α Q : Type u} [DecidableEq Q]
    (A : DFA α Q) {ks : List Q} {i j : Q} {w : UAM_Free.FreeMonoid α}
    (h : EliminatedPath A [] i w j) : EliminatedPath A ks i w j := by
  induction ks with
  | nil => exact h
  | cons k ks ih => exact EliminatedPath.old k i j ih

private theorem eliminatedPath_append_of_mem {α Q : Type u} [DecidableEq Q]
    (A : DFA α Q) {ks : List Q} {i k j : Q}
    {w₁ w₂ : UAM_Free.FreeMonoid α} (hk : k ∈ ks)
    (h₁ : EliminatedPath A ks i w₁ k)
    (h₂ : EliminatedPath A ks k w₂ j) :
    EliminatedPath A ks i (w₁ ++ w₂) j := by
  induction ks generalizing i k j w₁ w₂ with
  | nil => cases hk
  | cons q qs ih =>
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · cases h₁ with
        | old _ _ _ hp₁ =>
          cases h₂ with
          | old _ _ _ hp₂ =>
            simpa using EliminatedPath.through k i j hp₁
              (RepeatedPath.empty qs k) hp₂
          | through _ _ _ hp₂ hloop₂ hsuffix₂ =>
            simpa [List.append_assoc] using
              EliminatedPath.through k i j hp₁
                (RepeatedPath.concat (RepeatedPath.word hp₂) hloop₂) hsuffix₂
        | through _ _ _ hp₁ hloop₁ hsuffix₁ =>
          cases h₂ with
          | old _ _ _ hp₂ =>
            simpa [List.append_assoc] using
              EliminatedPath.through k i j hp₁
                (RepeatedPath.concat hloop₁ (RepeatedPath.word hsuffix₁)) hp₂
          | through _ _ _ hp₂ hloop₂ hsuffix₂ =>
            simpa [List.append_assoc] using
              EliminatedPath.through k i j hp₁
                (RepeatedPath.concat hloop₁
                  (RepeatedPath.concat (RepeatedPath.word hsuffix₁)
                    (RepeatedPath.concat (RepeatedPath.word hp₂) hloop₂))) hsuffix₂
      · cases h₁ with
        | old _ _ _ hp₁ =>
          cases h₂ with
          | old _ _ _ hp₂ => exact EliminatedPath.old q i j (ih hk hp₁ hp₂)
          | through _ _ _ hp₂ hloop hsuffix =>
            have hprefix := ih hk hp₁ hp₂
            have hres := EliminatedPath.through q i j hprefix hloop hsuffix
            simpa [List.append_assoc] using hres
        | through _ _ _ hp₁ hloop hsuffix =>
          cases h₂ with
          | old _ _ _ hp₂ =>
            have htail := ih (i := q) (k := k) (j := j) hk hsuffix hp₂
            have hres := EliminatedPath.through q i j hp₁ hloop htail
            simpa [List.append_assoc] using hres
          | through _ _ _ hp₂ hloop₂ hsuffix₂ =>
            have hmiddle := ih (i := q) (k := k) (j := q) hk hsuffix hp₂
            have hloops := RepeatedPath.concat hloop
              (RepeatedPath.concat (RepeatedPath.word hmiddle) hloop₂)
            have hres := EliminatedPath.through q i j hp₁ hloops hsuffix₂
            simpa [List.append_assoc] using hres

private theorem eliminatedPath_complete_univ {α Q : Type u} [DecidableEq Q]
    [Fintype Q] (A : DFA α Q) (i : Q) (w : UAM_Free.FreeMonoid α) :
    EliminatedPath A Finset.univ.toList i w (A.evalFrom i w) := by
  induction w generalizing i with
  | nil => exact eliminatedPath_lift A (EliminatedPath.base_nil i)
  | cons a w ih =>
      have hfirst : EliminatedPath A Finset.univ.toList i [a] (A.δ i a) :=
        eliminatedPath_lift A (EliminatedPath.base_atom i a)
      have hrest := ih (A.δ i a)
      have hmem : A.δ i a ∈ Finset.univ.toList := by simp
      simpa using eliminatedPath_append_of_mem A hmem hfirst hrest

private theorem foldl_alt_language {α β : Type u} (l : List β)
    (f : β → RegExp α) (r : RegExp α) :
    languageOf (l.foldl (fun acc b => .alt acc (f b)) r) =
      languageOf r ∪ {w | ∃ b ∈ l, w ∈ languageOf (f b)} := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, languageOf_alt, ih]
      ext w
      simp [or_left_comm, or_comm]

/-- Correctness of finite state elimination. -/
theorem dfaRegex_language {α Q : Type u} [Fintype α] [DecidableEq α]
    [Fintype Q] [DecidableEq Q] (A : DFA α Q) :
    languageOf (dfaRegex A) = A.language := by
  unfold dfaRegex
  rw [foldl_alt_language]
  ext w
  simp only [languageOf_empty_set, Set.mem_union, Set.mem_empty_iff_false,
    false_or, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, hqu, hq⟩
    by_cases hqF : q ∈ A.F
    · rw [if_pos hqF, pathRegex_language_aux] at hq
      change A.evalFrom A.q₀ w ∈ A.F
      rw [eliminatedPath_sound A hq]
      exact hqF
    · rw [if_neg hqF, languageOf_empty_set] at hq
      exact hq.elim
  · intro hw
    change A.evalFrom A.q₀ w ∈ A.F at hw
    exact ⟨A.evalFrom A.q₀ w, by simp, by
      rw [if_pos hw, pathRegex_language_aux]
      exact eliminatedPath_complete_univ A A.q₀ w⟩

/-- Every language accepted by a finite DFA over a finite alphabet is denoted
by a regular expression. -/
theorem dfa_language_is_regular {α Q : Type u} [Fintype α] [DecidableEq α]
    [Fintype Q] [DecidableEq Q] (A : DFA α Q) :
    IsRegularLanguage A.language := by
  exact ⟨dfaRegex A, dfaRegex_language A⟩

/-- Full Kleene theorem for finite alphabets.  The alphabet-finiteness
hypothesis is essential, as shown by `UAM_KleeneCounterexample`. -/
theorem kleene_complete {α : Type u} [Fintype α] [DecidableEq α]
    (L : Set (UAM_Free.FreeMonoid α)) :
    IsRegularLanguage L ↔ ∃ (Q : Type u) (_ : Fintype Q) (_ : DecidableEq Q)
      (A : DFA α Q), A.language = L := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨Set (ThompsonState r), inferInstance, inferInstance,
      regexToDFA r, regexToDFA_language r⟩
  · rintro ⟨Q, hQ, dQ, A, rfl⟩
    exact dfa_language_is_regular A

end
end UAM_KleeneComplete