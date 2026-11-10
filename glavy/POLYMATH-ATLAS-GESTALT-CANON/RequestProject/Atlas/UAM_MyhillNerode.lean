import Mathlib.Data.Fintype.Quotient
import Mathlib.Tactic
import RequestProject.Atlas.UAM_RegularLanguages

/-!
# The Myhill--Nerode theorem for right quotients

This module packages the right Nerode relation as a setoid, constructs its
canonical DFA, and proves that a language is recognized by a finite DFA exactly
when its type of right Nerode classes is finite.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_MyhillNerode

open UAM_DFAEval UAM_RegularLanguages
open Classical

universe u

variable {α Q : Type u}

/-- The setoid of words indistinguishable by every right continuation. -/
def languageNerodeSetoid (L : Set (UAM_Free.FreeMonoid α)) :
    Setoid (UAM_Free.FreeMonoid α) where
  r := nerodeRel L
  iseqv := ⟨nerodeRel_refl L, fun h => nerodeRel_symm L _ _ h,
    fun h₁ h₂ => nerodeRel_trans L _ _ _ h₁ h₂⟩

/-- The type of right Nerode equivalence classes of `L`. -/
abbrev NerodeClass (L : Set (UAM_Free.FreeMonoid α)) :=
  Quotient (languageNerodeSetoid L)

/-- Appending the same word preserves right Nerode equivalence. -/
theorem nerodeRel_append_left (L : Set (UAM_Free.FreeMonoid α))
    {w₁ w₂ : UAM_Free.FreeMonoid α} (h : nerodeRel L w₁ w₂)
    (x : UAM_Free.FreeMonoid α) : nerodeRel L (w₁ ++ x) (w₂ ++ x) := by
  intro v
  simpa only [List.append_assoc] using h (x ++ v)

/-- The transition on Nerode classes induced by appending one letter. -/
noncomputable def nerodeTransition (L : Set (UAM_Free.FreeMonoid α))
    (q : NerodeClass L) (a : α) : NerodeClass L :=
  Quotient.map (fun w => w ++ [a])
    (fun _ _ h => by
      change nerodeRel L _ _ at h ⊢
      exact nerodeRel_append_left L h [a]) q

/-- The canonical DFA of a language, whose states are its right Nerode classes. -/
noncomputable def canonicalDFA (L : Set (UAM_Free.FreeMonoid α)) :
    DFA α (NerodeClass L) where
  δ := nerodeTransition L
  q₀ := Quotient.mk (languageNerodeSetoid L) []
  F := {q | Quotient.lift (fun w => w ∈ L)
    (fun _ _ h => by
      change nerodeRel L _ _ at h
      simpa only [List.append_nil] using h []) q}

/-- Evaluation in the canonical DFA appends the input word to a representative. -/
theorem canonicalDFA_evalFrom (L : Set (UAM_Free.FreeMonoid α))
    (p w : UAM_Free.FreeMonoid α) :
    (canonicalDFA L).evalFrom (Quotient.mk (languageNerodeSetoid L) p) w =
      Quotient.mk (languageNerodeSetoid L) (p ++ w) := by
  induction w generalizing p with
  | nil => simp only [DFA.evalFrom, List.append_nil]
  | cons a ws ih =>
      change (canonicalDFA L).evalFrom
        (Quotient.mk (languageNerodeSetoid L) (p ++ [a])) ws = _
      rw [ih]
      simp only [List.append_assoc, List.singleton_append]

/-- The canonical DFA recognizes exactly its defining language. -/
theorem canonicalDFA_language (L : Set (UAM_Free.FreeMonoid α)) :
    (canonicalDFA L).language = L := by
  ext w
  change (canonicalDFA L).eval w ∈ (canonicalDFA L).F ↔ w ∈ L
  rw [show (canonicalDFA L).eval w =
    Quotient.mk (languageNerodeSetoid L) w by
      simpa only [List.nil_append] using canonicalDFA_evalFrom L [] w]
  rfl

/-- Every right Nerode class has a representative selected from a DFA state
reached by that representative. -/
private noncomputable def stateToNerodeClass (L : Set (UAM_Free.FreeMonoid α))
    [DecidableEq Q] (A : DFA α Q) (q : Q) : NerodeClass L :=
  if h : ∃ w, A.eval w = q then
    Quotient.mk (languageNerodeSetoid L) (Classical.choose h)
  else Quotient.mk (languageNerodeSetoid L) []

/-- If `A` recognizes `L`, its state type surjects onto the right Nerode classes
of `L`. Unreachable states may be sent to the class of the empty word. -/
theorem stateToNerodeClass_surjective (L : Set (UAM_Free.FreeMonoid α))
    [DecidableEq Q] (A : DFA α Q) (hL : A.language = L) :
    Function.Surjective (stateToNerodeClass L A) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro w
  let hReach : ∃ v, A.eval v = A.eval w := ⟨w, rfl⟩
  refine ⟨A.eval w, ?_⟩
  rw [stateToNerodeClass, dif_pos hReach]
  apply Quotient.sound
  have hEval : A.eval (Classical.choose hReach) = A.eval w :=
    Classical.choose_spec hReach
  have hNerode : nerodeRel A.language (Classical.choose hReach) w :=
    UAM_RegularLanguages.DFA.dfa_nerode_of_eval_eq A _ _ hEval
  simpa only [hL] using hNerode

/-- Recognition by a finite DFA implies finite index of the right Nerode
relation. -/
noncomputable def fintypeNerodeClassOfDFA (L : Set (UAM_Free.FreeMonoid α))
    [DecidableEq Q] [Fintype Q] (A : DFA α Q) (hL : A.language = L) :
    Fintype (NerodeClass L) :=
  Fintype.ofSurjective (stateToNerodeClass L A)
    (stateToNerodeClass_surjective L A hL)

/-- **Myhill--Nerode theorem.** A language is recognized by a finite DFA if and
only if its right Nerode relation has finite index. -/
theorem recognizable_iff_finite_nerode (L : Set (UAM_Free.FreeMonoid α)) :
    (∃ (Q : Type u) (_ : Fintype Q) (_ : DecidableEq Q)
      (A : DFA α Q), A.language = L) ↔ Nonempty (Fintype (NerodeClass L)) := by
  constructor
  · rintro ⟨Q, finiteQ, decidableQ, A, hL⟩
    letI : Fintype Q := finiteQ
    letI : DecidableEq Q := decidableQ
    exact ⟨fintypeNerodeClassOfDFA L A hL⟩
  · rintro ⟨finiteClasses⟩
    letI : Fintype (NerodeClass L) := finiteClasses
    exact ⟨NerodeClass L, inferInstance, Quotient.decidableEq, canonicalDFA L,
      canonicalDFA_language L⟩

end UAM_MyhillNerode
