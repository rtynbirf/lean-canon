import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import RequestProject.Atlas.UAM_MinimalDFA
import RequestProject.Atlas.UAM_MyhillNerode

/-!
# Uniqueness and cardinal minimality of reduced accessible DFAs

A reduced DFA is taken here in the standard trim sense: every state is reachable
from the initial state, and distinct states are distinguishable by a continuation.
The reachability clause is necessary: without it, arbitrary unreachable,
pairwise distinguishable states can be added without changing the language.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM_MinimalUnique

open UAM_DFAEval UAM_DFAHomomorphism UAM_MyhillNerode
open Classical

universe u

variable {α Q Q₁ Q₂ : Type u}
variable [DecidableEq Q] [DecidableEq Q₁] [DecidableEq Q₂]

/-- Every state of the DFA is reachable from its initial state. -/
def IsAccessible (A : DFA α Q) : Prop :=
  ∀ q, ∃ w : UAM_Free.FreeMonoid α, A.eval w = q

/-- No two distinct states have the same continuation language. -/
def IsStateReduced (A : DFA α Q) : Prop :=
  ∀ q r, stateNerodeRel A q r → q = r

/-- A reduced DFA: accessible and with pairwise distinguishable states. -/
def IsReduced (A : DFA α Q) : Prop :=
  IsAccessible A ∧ IsStateReduced A

/-- Isomorphism of DFAs, including initial and accepting states. -/
structure DFAIso (A : DFA α Q₁) (B : DFA α Q₂) where
  toEquiv : Q₁ ≃ Q₂
  map_q₀ : toEquiv A.q₀ = B.q₀
  map_δ : ∀ q a, toEquiv (A.δ q a) = B.δ (toEquiv q) a
  map_F : ∀ q, q ∈ A.F ↔ toEquiv q ∈ B.F

namespace CanonicalMap

variable (A : DFA α Q) (hacc : IsAccessible A)

/-- A chosen word reaching a given state. -/
noncomputable def word (q : Q) : UAM_Free.FreeMonoid α :=
  Classical.choose (hacc q)

theorem eval_word (q : Q) : A.eval (word A hacc q) = q :=
  Classical.choose_spec (hacc q)

/-- Send a reachable state to the Nerode class of a word reaching it. -/
noncomputable def toClass (L : Set (UAM_Free.FreeMonoid α)) (q : Q) : NerodeClass L :=
  Quotient.mk (languageNerodeSetoid L) (word A hacc q)

end CanonicalMap

/-- The canonical map from an accessible recognizing DFA onto Nerode classes is
surjective. -/
theorem canonicalMap_surjective (L : Set (UAM_Free.FreeMonoid α))
    (A : DFA α Q) (hacc : IsAccessible A) (hL : A.language = L) :
    Function.Surjective (CanonicalMap.toClass A hacc L) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro w
  refine ⟨A.eval w, ?_⟩
  apply Quotient.sound
  have heval : A.eval (CanonicalMap.word A hacc (A.eval w)) = A.eval w :=
    CanonicalMap.eval_word A hacc (A.eval w)
  have hn := UAM_RegularLanguages.DFA.dfa_nerode_of_eval_eq A _ _ heval
  simpa only [hL] using hn

/-- For a state-reduced accessible recognizing DFA, the canonical map is
injective. -/
theorem canonicalMap_injective (L : Set (UAM_Free.FreeMonoid α))
    (A : DFA α Q) (hacc : IsAccessible A) (hred : IsStateReduced A)
    (hL : A.language = L) :
    Function.Injective (CanonicalMap.toClass A hacc L) := by
  intro q r hqr
  apply hred q r
  intro v
  have hn : UAM_RegularLanguages.nerodeRel L
      (CanonicalMap.word A hacc q) (CanonicalMap.word A hacc r) :=
    Quotient.exact hqr
  have hv : A.eval (CanonicalMap.word A hacc q ++ v) ∈ A.F ↔
      A.eval (CanonicalMap.word A hacc r ++ v) ∈ A.F := by
    change CanonicalMap.word A hacc q ++ v ∈ A.language ↔
      CanonicalMap.word A hacc r ++ v ∈ A.language
    rw [hL]
    exact iff_of_eq (hn v)
  change A.evalFrom q v ∈ A.F ↔ A.evalFrom r v ∈ A.F
  rw [← CanonicalMap.eval_word A hacc q,
    ← CanonicalMap.eval_word A hacc r]
  simpa only [DFA.eval_concat] using hv

/-- The canonical map preserves all DFA structure. -/
noncomputable def canonicalMap_isHom (L : Set (UAM_Free.FreeMonoid α))
    (A : DFA α Q) (hacc : IsAccessible A) (hL : A.language = L) :
    DFAHom A (canonicalDFA L) := by
  let f := CanonicalMap.toClass A hacc L
  refine {
    toFun := f
    map_q₀ := ?_
    map_δ := ?_
    map_F := ?_
  }
  · apply Quotient.sound
    have heval : A.eval (CanonicalMap.word A hacc A.q₀) = A.eval [] := by
      rw [CanonicalMap.eval_word A hacc A.q₀]
      rfl
    have hn := UAM_RegularLanguages.DFA.dfa_nerode_of_eval_eq A _ _ heval
    simpa only [hL] using hn
  · intro q a
    apply Quotient.sound
    have heval : A.eval (CanonicalMap.word A hacc (A.δ q a)) =
        A.eval (CanonicalMap.word A hacc q ++ [a]) := by
      rw [CanonicalMap.eval_word A hacc (A.δ q a), A.eval_concat,
        CanonicalMap.eval_word A hacc q]
      rfl
    have hn := UAM_RegularLanguages.DFA.dfa_nerode_of_eval_eq A _ _ heval
    simpa only [hL] using hn
  · intro q
    change q ∈ A.F ↔ CanonicalMap.word A hacc q ∈ L
    rw [← hL]
    change q ∈ A.F ↔ A.eval (CanonicalMap.word A hacc q) ∈ A.F
    rw [CanonicalMap.eval_word A hacc q]

/-- Every reduced DFA recognizing `L` is isomorphic to its canonical Nerode DFA. -/
noncomputable def reducedIsoCanonical (L : Set (UAM_Free.FreeMonoid α))
    (A : DFA α Q) (hred : IsReduced A) (hL : A.language = L) :
    DFAIso A (canonicalDFA L) := by
  let hom := canonicalMap_isHom L A hred.1 hL
  let equiv := Equiv.ofBijective hom.toFun
    ⟨canonicalMap_injective L A hred.1 hred.2 hL,
      canonicalMap_surjective L A hred.1 hL⟩
  exact {
    toEquiv := equiv
    map_q₀ := hom.map_q₀
    map_δ := hom.map_δ
    map_F := hom.map_F
  }

/-- **Uniqueness of minimal DFAs.** Any two reduced DFAs recognizing the same
language are isomorphic, up to renaming states. -/
noncomputable def reducedDFA_unique (A₁ : DFA α Q₁) (A₂ : DFA α Q₂)
    (h₁ : IsReduced A₁) (h₂ : IsReduced A₂)
    (hL : A₁.language = A₂.language) : DFAIso A₁ A₂ := by
  let i₁ := reducedIsoCanonical A₁.language A₁ h₁ rfl
  let i₂ := reducedIsoCanonical A₁.language A₂ h₂ hL.symm
  let e : Q₁ ≃ Q₂ := i₁.toEquiv.trans i₂.toEquiv.symm
  refine {
    toEquiv := e
    map_q₀ := ?_
    map_δ := ?_
    map_F := ?_
  }
  · change i₂.toEquiv.symm (i₁.toEquiv A₁.q₀) = A₂.q₀
    rw [i₁.map_q₀]
    exact i₂.toEquiv.injective (by simp only [Equiv.apply_symm_apply, i₂.map_q₀])
  · intro q a
    change i₂.toEquiv.symm (i₁.toEquiv (A₁.δ q a)) =
      A₂.δ (i₂.toEquiv.symm (i₁.toEquiv q)) a
    apply i₂.toEquiv.injective
    rw [Equiv.apply_symm_apply, i₁.map_δ, i₂.map_δ]
    simp only [Equiv.apply_symm_apply]
  · intro q
    change q ∈ A₁.F ↔ i₂.toEquiv.symm (i₁.toEquiv q) ∈ A₂.F
    rw [i₁.map_F]
    have hi := i₂.map_F (i₂.toEquiv.symm (i₁.toEquiv q))
    rw [i₂.toEquiv.apply_symm_apply] at hi
    exact hi.symm

/-- A total map from DFA states onto language classes, using a chosen reaching
word when one exists and the empty word otherwise. -/
private noncomputable def arbitraryStateToClass (L : Set (UAM_Free.FreeMonoid α))
    (A : DFA α Q) (q : Q) : NerodeClass L :=
  if h : ∃ w, A.eval w = q then
    Quotient.mk (languageNerodeSetoid L) (Classical.choose h)
  else Quotient.mk (languageNerodeSetoid L) []

private theorem arbitraryStateToClass_surjective
    (L : Set (UAM_Free.FreeMonoid α)) (A : DFA α Q)
    (hL : A.language = L) :
    Function.Surjective (arbitraryStateToClass L A) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro w
  let hr : ∃ v, A.eval v = A.eval w := ⟨w, rfl⟩
  refine ⟨A.eval w, ?_⟩
  rw [arbitraryStateToClass, dif_pos hr]
  apply Quotient.sound
  have heval : A.eval (Classical.choose hr) = A.eval w := Classical.choose_spec hr
  have hn := UAM_RegularLanguages.DFA.dfa_nerode_of_eval_eq A _ _ heval
  simpa only [hL] using hn

/-- The canonical Nerode DFA has no more states than any finite DFA recognizing
its language. No accessibility or reducedness assumption is needed here. -/
theorem canonicalDFA_card_le (L : Set (UAM_Free.FreeMonoid α))
    (A : DFA α Q) [Fintype Q] [Fintype (NerodeClass L)]
    (hL : A.language = L) :
    Fintype.card (NerodeClass L) ≤ Fintype.card Q := by
  exact Fintype.card_le_of_surjective (arbitraryStateToClass L A)
    (arbitraryStateToClass_surjective L A hL)

end UAM_MinimalUnique
