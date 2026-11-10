import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Free
import RequestProject.Atlas.UAMProject.UAM_DFAEval

namespace UAMP_NFA
universe u

open UAMP_DFAEval

/-- Nondeterministic finite automaton -/
structure NFA (α Q : Type u) [DecidableEq Q] where
  δ : Q → α → Set Q
  q₀ : Q
  F : Set Q

variable {α Q : Type u} [DecidableEq Q] (A : NFA α Q)

/-- Reachable states from q on word w (set of states) -/
def reachableFrom (A : NFA α Q) (q : Q) : UAMP_Free.FreeMonoid α → Set Q
  | [] => {q}
  | a :: w => ⋃ q' ∈ A.δ q a, reachableFrom A q' w

/-- Reachable states from initial state -/
def reachable (w : UAMP_Free.FreeMonoid α) : Set Q := reachableFrom A A.q₀ w

/-- NFA accepts w iff some reachable state is in F -/
def nfaAccepts (w : UAMP_Free.FreeMonoid α) : Prop := ∃ q ∈ reachable A w, q ∈ A.F

/-- NFA language -/
def nfaLanguage : Set (UAMP_Free.FreeMonoid α) := {w | nfaAccepts A w}

/-- Concatenation distributes over reachableFrom
(в архиве шаг индукции был оставлен без доказательства). -/
theorem reachableFrom_concat (q : Q) (w₁ w₂ : UAMP_Free.FreeMonoid α) :
    reachableFrom A q (w₁ ++ w₂) =
    ⋃ q' ∈ reachableFrom A q w₁, reachableFrom A q' w₂ := by
  induction w₁ generalizing q with
  | nil =>
    show reachableFrom A q w₂ = ⋃ q' ∈ ({q} : Set Q), reachableFrom A q' w₂
    simp
  | cons a w ih =>
    show (⋃ q' ∈ A.δ q a, reachableFrom A q' (w ++ w₂))
        = ⋃ q'' ∈ (⋃ q' ∈ A.δ q a, reachableFrom A q' w), reachableFrom A q'' w₂
    simp only [ih]
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    tauto

section Subset

variable [DecidableEq (Set Q)]

/-- Subset construction: convert NFA to DFA on power set of Q.
(Требуется разрешимость равенства множеств состояний; её можно получить из
`Classical.decEq`.) -/
def toDFA : DFA α (Set Q) where
  δ := fun S a => ⋃ q ∈ S, A.δ q a
  q₀ := {A.q₀}
  F := {S | ∃ q ∈ S, q ∈ A.F}

/-- Прогон детерминизованного автомата совпадает с объединением достижимых
множеств исходного НКА. -/
theorem toDFA_evalFrom (S : Set Q) (w : UAMP_Free.FreeMonoid α) :
    evalFrom (toDFA A) S w = ⋃ q ∈ S, reachableFrom A q w := by
  induction w generalizing S with
  | nil =>
    show S = ⋃ q ∈ S, ({q} : Set Q)
    simp
  | cons a w ih =>
    show evalFrom (toDFA A) (⋃ q ∈ S, A.δ q a) w = ⋃ q ∈ S, ⋃ q' ∈ A.δ q a, reachableFrom A q' w
    rw [ih]
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    tauto

/-- NFA language equals toDFA language
(в архиве доказательство отсутствовало). -/
theorem nfaLanguage_eq_toDFA_language :
    nfaLanguage A = language (toDFA A) := by
  ext w
  show (∃ q ∈ reachable A w, q ∈ A.F) ↔ evalFrom (toDFA A) (toDFA A).q₀ w ∈ (toDFA A).F
  rw [toDFA_evalFrom]
  show (∃ q ∈ reachableFrom A A.q₀ w, q ∈ A.F)
      ↔ ∃ q ∈ (⋃ q' ∈ ({A.q₀} : Set Q), reachableFrom A q' w), q ∈ A.F
  simp

end Subset

/-- Trivial NFA: single state, no transitions, accepts only empty word -/
def trivialNFA (α : Type u) : NFA α PUnit.{u + 1} where
  δ := fun _ _ => ∅
  q₀ := PUnit.unit
  F := {PUnit.unit}

end UAMP_NFA
