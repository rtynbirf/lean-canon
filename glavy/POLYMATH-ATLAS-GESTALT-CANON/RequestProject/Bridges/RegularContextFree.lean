/-
# Мост UAM: регулярные языки ⊆ контекстно-свободные

Слой регулярных языков (DFA, Майхилл–Нероуд, минимизация) и новый
контекстно-свободный слой (`RequestProject/UAM_ContextFree.lean`) соединяются
явной конструкцией **праволинейной грамматики** детерминированного автомата:

    q → a · δ(q,a)      для каждого входного символа a
    q → ε               если q допускающее

Доказано `dfa_language_eq_grammar_language`: язык грамматики автомата в
точности совпадает с языком автомата, откуда `regular_subset_contextFree` —
каждый регулярный язык контекстно-свободен, и `regular_subset_pda` —
каждый регулярный язык распознаётся автоматом с магазинной памятью.

Обратное включение неверно (язык `aⁿbⁿ` контекстно-свободен); нерегулярность
`aⁿbⁿ` здесь не доказывается и не утверждается.
-/
import Mathlib
import RequestProject.UAM_ContextFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM.ContextFree

universe u

variable {α σ : Type u}

/-- Праволинейная грамматика детерминированного автомата. -/
def ofDFA (M : DFA α σ) : Grammar σ α where
  rule q β :=
    (β = [] ∧ q ∈ M.accept) ∨ (∃ a : α, β = [Sum.inr a, Sum.inl (M.step q a)])
  start := M.start

/-- Ключевая лемма: из нетерминала-состояния выводятся ровно те слова, которые
переводят автомат в допускающее состояние. -/
theorem yields_ofDFA_iff (M : DFA α σ) :
    ∀ (w : List α) (q : σ),
      Yields (ofDFA M) [Sum.inl q] w ↔ M.evalFrom q w ∈ M.accept := by
  intro w
  induction w with
  | nil =>
      intro q
      constructor
      · intro h
        have key : ∀ v : List α, v = [] →
            Yields (ofDFA M) [Sum.inl q] v → q ∈ M.accept := by
          intro v hv hy
          cases hy with
          | nonterm hr hβ hrest =>
              rcases hr with ⟨rfl, hacc⟩ | ⟨a, rfl⟩
              · exact hacc
              · cases hβ with
                | term h' => simp at hv
        simpa [DFA.evalFrom] using key [] rfl h
      · intro h
        have hy : Yields (ofDFA M) [Sum.inl q] ([] ++ []) :=
          Yields.nonterm (Or.inl ⟨rfl, by simpa [DFA.evalFrom] using h⟩)
            Yields.nil Yields.nil
        simpa using hy
  | cons a w ih =>
      intro q
      constructor
      · intro h
        have key : ∀ v : List α, v = a :: w →
            Yields (ofDFA M) [Sum.inl q] v → M.evalFrom (M.step q a) w ∈ M.accept := by
          intro v hv hy
          cases hy with
          | nonterm hr hβ hrest =>
              rcases hr with ⟨rfl, hacc⟩ | ⟨b, rfl⟩
              · cases hβ
                cases hrest
                simp at hv
              · cases hβ with
                | term h' =>
                    cases hrest
                    simp only [List.append_nil, List.cons.injEq] at hv
                    obtain ⟨hba, hu⟩ := hv
                    subst hba
                    subst hu
                    exact (ih (M.step q b)).mp h'
        simpa [DFA.evalFrom_cons] using key (a :: w) rfl h
      · intro h
        have hbody : Yields (ofDFA M) [Sum.inr a, Sum.inl (M.step q a)] (a :: w) := by
          refine Yields.term ?_
          have hw : Yields (ofDFA M) [Sum.inl (M.step q a)] w :=
            (ih (M.step q a)).mpr (by simpa [DFA.evalFrom_cons] using h)
          simpa using hw
        have hy := Yields.nonterm (g := ofDFA M) (A := q) (α := [])
          (Or.inr ⟨a, rfl⟩) hbody Yields.nil
        simpa using hy

/-- **Язык праволинейной грамматики автомата совпадает с языком автомата.** -/
theorem dfa_language_eq_grammar_language (M : DFA α σ) :
    (ofDFA M).language = M.accepts := by
  ext w
  exact yields_ofDFA_iff M w M.start

/-- **Каждый регулярный язык контекстно-свободен.** -/
theorem regular_subset_contextFree (L : Set (List α))
    (h : ∃ (σ : Type u) (M : DFA α σ), M.accepts = L) :
    ∃ (N : Type u) (g : Grammar N α), g.language = L := by
  obtain ⟨σ, M, rfl⟩ := h
  exact ⟨σ, ofDFA M, dfa_language_eq_grammar_language M⟩

/-- **Каждый регулярный язык распознаётся автоматом с магазинной памятью**
(композиция моста с эквивалентностью CFG ≡ PDA). -/
theorem regular_subset_pda (L : Set (List α))
    (h : ∃ (σ : Type u) (M : DFA α σ), M.accepts = L) :
    ∃ (Γ : Type u) (P : PDA Γ α), P.language = L := by
  obtain ⟨N, g, hg⟩ := regular_subset_contextFree L h
  exact ⟨N ⊕ α, g.toPDA, by rw [pda_language_toPDA g, hg]⟩

end UAM.ContextFree
