import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_FinalTheorem
import RequestProject.Atlas.UAM_RSIA_ConstrainedCapstone
import RequestProject.Atlas.UAM_RSIA_ConstrainedFormalMind

set_option autoImplicit false

/-!
# RSIA project closure: unifying vacuous and non-vacuous paths

This file formally connects the original `FinalCapstone` with the non-vacuous
`ConstrainedFinalPackage`. It proves that the original global formal-mind
condition can only hold on trivial component languages, while the constrained
path has a concrete nonempty, non-universal `Fin 4` instance. At the universal
language, the constrained local invariant promotes to the original global one.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- If all words are Nerode-related for a language, the language is empty or
universal. -/
theorem Environment.nerode_all_related_implies_trivial
    (s : Session α)
    (hAll : ∀ (w₁ w₂ : UAM_Free.FreeMonoid α),
      UAM_RegularLanguages.nerodeRel s.protocolLanguage w₁ w₂) :
    s.protocolLanguage = ∅ ∨ s.protocolLanguage = Set.univ := by
  by_cases hEmpty : s.protocolLanguage = ∅
  · exact Or.inl hEmpty
  · right
    apply Set.eq_univ_of_forall
    intro w
    have hNonempty : s.protocolLanguage.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨v₀, hv₀⟩ := hNonempty
    have hRel := hAll v₀ w []
    simp only [List.append_nil] at hRel
    exact Eq.mp hRel hv₀

/-- The original globally quantified invariant forces the session language to
be empty or universal. -/
theorem Environment.isNerodePreserving_trivial_only
    (s : Session α)
    (hNP : Environment.isNerodePreserving s) :
    s.protocolLanguage = ∅ ∨ s.protocolLanguage = Set.univ := by
  apply Environment.nerode_all_related_implies_trivial s
  intro w₁ w₂
  exact hNP { current := w₁, apply := fun _ => w₂ } w₂

/-- An original hierarchy containing a component with a nonempty,
non-universal language cannot satisfy `RSIAIsFormalMind`. -/
theorem oldPath_vacuous_for_nontrivial
    (hps : HierarchicalParallelSystem α)
    (hNontrivial : ∃ st ∈ hps.system.sessions,
      st.session.protocolLanguage ≠ ∅ ∧
      st.session.protocolLanguage ≠ Set.univ) :
    ¬ RSIAIsFormalMind hps := by
  intro hFM
  obtain ⟨st, hMem, hNotEmpty, hNotUniv⟩ := hNontrivial
  have hTrivial := Environment.isNerodePreserving_trivial_only st.session
    (hFM.2.1 st hMem)
  cases hTrivial with
  | inl h => exact hNotEmpty h
  | inr h => exact hNotUniv h

/-- At the universal language, each constrained local invariant promotes to
its original globally quantified counterpart. -/
theorem ConstrainedCapstone.local_promotes_to_global_at_univ
    (cap : ConstrainedCapstone α)
    (hUniv : ∀ state ∈ cap.hps.system.sessions,
      state.session.protocolLanguage = Set.univ) :
    ∀ state ∈ cap.hps.system.sessions,
      Environment.isNerodePreserving state.session :=
  ConstrainedCapstone.local_implies_global_when_univ cap hUniv

/-- The constrained path has a concrete formal-mind certificate with a
nonempty, non-universal root language and Nerode-preserving compression. -/
theorem constrained_superior_to_old :
    ∃ (cap : ConstrainedCapstone (Fin 4)),
      cap.rootLanguage ≠ ∅ ∧ cap.rootLanguage ≠ Set.univ ∧
      ConstrainedRSIAIsFormalMind cap.hps ∧
      RuleUnmisunderstandable cap.rootLanguage cap.rootCompress := by
  exact ⟨constrainedCapstoneFin4,
    constrainedCapstoneFin4_language_nontrivial.1,
    constrainedCapstoneFin4_language_nontrivial.2,
    instConstrainedHPSFin4_isFormalMind, by
      rw [constrainedFormalMindFin4_rootLanguage]
      change RuleUnmisunderstandable Fin4ZeroStarLanguage
        fin4ZeroStarAntiEntropy.compress
      exact constrained_rules_unmisunderstandable⟩

/-- A unified closure record containing both historical paths, a certificate
of the old path's trivial-language restriction, a concrete non-vacuity
certificate for the constrained path, and their universal-language bridge. -/
structure ProjectClosure (α : Type u) where
  oldPath : FinalCapstone α
  newPath : ConstrainedFinalPackage α
  vacuityCertificate :
    ∀ (hps : HierarchicalParallelSystem α)
      (_hNontrivial : ∃ st ∈ hps.system.sessions,
        st.session.protocolLanguage ≠ ∅ ∧
        st.session.protocolLanguage ≠ Set.univ),
      ¬ RSIAIsFormalMind hps
  nonvacuityCertificate :
    ∃ (cap : ConstrainedCapstone α),
      cap.rootLanguage ≠ ∅ ∧ cap.rootLanguage ≠ Set.univ ∧
      ConstrainedRSIAIsFormalMind cap.hps
  unification :
    ∀ (cap : ConstrainedCapstone α)
      (_hUniv : ∀ state ∈ cap.hps.system.sessions,
        state.session.protocolLanguage = Set.univ),
      ∀ state ∈ cap.hps.system.sessions,
        Environment.isNerodePreserving state.session

/-- Concrete unified closure over `Fin 4`. -/
noncomputable def projectClosureFin4 : ProjectClosure (Fin 4) where
  oldPath := finalCapstone
  newPath := constrainedFinalPackageFin4
  vacuityCertificate := oldPath_vacuous_for_nontrivial
  nonvacuityCertificate := by
    exact ⟨constrainedCapstoneFin4,
      constrainedCapstoneFin4_language_nontrivial.1,
      constrainedCapstoneFin4_language_nontrivial.2,
      instConstrainedHPSFin4_isFormalMind⟩
  unification := ConstrainedCapstone.local_promotes_to_global_at_univ

@[simp] theorem projectClosureFin4_oldPath :
    projectClosureFin4.oldPath = (finalCapstone : FinalCapstone (Fin 4)) := rfl

@[simp] theorem projectClosureFin4_newPath :
    projectClosureFin4.newPath = constrainedFinalPackageFin4 := rfl

/-- The unified project closure is inhabited over `Fin 4`. -/
theorem projectClosureFin4_nonempty :
    Nonempty (ProjectClosure (Fin 4)) :=
  ⟨projectClosureFin4⟩

/-- Both paths are packaged, the old global condition is impossible for any
hierarchy containing a nontrivial component language, and the constrained path
exhibits a concrete nontrivial language with unmisunderstandable compression. -/
theorem rsia_project_fully_closed :
    Nonempty (ProjectClosure (Fin 4)) ∧
    ∃ (cap : ConstrainedCapstone (Fin 4)),
      cap.rootLanguage ≠ ∅ ∧ cap.rootLanguage ≠ Set.univ ∧
      RuleUnmisunderstandable cap.rootLanguage cap.rootCompress ∧
      ∀ (hps : HierarchicalParallelSystem (Fin 4))
        (_hNontrivial : ∃ st ∈ hps.system.sessions,
          st.session.protocolLanguage ≠ ∅ ∧
          st.session.protocolLanguage ≠ Set.univ),
        ¬ RSIAIsFormalMind hps := by
  refine ⟨⟨projectClosureFin4⟩, ?_⟩
  obtain ⟨cap, hEmpty, hUniv, hRules⟩ :=
    constrained_rsia_project_nonvacuous_closed.2
  exact ⟨cap, hEmpty, hUniv, hRules, oldPath_vacuous_for_nontrivial⟩

end UAM_RSIA
