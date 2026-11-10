import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_Coordination

set_option autoImplicit false

/-!
# Locally constrained RSIA hierarchy

This file gives a parallel RSIA hierarchy whose environment invariant is local
to each session.  It also constructs a concrete instance over `Fin 4` for the
nontrivial protocol language `0*`.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- Unlike the original global invariant, this condition concerns only the
actual environment stored in the session. -/
def Environment.isLocallyNerodePreserving (s : Session α) : Prop :=
  ∀ action, UAM_RegularLanguages.nerodeRel s.protocolLanguage
    s.environment.current (s.environment.apply action)

/-- On the universal language the local invariant can be promoted to the
original global invariant. -/
theorem Environment.local_implies_global_univ (s : Session α)
    (hLanguage : s.protocolLanguage = Set.univ)
    (_hLocal : Environment.isLocallyNerodePreserving s) :
    Environment.isNerodePreserving s := by
  intro env action continuation
  rw [hLanguage]
  simp

/-- The language `0*` over the four-letter alphabet. -/
def Fin4ZeroStarLanguage : Set (UAM_Free.FreeMonoid (Fin 4)) :=
  {word | ∀ letter ∈ word, letter = 0}

/-- A protocol whose only rule prepends zero. -/
def fin4ZeroProtocol : Protocol (Fin 4) where
  rules := {rule | rule.2 = 0 :: rule.1}

/-- Compliance with the zero-prepending protocol is exactly membership in
`0*`. -/
theorem fin4ZeroProtocol_language :
    fin4ZeroProtocol.language = Fin4ZeroStarLanguage := by
  ext word
  simp [Fin4ZeroStarLanguage, fin4ZeroProtocol, Protocol.language]
  constructor
  · intro hCompliance
    induction hCompliance with
    | empty => simp
    | step _ h_rule h_ih =>
      intro letter h_letter
      simp [List.mem_cons] at h_letter
      obtain rfl | h_letter := h_letter
      · show letter = 0
        exact List.cons.inj h_rule |>.1
      · exact h_ih letter h_letter
  · intro hAllZero
    induction word with
    | nil => exact ProtocolCompliance.empty
    | cons a w ih =>
      have ha : a = 0 := by simpa using hAllZero a (by simp)
      have hw : ∀ letter ∈ w, letter = 0 :=
        fun l hl => hAllZero l (by simp [hl])
      have ih' := ih hw
      apply ProtocolCompliance.step ih'
      simp [ha]
      rfl

/-- The language `0*` is neither empty nor universal. -/
theorem Fin4ZeroStarLanguage_nontrivial :
    Fin4ZeroStarLanguage ≠ ∅ ∧ Fin4ZeroStarLanguage ≠ Set.univ := by
  constructor
  · intro h
    have : ([] : UAM_Free.FreeMonoid (Fin 4)) ∈ Fin4ZeroStarLanguage := by simp [Fin4ZeroStarLanguage]
    rw [h] at this
    exact this
  · intro h
    have : ([1] : UAM_Free.FreeMonoid (Fin 4)) ∈ Fin4ZeroStarLanguage := by simp [h]
    simp [Fin4ZeroStarLanguage] at this

/-- Membership of a concatenation in `0*` separates over its two factors. -/
theorem fin4ZeroStar_append (left right : UAM_Free.FreeMonoid (Fin 4)) :
    left ++ right ∈ Fin4ZeroStarLanguage ↔
      left ∈ Fin4ZeroStarLanguage ∧ right ∈ Fin4ZeroStarLanguage := by
  simp [Fin4ZeroStarLanguage, List.mem_append]
  constructor
  · intro h
    exact ⟨fun letter hl => h letter (Or.inl hl), fun letter hr => h letter (Or.inr hr)⟩
  · intro ⟨hl_mem, hr_mem⟩ letter h
    rcases h with hleft | hright
    · exact hl_mem letter hleft
    · exact hr_mem letter hright

/-- Compression used by the concrete anti-entropy cycle.  An all-zero word
loses its head.  A word containing a nonzero letter is replaced by `[1]`,
except that `[1]` is replaced by `[2]`; thus its Nerode class is unchanged and
every nonempty word changes. -/
noncomputable def fin4ZeroStarCompress (word : UAM_Free.FreeMonoid (Fin 4)) :
    UAM_Free.FreeMonoid (Fin 4) :=
  if _hEmpty : word = [] then []
  else if _hZero : word ∈ Fin4ZeroStarLanguage then word.tail
  else if word = [1] then [2] else [1]

/-- The concrete compression is length-nonincreasing and changes every
nonempty input. -/
theorem fin4ZeroStarCompress_isCompression
    (word : UAM_Free.FreeMonoid (Fin 4)) (hNonempty : word ≠ []) :
    IsCompression word (fin4ZeroStarCompress word) := by
  cases word with
  | nil => exact (hNonempty rfl).elim
  | cons a rest =>
    simp only [fin4ZeroStarCompress]
    simp only [List.cons_ne_nil, ↓reduceDIte]
    split_ifs with hZero hOne
    · constructor
      · simp
      · intro hEq
        have hLength := congrArg List.length hEq
        simp at hLength
    · simp only [hOne]
      constructor <;> decide
    · constructor
      · simp
      · intro hEq
        exact hOne hEq.symm

/-- Compression preserves whether a word belongs to `0*`. -/
theorem fin4ZeroStarCompress_mem (word : UAM_Free.FreeMonoid (Fin 4)) :
    (fin4ZeroStarCompress word ∈ Fin4ZeroStarLanguage) ↔
      word ∈ Fin4ZeroStarLanguage := by
  unfold fin4ZeroStarCompress
  split_ifs with hEmpty hZero hOne
  · rw [hEmpty]
  · refine ⟨fun _ => hZero, ?_⟩
    unfold Fin4ZeroStarLanguage at hZero ⊢
    intro h a ha
    exact hZero a (List.mem_of_mem_tail ha)
  · rw [hOne]
    simp [Fin4ZeroStarLanguage]
  · simp only [Fin4ZeroStarLanguage] at hZero ⊢
    tauto

/-- A genuine anti-entropy cycle for the nontrivial `0*` language. -/
noncomputable def fin4ZeroStarAntiEntropy : AntiEntropyCycle (Fin 4) where
  period := 1
  compress := fin4ZeroStarCompress
  compresses_nonempty := fin4ZeroStarCompress_isCompression
  compress_empty := by simp [fin4ZeroStarCompress]

/-- The concrete cycle preserves both Nerode classes of `0*`. -/
theorem fin4ZeroStarAntiEntropy_nerode :
    NerodePreserving Fin4ZeroStarLanguage fin4ZeroStarAntiEntropy.compress := by
  intro w
  unfold fin4ZeroStarAntiEntropy AntiEntropyCycle.compress
  unfold fin4ZeroStarCompress
  -- We need to show nerodeRel Fin4ZeroStarLanguage w (compress w)
  -- cases on w
  cases w with
  | nil => exact UAM_RegularLanguages.nerodeRel_refl _ _
  | cons a rest =>
    -- Manual case split
    by_cases hEmpty : a :: rest = []
    · exact absurd hEmpty (List.cons_ne_nil a rest)
    · simp only [hEmpty, ↓reduceDIte]
      by_cases hZero : a :: rest ∈ Fin4ZeroStarLanguage
      · -- a :: rest ∈ Fin4ZeroStarLanguage, compress to tail = rest
        simp only [hZero, ↓reduceDIte]
        -- Goal: nerodeRel Fin4ZeroStarLanguage (a :: rest) (a :: rest).tail
        -- Since (a :: rest) ∈ Fin4ZeroStarLanguage, a = 0
        unfold Fin4ZeroStarLanguage at hZero
        -- hZero : ∀ letter ∈ a :: rest, letter = 0
        have ha : a = 0 := hZero a (by simp)
        -- (a :: rest).tail = rest
        have hTail : (a :: rest).tail = rest := rfl
        rw [hTail]
        -- Need: ∀ v, ((a :: rest) ++ v ∈ Fin4ZeroStarLanguage) = (rest ++ v ∈ Fin4ZeroStarLanguage)
        intro v
        simp only [ha, List.cons_append]
        -- Need: (0 :: (rest ++ v) ∈ Fin4ZeroStarLanguage) = (rest ++ v ∈ Fin4ZeroStarLanguage)
        unfold Fin4ZeroStarLanguage
        simp
      · simp only [hZero, ↓reduceDIte]
        by_cases hOne : a :: rest = [1]
        · -- a :: rest = [1], ∉ Fin4ZeroStarLanguage, compress to [2]
          simp only [hOne, ite_true]
          -- Need: nerodeRel Fin4ZeroStarLanguage [1] [2]
          -- i.e., ∀ v, ([1] ++ v ∈ Fin4ZeroStarLanguage) = ([2] ++ v ∈ Fin4ZeroStarLanguage)
          -- Both [1] ++ v and [2] ++ v contain non-zero elements, so both are false
          intro v
          simp only [List.singleton_append]
          unfold Fin4ZeroStarLanguage
          simp
        · -- a :: rest ∉ Fin4ZeroStarLanguage, ≠ [1], compress to [1]
          simp only [hOne, ite_false]
          -- Need: nerodeRel Fin4ZeroStarLanguage (a :: rest) [1]
          -- Since a :: rest ∉ Fin4ZeroStarLanguage and [1] ∉ Fin4ZeroStarLanguage
          -- Both sides are false for any v
          intro v
          -- [1] ++ v = 1 :: v, which contains 1, so not in Fin4ZeroStarLanguage
          have hRight : [1] ++ v ∉ Fin4ZeroStarLanguage := by
            simp only [List.singleton_append]
            unfold Fin4ZeroStarLanguage
            simp
          -- (a :: rest) ++ v contains a non-zero element from a :: rest
          have hLeft : (a :: rest) ++ v ∉ Fin4ZeroStarLanguage := by
            intro h
            apply hZero
            unfold Fin4ZeroStarLanguage at h ⊢
            intro letter hletter
            have := h letter (List.mem_append_left _ hletter)
            exact this
          simp only [hLeft, hRight]

/-- Configuration carrying the local hierarchy's anti-entropy operation. -/
structure ConstrainedRSIAConfig (α : Type u)
    (language : Set (UAM_Free.FreeMonoid α)) where
  steps : List (AgentId × UAM_Free.FreeMonoid α)
  antiEntropy : AntiEntropyCycle α
  antiEntropy_nerode : NerodePreserving language antiEntropy.compress

/-- An RSIA state using the locally quantified environment invariant. -/
structure ConstrainedRSIAState (α : Type u) where
  session : Session α
  config : ConstrainedRSIAConfig α session.protocolLanguage
  localNerode : Environment.isLocallyNerodePreserving session
  rounds : List (RSIARound α)
  rounds_language : ∀ round ∈ rounds,
    round.input.protocolLanguage = session.protocolLanguage ∧
      round.output.protocolLanguage = session.protocolLanguage
  forks : List (ForkResult α)

/-- A finite family of locally constrained states. -/
structure ConstrainedParallelSystem (α : Type u) where
  sessions : List (ConstrainedRSIAState α)
  sessions_localNerode : ∀ state ∈ sessions,
    Environment.isLocallyNerodePreserving state.session

/-- A constrained parallel system together with root-to-component protocol
language evolution chains. -/
structure ConstrainedHierarchicalParallelSystem (α : Type u) where
  system : ConstrainedParallelSystem α
  rootLabel : SessionLabel
  rootLabel_in_range : rootLabel < system.sessions.length
  chains : ∀ (j : Nat) (hj : j < system.sessions.length),
    EvolutionChain α
      ((system.sessions.get ⟨rootLabel, rootLabel_in_range⟩).session.protocolLanguage)
      ((system.sessions.get ⟨j, hj⟩).session.protocolLanguage)

/-- A session whose actual environment remains in the all-zero Nerode class. -/
def fin4ZeroStarSession : Session (Fin 4) where
  protocol := fin4ZeroProtocol
  environment := { current := [0], apply := fun _ => [0] }
  agents := []
  phase := .construction

/-- The concrete session satisfies the local invariant. -/
theorem fin4ZeroStarSession_localNerode :
    Environment.isLocallyNerodePreserving fin4ZeroStarSession := by
  intro action
  unfold fin4ZeroStarSession
  simp [UAM_RegularLanguages.nerodeRel]

/-- The concrete locally constrained state. -/
noncomputable def fin4ZeroStarConstrainedState : ConstrainedRSIAState (Fin 4) where
  session := fin4ZeroStarSession
  config := {
    steps := []
    antiEntropy := fin4ZeroStarAntiEntropy
    antiEntropy_nerode := by
      rw [fin4ZeroStarSession, Session.protocolLanguage,
        fin4ZeroProtocol_language]
      exact fin4ZeroStarAntiEntropy_nerode }
  localNerode := fin4ZeroStarSession_localNerode
  rounds := []
  rounds_language := by simp
  forks := []

/-- The singleton constrained parallel system. -/
noncomputable def fin4ZeroStarConstrainedParallel : ConstrainedParallelSystem (Fin 4) where
  sessions := [fin4ZeroStarConstrainedState]
  sessions_localNerode := by
    intro state hState
    simp only [List.mem_singleton] at hState
    subst state
    exact fin4ZeroStarSession_localNerode

/-- A concrete constrained hierarchy over `Fin 4` with protocol language `0*`. -/
noncomputable def instConstrainedHPSFin4 : ConstrainedHierarchicalParallelSystem (Fin 4) where
  system := fin4ZeroStarConstrainedParallel
  rootLabel := 0
  rootLabel_in_range := by simp [fin4ZeroStarConstrainedParallel]
  chains := by
    intro j hj
    have hjZero : j = 0 := by
      simpa [fin4ZeroStarConstrainedParallel] using hj
    subst j
    exact EvolutionChain.nil _

/-- The constrained hierarchy is constructively inhabited over `Fin 4`. -/
theorem constrainedHPSFin4_nonempty :
    Nonempty (ConstrainedHierarchicalParallelSystem (Fin 4)) :=
  ⟨instConstrainedHPSFin4⟩

end UAM_RSIA
