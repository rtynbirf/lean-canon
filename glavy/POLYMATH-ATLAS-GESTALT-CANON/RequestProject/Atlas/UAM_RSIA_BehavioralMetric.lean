import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_CompressionDynamics

set_option autoImplicit false

/-!
# Behavioral pseudometric

The behavioral distance is the prefix ultrametric induced by the least length
of a suffix that distinguishes two residual languages.  Nerode-equivalent words
are assigned distance zero.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- A suffix of length `n` distinguishes the residual languages at `w₁` and
`w₂`. -/
def DistinguishedAt
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ : UAM_Free.FreeMonoid α) (n : Nat) : Prop :=
  ∃ v : UAM_Free.FreeMonoid α, v.length = n ∧
    (w₁ ++ v ∈ L) ≠ (w₂ ++ v ∈ L)

/-- The least length of a distinguishing suffix, when one exists. -/
noncomputable def distinguishingSuffixLength
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ : UAM_Free.FreeMonoid α) : Option Nat :=
  if h : ∃ n, DistinguishedAt L w₁ w₂ n then some (Nat.find h) else none

/-- Behavioral distance: zero for Nerode-equivalent words and `2⁻ᵏ` when the
least distinguishing suffix has length `k`. -/
noncomputable def behavioralDistance
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ : UAM_Free.FreeMonoid α) : ℝ :=
  match distinguishingSuffixLength L w₁ w₂ with
  | none => 0
  | some k => (2 : ℝ)⁻¹ ^ k

/-- Having a distinguishing suffix is exactly failure of Nerode equivalence. -/
theorem exists_distinguishedAt_iff_not_nerode
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ : UAM_Free.FreeMonoid α) :
    (∃ n, DistinguishedAt L w₁ w₂ n) ↔
      ¬ UAM_RegularLanguages.nerodeRel L w₁ w₂ := by
  constructor
  · intro ⟨n, v, hv_len, hv_dist⟩ hNerode
    exact hv_dist (hNerode v)
  · intro hNotNerode
    simp only [UAM_RegularLanguages.nerodeRel] at hNotNerode
    push_neg at hNotNerode
    obtain ⟨v, hv_dist⟩ := hNotNerode
    exact ⟨v.length, v, rfl, hv_dist⟩

/-- The least distinguishing length is symmetric. -/
theorem distinguishingSuffixLength_symm
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ : UAM_Free.FreeMonoid α) :
    distinguishingSuffixLength L w₁ w₂ =
      distinguishingSuffixLength L w₂ w₁ := by
  unfold distinguishingSuffixLength
  have key : (∃ n, DistinguishedAt L w₁ w₂ n) ↔ ∃ n, DistinguishedAt L w₂ w₁ n := by
    constructor <;> intro ⟨n, v, hn, hne⟩ <;> exact ⟨n, v, hn, hne.symm⟩
  have equiv : ∀ n, DistinguishedAt L w₁ w₂ n ↔ DistinguishedAt L w₂ w₁ n := fun n =>
    ⟨fun ⟨v, hn, hne⟩ => ⟨v, hn, hne.symm⟩, fun ⟨v, hn, hne⟩ => ⟨v, hn, hne.symm⟩⟩
  have h₁ : (∃ n, DistinguishedAt L w₁ w₂ n) ↔ (∃ n, DistinguishedAt L w₂ w₁ n) :=
    ⟨fun ⟨n, hn⟩ => ⟨n, (equiv n).mp hn⟩, fun ⟨n, hn⟩ => ⟨n, (equiv n).mpr hn⟩⟩
  split_ifs with h₁' h₂ <;> simp_all
  -- Goal: Nat.find h₁' = Nat.find h₂
  -- Use Nat.find_eq_iff or similar
  refine le_antisymm ?_ ?_
  · apply Nat.find_min' _
    exact (equiv (Nat.find h₂)).mpr (Nat.find_spec h₂)
  · apply Nat.find_min' _
    exact (equiv (Nat.find h₁')).mp (Nat.find_spec h₁')

/-- Behavioral distance is nonnegative. -/
theorem behavioralDistance_nonneg
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ : UAM_Free.FreeMonoid α) :
    0 ≤ behavioralDistance L w₁ w₂ := by
  unfold behavioralDistance
  split
  · simp
  · simp

/-- Behavioral distance vanishes exactly on a Nerode class. -/
theorem behavioralDistance_eq_zero_iff
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ : UAM_Free.FreeMonoid α) :
    behavioralDistance L w₁ w₂ = 0 ↔
      UAM_RegularLanguages.nerodeRel L w₁ w₂ := by
  unfold behavioralDistance
  rw [distinguishingSuffixLength]
  split_ifs with h
  · -- Case: ∃ n, DistinguishedAt L w₁ w₂ n (so distinguishingSuffixLength = some k)
    simp
    rw [exists_distinguishedAt_iff_not_nerode] at h
    exact h
  · -- Case: ¬∃ n, DistinguishedAt L w₁ w₂ n
    simp
    by_contra hc
    rw [exists_distinguishedAt_iff_not_nerode] at h
    exact h hc

/-- Behavioral distance is symmetric. -/
theorem behavioralDistance_symm
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ : UAM_Free.FreeMonoid α) :
    behavioralDistance L w₁ w₂ = behavioralDistance L w₂ w₁ := by
  simp [behavioralDistance, distinguishingSuffixLength_symm]

/-- The behavioral distance satisfies the strong triangle inequality. -/
theorem behavioralDistance_ultrametric
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ w₃ : UAM_Free.FreeMonoid α) :
    behavioralDistance L w₁ w₃ ≤
      max (behavioralDistance L w₁ w₂) (behavioralDistance L w₂ w₃) := by
  -- Key lemma: if v distinguishes w₁ from w₃, then v distinguishes
  -- either w₁ from w₂, or w₂ from w₃ (or both)
  have key : ∀ v : UAM_Free.FreeMonoid α,
    (w₁ ++ v ∈ L) ≠ (w₃ ++ v ∈ L) →
    (w₁ ++ v ∈ L) ≠ (w₂ ++ v ∈ L) ∨ (w₂ ++ v ∈ L) ≠ (w₃ ++ v ∈ L) := by
    intro v h
    by_contra hc
    push_neg at hc
    exact h (hc.1.trans hc.2)
  -- Case split on whether there's a distinguishing suffix for (w₁, w₃)
  cases hdist : distinguishingSuffixLength L w₁ w₃ with
  | none =>
    -- No distinguishing suffix means distance is 0
    simp [behavioralDistance, hdist]
    left
    split <;> simp
  | some k =>
    -- From hdist, we know DistinguishedAt L w₁ w₃ k holds
    have hd : DistinguishedAt L w₁ w₃ k := by
      unfold distinguishingSuffixLength at hdist
      split at hdist <;> try simp_all
      rename_i h
      rw [← hdist]
      exact Nat.find_spec h
    -- Extract the distinguishing suffix v
    obtain ⟨v, hv_len, hv_dist⟩ := hd
    -- By key lemma, v distinguishes either (w₁, w₂) or (w₂, w₃)
    have h := key v hv_dist
    -- behavioralDistance L w₁ w₃ = 2⁻¹ ^ k
    have eq_w1w3 : behavioralDistance L w₁ w₃ = (2 : ℝ)⁻¹ ^ k := by
      unfold behavioralDistance; simp [hdist]
    -- If DistinguishedAt L a b k, then behavioralDistance L a b ≥ 2⁻ᵏ
    have dist_bound : ∀ {a b : UAM_Free.FreeMonoid α}, DistinguishedAt L a b k →
        behavioralDistance L a b ≥ (2 : ℝ)⁻¹ ^ k := by
      intro a b hD
      unfold behavioralDistance
      have hex : ∃ n, DistinguishedAt L a b n := ⟨k, hD⟩
      simp [distinguishingSuffixLength, hex]
      -- Need to show (2^k)⁻¹ ≤ (2^(Nat.find hex))⁻¹, i.e., Nat.find hex ≤ k
      have hfind : Nat.find hex ≤ k := Nat.find_min' hex hD
      have hpow : (2 : ℝ) ^ Nat.find hex ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hfind
      exact inv_anti₀ (by norm_num) hpow
    -- Case split on which pair is distinguished
    rcases h with h1 | h2
    · -- v distinguishes (w₁, w₂), so distinguishingSuffixLength L w₁ w₂ ≤ k
      have hD1 : DistinguishedAt L w₁ w₂ k := ⟨v, hv_len, h1⟩
      rw [eq_w1w3]
      exact le_max_of_le_left (dist_bound hD1)
    · -- v distinguishes (w₂, w₃), so distinguishingSuffixLength L w₂ w₃ ≤ k
      have hD2 : DistinguishedAt L w₂ w₃ k := ⟨v, hv_len, h2⟩
      rw [eq_w1w3]
      exact le_max_of_le_right (dist_bound hD2)

/-- Consequently, behavioral distance satisfies the ordinary triangle
inequality. -/
theorem behavioralDistance_triangle
    (L : Set (UAM_Free.FreeMonoid α))
    (w₁ w₂ w₃ : UAM_Free.FreeMonoid α) :
    behavioralDistance L w₁ w₃ ≤
      behavioralDistance L w₁ w₂ + behavioralDistance L w₂ w₃ := by
  have h := behavioralDistance_ultrametric L w₁ w₂ w₃
  have h1 : behavioralDistance L w₁ w₂ ≥ 0 := behavioralDistance_nonneg L w₁ w₂
  have h2 : behavioralDistance L w₂ w₃ ≥ 0 := behavioralDistance_nonneg L w₂ w₃
  apply h.trans
  rcases le_total (behavioralDistance L w₁ w₂) (behavioralDistance L w₂ w₃) with hle | hle
  · rw [max_eq_right hle]
    exact le_add_of_nonneg_left h1
  · rw [max_eq_left hle]
    exact le_add_of_nonneg_right h2

/-- A pointwise Nerode-preserving map does not change behavioral distance: it
preserves each residual language, not merely membership at the empty suffix. -/
theorem behavioralDistance_nerodePreserving
    (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hf : NerodePreserving L f)
    (w₁ w₂ : UAM_Free.FreeMonoid α) :
    behavioralDistance L (f w₁) (f w₂) = behavioralDistance L w₁ w₂ := by
  unfold behavioralDistance
  -- Key: NerodePreserving means ∀ w, nerodeRel L w (f w), i.e., ∀ w v, (w ++ v ∈ L) = (f w ++ v ∈ L)
  have h_eq : ∀ v : UAM_Free.FreeMonoid α, (f w₁ ++ v ∈ L) = (w₁ ++ v ∈ L) := fun v => (hf w₁ v).symm
  have h_eq₂ : ∀ v : UAM_Free.FreeMonoid α, (f w₂ ++ v ∈ L) = (w₂ ++ v ∈ L) := fun v => (hf w₂ v).symm
  -- DistinguishedAt is preserved
  have dist_eq : ∀ n, DistinguishedAt L (f w₁) (f w₂) n ↔ DistinguishedAt L w₁ w₂ n := by
    intro n
    constructor <;> intro ⟨v, hv_len, hv_dist⟩
    · exact ⟨v, hv_len, by simp_all⟩
    · exact ⟨v, hv_len, by simp_all⟩
  unfold distinguishingSuffixLength
  -- The existential conditions are equivalent
  have hex_eq : (∃ n, DistinguishedAt L (f w₁) (f w₂) n) ↔ (∃ n, DistinguishedAt L w₁ w₂ n) := by
    constructor
    · intro ⟨n, hn⟩; exact ⟨n, (dist_eq n).mp hn⟩
    · intro ⟨n, hn⟩; exact ⟨n, (dist_eq n).mpr hn⟩
  by_cases h₁ : ∃ n, DistinguishedAt L (f w₁) (f w₂) n <;> by_cases h₂ : ∃ n, DistinguishedAt L w₁ w₂ n
  · simp [h₁, h₂]
    -- Need to show Nat.find h₁ = Nat.find h₂
    -- Since dist_eq says the predicates are equivalent, Nat.find gives the same value
    have pred_eq : (fun n => DistinguishedAt L (f w₁) (f w₂) n) = (fun n => DistinguishedAt L w₁ w₂ n) := by
      ext n; exact dist_eq n
    have find_eq : Nat.find h₁ = Nat.find h₂ := by simp_all
    simp [find_eq]
  · exfalso; exact h₂ (hex_eq.mp h₁)
  · exfalso; exact h₁ (hex_eq.mpr h₂)
  · simp [h₁, h₂] -- both false

/-- Two all-zero words have behavioral distance zero. -/
theorem fin4_behavioral_zero_words : behavioralDistance Fin4ZeroStarLanguage
    ([0, 0] : UAM_Free.FreeMonoid (Fin 4)) [0] = 0 := by
  rw [behavioralDistance_eq_zero_iff]
  intro v
  simp [Fin4ZeroStarLanguage]

/-- Two nonzero representatives have behavioral distance zero. -/
theorem fin4_behavioral_nonzero_words : behavioralDistance Fin4ZeroStarLanguage
    ([1] : UAM_Free.FreeMonoid (Fin 4)) [2] = 0 := by
  rw [behavioralDistance_eq_zero_iff]
  intro v
  simp only [List.singleton_append]
  unfold Fin4ZeroStarLanguage
  simp

/-- Zero and nonzero representatives are behaviorally separated. -/
theorem fin4_behavioral_classes_separated : 0 < behavioralDistance Fin4ZeroStarLanguage
    ([0] : UAM_Free.FreeMonoid (Fin 4)) [1] := by
  -- The empty suffix distinguishes [0] from [1]: [0] ∈ Fin4ZeroStarLanguage but [1] ∉ it
  have hD : DistinguishedAt Fin4ZeroStarLanguage [0] [1] 0 := by
    use []
    simp [Fin4ZeroStarLanguage]
  -- So behavioralDistance is 2⁻¹ ^ 0 = 1 > 0
  unfold behavioralDistance
  have hex : ∃ n, DistinguishedAt Fin4ZeroStarLanguage [0] [1] n := ⟨0, hD⟩
  simp [distinguishingSuffixLength, hex]

end UAM_RSIA
