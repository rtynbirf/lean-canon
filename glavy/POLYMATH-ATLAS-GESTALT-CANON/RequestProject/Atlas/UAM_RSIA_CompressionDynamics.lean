import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_ConstrainedProjectClosure

set_option autoImplicit false

/-!
# Compression dynamics

Strict decrease of word length is stronger than the concrete Run 37 compression
condition.  This module makes the distinction explicit and proves that strict
anti-entropy and pointwise Nerode preservation are incompatible with a language
having more than one Nerode class.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-- A strictly anti-entropic map shortens every nonempty word. -/
def IsStrictlyAntiEntropic (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) : Prop :=
  ∀ w, w ≠ [] → (f w).length < w.length

/-- Pointwise Nerode preservation together with strict length decrease. -/
def IsStrictAntiEntropicNerodePreserving
    (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) : Prop :=
  NerodePreserving L f ∧ IsStrictlyAntiEntropic f

/-- A language has at least two Nerode classes when some word is distinguishable
from the empty word. -/
def HasMultipleNerodeClasses (L : Set (UAM_Free.FreeMonoid α)) : Prop :=
  ∃ w, ¬ UAM_RegularLanguages.nerodeRel L w []

/-- A compression orbit either reaches the empty word, stabilizes at a nonempty
word, or contains a genuine periodic return. -/
inductive CompressionRegime
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (w : UAM_Free.FreeMonoid α) : Prop
  | reachesEmpty (n : Nat) (h : (f^[n]) w = [])
  | stabilizesNonempty (n : Nat)
      (hne : (f^[n]) w ≠ [])
      (hfix : f ((f^[n]) w) = (f^[n]) w)
  | periodic (start period : Nat) (hperiod : 0 < period)
      (hreturn : (f^[start + period]) w = (f^[start]) w)

/-- Strictly decreasing length forces every orbit to reach the empty word. -/
theorem strictlyAntiEntropic_reaches_empty
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hf : IsStrictlyAntiEntropic f) (w : UAM_Free.FreeMonoid α) :
    ∃ n ≤ w.length, (f^[n]) w = [] := by
  suffices h : ∀ len, ∀ w : UAM_Free.FreeMonoid α, w.length = len →
      ∃ n ≤ len, (f^[n]) w = [] by
    exact h w.length w rfl
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intro w hw
    by_cases hempty : w = []
    · exact ⟨0, Nat.zero_le _, hempty⟩
    · have hpos : 0 < w.length := Nat.pos_of_ne_zero fun h => hempty (List.eq_nil_of_length_eq_zero h)
      have hshort : (f w).length < len := by
        have := hf w hempty
        simp only [hw] at this
        exact this
      by_cases hzero : f w = []
      · exact ⟨1, by linarith, hzero⟩
      · obtain ⟨m, hm, hm'⟩ := ih (f w).length hshort (f w) rfl
        exact ⟨m + 1, by linarith, by rw [Function.iterate_succ_apply, hm']⟩

/-- Nerode preservation propagates from a word to every point of its orbit. -/
theorem nerodePreserving_iterate
    (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hf : NerodePreserving L f) (w : UAM_Free.FreeMonoid α) (n : Nat) :
    UAM_RegularLanguages.nerodeRel L w ((f^[n]) w) := by
  induction n with
  | zero => exact UAM_RegularLanguages.nerodeRel_refl L w
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact UAM_RegularLanguages.nerodeRel_trans L w (f^[n] w) (f (f^[n] w)) ih (hf (f^[n] w))

/-- The refined strict fifth-barrier assumptions are inconsistent for a
language with at least two Nerode classes. -/
theorem strict_fifth_barrier
    (L : Set (UAM_Free.FreeMonoid α))
    (hclasses : HasMultipleNerodeClasses L) :
    ¬ ∃ f, IsStrictAntiEntropicNerodePreserving L f := by
  intro ⟨f, ⟨hnerode, hstrict⟩⟩
  obtain ⟨w, hnw⟩ := hclasses
  obtain ⟨n, _, hn⟩ := strictlyAntiEntropic_reaches_empty f hstrict w
  have h := nerodePreserving_iterate L f hnerode w n
  rw [hn] at h
  exact hnw h

/-- Equivalently, a strictly anti-entropic Nerode-preserving map collapses all
words into the empty word's Nerode class. -/
theorem strict_compression_forces_single_nerode_class
    (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hf : IsStrictAntiEntropicNerodePreserving L f) :
    ∀ w, UAM_RegularLanguages.nerodeRel L w [] := by
  intro w
  obtain ⟨n, _, hn⟩ := strictlyAntiEntropic_reaches_empty f hf.2 w
  rw [← hn]
  exact nerodePreserving_iterate L f hf.1 w n

/-- The concrete compression sends `[1]` to `[2]`. -/
@[simp] theorem fin4ZeroStarCompress_one :
    fin4ZeroStarCompress ([1] : UAM_Free.FreeMonoid (Fin 4)) = [2] := by
  simp [fin4ZeroStarCompress, Fin4ZeroStarLanguage]

/-- The concrete compression sends `[2]` to `[1]`. -/
@[simp] theorem fin4ZeroStarCompress_two :
    fin4ZeroStarCompress ([2] : UAM_Free.FreeMonoid (Fin 4)) = [1] := by
  simp [fin4ZeroStarCompress, Fin4ZeroStarLanguage]

/-- The nonzero representatives form a genuine period-two orbit, the concrete
autopoietic boundary of the witness. -/
theorem fin4ZeroStarCompress_nonzero_periodic :
    CompressionRegime fin4ZeroStarCompress
      ([1] : UAM_Free.FreeMonoid (Fin 4)) := by
  exact CompressionRegime.periodic 0 2 (by norm_num) (by simp [fin4ZeroStarCompress_one, fin4ZeroStarCompress_two])

/-- The concrete period-two witness is not strictly anti-entropic. -/
theorem fin4ZeroStarCompress_not_strictlyAntiEntropic :
    ¬ IsStrictlyAntiEntropic fin4ZeroStarCompress := by
  intro h
  have := h [1] (List.ne_nil_of_length_pos (by norm_num))
  simp [fin4ZeroStarCompress_one] at this

/-- The empty word is already in the empty stabilization regime. -/
theorem fin4ZeroStarCompress_empty_regime :
    CompressionRegime fin4ZeroStarCompress
      ([] : UAM_Free.FreeMonoid (Fin 4)) := by
  exact CompressionRegime.reachesEmpty 0 rfl

/-- Every nonempty word of `0*` reaches the empty word under the concrete
compression. -/
theorem fin4ZeroStarCompress_zeroStar_reaches_empty
    (w : UAM_Free.FreeMonoid (Fin 4))
    (hw : w ∈ Fin4ZeroStarLanguage) :
    (fin4ZeroStarCompress^[w.length]) w = [] := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha : a = 0 := by simpa [Fin4ZeroStarLanguage] using hw a (by simp)
    have hw' : w ∈ Fin4ZeroStarLanguage := by
      simp [Fin4ZeroStarLanguage] at hw ⊢
      exact hw.2
    have hw0 : (0 :: w : List (Fin 4)) ∈ Fin4ZeroStarLanguage := by
      intro x hx
      apply hw
      simp [ha] at hx ⊢
      exact hx
    have hcompress : fin4ZeroStarCompress (a :: w) = w := by
      simp only [fin4ZeroStarCompress, ha]
      rw [dif_neg (by simp), dif_pos hw0]; rfl
    have hlen : (a :: w).length = w.length + 1 := by simp
    rw [hlen, Function.iterate_succ]
    simp [hcompress, ih hw']

end UAM_RSIA
