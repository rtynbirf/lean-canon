import RequestProject.Atlas.RSIAReview

set_option autoImplicit false

namespace RSIAFollowup

open RSIAReview

/-- The three residual kinds of the language “starts with 0”. -/
inductive ResidualKind
  | initial
  | accepting
  | rejecting
  deriving DecidableEq, Fintype

/-- Classification by the three residuals. -/
def residualKind : Word → ResidualKind
  | [] => .initial
  | false :: _ => .accepting
  | true :: _ => .rejecting

/-- The residual classification is exact, not merely a three-element lower bound. -/
theorem nerodeEq_startsWithZero_iff_residualKind_eq (u v : Word) :
    nerodeEq startsWithZero u v ↔ residualKind u = residualKind v := by
  constructor
  · intro h_equiv
    rcases u with - | ⟨a, us⟩ <;> rcases v with - | ⟨b, vs⟩
    · rfl
    · have h1 := h_equiv []
      simp [startsWithZero] at h1
      have h2 := h_equiv [false]
      simp [startsWithZero] at h2
      simp_all
    · have h1 := h_equiv []
      simp [startsWithZero] at h1
      have h2 := h_equiv [false]
      simp [startsWithZero] at h2
      simp_all
    · by_cases ha : a <;> by_cases hb : b <;> simp_all [residualKind]
      · have := h_equiv []
        simp [startsWithZero] at this
      · have := h_equiv []
        simp [startsWithZero] at this
  · intro h_kind
    rcases u with - | ⟨a, us⟩ <;> rcases v with - | ⟨b, vs⟩
    · intro z; rfl
    · cases b <;> simp [residualKind] at h_kind
    · cases a <;> simp [residualKind] at h_kind
    · by_cases ha : a <;> by_cases hb : b <;> simp_all [residualKind, startsWithZero, nerodeEq]

/-- Consequently there are exactly three residual kinds. -/
theorem residualKind_card : Fintype.card ResidualKind = 3 := by
  decide

/-- A canonical one-word representative of each residual. -/
def representative : ResidualKind → Word
  | .initial => []
  | .accepting => [false]
  | .rejecting => [true]

/-- A corrected set-valued compressor: map each word to the singleton containing
its residual's canonical representative. -/
def correctedCompressor (w : Word) : Finset Word :=
  {representative (residualKind w)}

/-- The compressor preserves the input's Nerode class exactly. -/
theorem correctedCompressor_preserves_class (w v : Word)
    (hv : v ∈ correctedCompressor w) :
    nerodeEq startsWithZero w v := by
  rw [nerodeEq_startsWithZero_iff_residualKind_eq]
  simp [correctedCompressor] at hv
  rw [hv]
  cases residualKind w <;> simp [representative, residualKind]

/-- Every residual kind is reached by the total output image, so the quotient
image score is all three classes rather than strictly below three. -/
theorem correctedCompressor_reaches_every_class (r : ResidualKind) :
    ∃ w v, v ∈ correctedCompressor w ∧ residualKind v = r := by
  use representative r, representative r
  cases r <;> simp [correctedCompressor, representative, residualKind]

/-- Its finite-set cardinality is constantly one. -/
theorem correctedCompressor_card (w : Word) :
    (correctedCompressor w).card = 1 := by
  simp [correctedCompressor]

/-- Interpreting size as output-set cardinality, it has uniform rate `1/2`
from input length two onward. -/
theorem correctedCompressor_uniform_card_rate (w : Word) (hw : 2 ≤ w.length) :
    2 * (correctedCompressor w).card ≤ w.length := by
  rw [correctedCompressor_card]
  exact hw

/-- Every output word has length at most one. -/
theorem correctedCompressor_output_length_le_one (w v : Word)
    (hv : v ∈ correctedCompressor w) :
    v.length ≤ 1 := by
  simp [correctedCompressor] at hv
  subst v
  cases residualKind w <;> simp [representative]

/-- Interpreting size as maximum/per-output word length, the same compressor
has uniform rate `1/2` from input length two onward. -/
theorem correctedCompressor_uniform_word_rate (w v : Word)
    (hw : 2 ≤ w.length) (hv : v ∈ correctedCompressor w) :
    2 * v.length ≤ w.length := by
  have hlen := correctedCompressor_output_length_le_one w v hv
  omega

/-- Uniform asymptotic shrinkage does not imply strict shrinkage at every
nonempty word: the one-letter accepting representative retains length one. -/
theorem correctedCompressor_not_pointwise_strict :
    ∃ w v, w ≠ [] ∧ v ∈ correctedCompressor w ∧ v.length = w.length := by
  refine ⟨[true], [true], ?_, ?_, rfl⟩
  · simp
  · simp [correctedCompressor, residualKind, representative]

/-- A compressor whose outputs all lie in the accepting residual, while their
word lengths exceed the input lengths. This witnesses the converse separation
between quotient-image score and a length rate. -/
def expandingOneClassCompressor (w : Word) : Finset Word :=
  {false :: List.replicate w.length false}

/-- The quotient image of `expandingOneClassCompressor` lies in one class. -/
theorem expandingOneClassCompressor_one_class (w v : Word)
    (hv : v ∈ expandingOneClassCompressor w) :
    residualKind v = .accepting := by
  simp [expandingOneClassCompressor] at hv
  subst v
  simp [residualKind]

/-- Its unique output is longer than its input. -/
theorem expandingOneClassCompressor_expands (w v : Word)
    (hv : v ∈ expandingOneClassCompressor w) :
    v.length = w.length + 1 := by
  simp [expandingOneClassCompressor] at hv
  subst v
  simp

/-- Pointwise upper distance on function spaces. -/
def PointwiseBound {α β : Type*} (d : β → β → Nat)
    (f g : α → β) (k : Nat) : Prop :=
  ∀ x, d (f x) (g x) ≤ k

/-- Precomposition is non-expansive for a pointwise/supremum-style bound.
No triangle or ultrametric axiom is needed. -/
theorem PointwiseBound.precomp {α β γ : Type*} (d : β → β → Nat)
    (f g : α → β) (h : γ → α) (k : Nat)
    (hfg : PointwiseBound d f g k) :
    PointwiseBound d (f ∘ h) (g ∘ h) k := by
  intro z
  exact hfg (h z)

end RSIAFollowup
