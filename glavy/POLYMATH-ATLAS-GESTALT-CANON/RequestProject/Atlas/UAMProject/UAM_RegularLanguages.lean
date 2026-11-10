import Mathlib.Tactic
import RequestProject.Atlas.UAMProject.UAM_Free
import RequestProject.Atlas.UAMProject.UAM_Congruence
import RequestProject.Atlas.UAMProject.UAM_Morphism

namespace UAMP_RegularLanguages
universe u

open UAMP_Free hiding FreeMonoid
open UAMP_Congruence UAMP_Morphism

/-- Top-level DFA structure (A as first argument) -/
structure DFA (α Q : Type u) [DecidableEq Q] where
  δ : Q → α → Q
  q₀ : Q
  F : Set Q

variable {α Q : Type u} [DecidableEq Q] (A : DFA α Q)

/-- Run DFA from state q on word w -/
def evalFrom (A : DFA α Q) (q : Q) : UAMP_Free.FreeMonoid α → Q
  | [] => q
  | a :: w => evalFrom A (A.δ q a) w

/-- Run DFA from initial state -/
def eval (w : UAMP_Free.FreeMonoid α) : Q := evalFrom A A.q₀ w

/-- Does DFA accept word w? -/
def accepts (w : UAMP_Free.FreeMonoid α) : Prop := eval A w ∈ A.F

/-- Language of DFA -/
def language : Set (UAMP_Free.FreeMonoid α) := {w | accepts A w}

/-- Right-invariant relation w.r.t. language L -/
def IsRightInvariant (L : Set (UAMP_Free.FreeMonoid α)) (r : UAMP_Free.FreeMonoid α → UAMP_Free.FreeMonoid α → Prop) : Prop :=
  ∀ u v, r u v → ∀ w, (u ++ w ∈ L ↔ v ++ w ∈ L)

/-- L is stabilized by relation r -/
def StabilizedBy (L : Set (UAMP_Free.FreeMonoid α)) (r : UAMP_Free.FreeMonoid α → UAMP_Free.FreeMonoid α → Prop) : Prop :=
  ∀ u v, r u v → (u ∈ L ↔ v ∈ L)

/-- Nerode equivalence for language L -/
def nerodeRel (L : Set (UAMP_Free.FreeMonoid α)) (u v : UAMP_Free.FreeMonoid α) : Prop :=
  ∀ w, (u ++ w ∈ L ↔ v ++ w ∈ L)

/-- Syntactic congruence for L: nerode is two-sided -/
def syntacticRel (L : Set (UAMP_Free.FreeMonoid α)) (u v : UAMP_Free.FreeMonoid α) : Prop :=
  ∀ a b, (a ++ u ++ b ∈ L ↔ a ++ v ++ b ∈ L)

/- Архивная версия объявляла отношение Нероуда конгруэнцией
(`nerodeCongruence`), однако отношение Нероуда лишь право-инвариантно и в общем
случае не согласовано с умножением слева: из `a ~ b`, `c ~ d` не следует
`a·c ~ b·d`. Ниже доказана верная право-инвариантность, а синтаксический моноид
строится по двустороннему (синтаксическому) отношению. -/

/-- Отношение Нероуда право-инвариантно. -/
theorem nerodeRel_isRightInvariant (L : Set (UAMP_Free.FreeMonoid α)) :
    IsRightInvariant L (nerodeRel L) := fun _ _ h => h

/-- Отношение Нероуда сохраняется при дописывании слова справа. -/
theorem nerodeRel_append (L : Set (UAMP_Free.FreeMonoid α))
    {u v : UAMP_Free.FreeMonoid α} (h : nerodeRel L u v) (x : UAMP_Free.FreeMonoid α) :
    nerodeRel L (u ++ x) (v ++ x) := by
  intro w
  have h1 := h (x ++ w)
  simpa [List.append_assoc] using h1

/-- Синтаксическое отношение — конгруэнция. -/
def syntacticCongruence (L : Set (UAMP_Free.FreeMonoid α)) :
    IsCongruence (UAMP_Free.FreeMonoid α) where
  r := syntacticRel L
  refl := fun _ _ _ => Iff.rfl
  symm := fun _ _ h a b => (h a b).symm
  trans := fun _ _ _ hab hbc a b => (hab a b).trans (hbc a b)
  mul_compat := fun a b c d hab hcd x y => by
    show x ++ (a ++ c) ++ y ∈ L ↔ x ++ (b ++ d) ++ y ∈ L
    have e1 : x ++ (a ++ c) ++ y = x ++ a ++ (c ++ y) := by simp [List.append_assoc]
    have e2 : x ++ (b ++ c) ++ y = x ++ b ++ (c ++ y) := by simp [List.append_assoc]
    have e3 : x ++ (b ++ c) ++ y = (x ++ b) ++ c ++ y := by simp [List.append_assoc]
    have e4 : x ++ (b ++ d) ++ y = (x ++ b) ++ d ++ y := by simp [List.append_assoc]
    calc x ++ (a ++ c) ++ y ∈ L ↔ x ++ a ++ (c ++ y) ∈ L := by rw [e1]
      _ ↔ x ++ b ++ (c ++ y) ∈ L := hab x (c ++ y)
      _ ↔ x ++ (b ++ c) ++ y ∈ L := by rw [e2]
      _ ↔ (x ++ b) ++ c ++ y ∈ L := by rw [e3]
      _ ↔ (x ++ b) ++ d ++ y ∈ L := hcd (x ++ b) y
      _ ↔ x ++ (b ++ d) ++ y ∈ L := by rw [e4]
  one_compat := fun _ _ => Iff.rfl

/-- Syntactic monoid of L -/
abbrev SyntacticMonoid (L : Set (UAMP_Free.FreeMonoid α)) : Type u :=
  QuotientMonoid (syntacticCongruence L)

/-- Acceptance in syntactic monoid -/
def syntacticAccepting (L : Set (UAMP_Free.FreeMonoid α)) : Set (SyntacticMonoid L) :=
  (fun w => mk (syntacticCongruence L) w) '' L

/-- L устойчиво относительно синтаксического отношения. -/
theorem syntactic_stabilized (L : Set (UAMP_Free.FreeMonoid α)) :
    StabilizedBy L (syntacticCongruence L).r := by
  intro u v h
  have := h [] []
  simpa using this

theorem mem_syntacticAccepting (L : Set (UAMP_Free.FreeMonoid α))
    (w : UAMP_Free.FreeMonoid α) :
    mk (syntacticCongruence L) w ∈ syntacticAccepting L ↔ w ∈ L := by
  constructor
  · rintro ⟨a, ha, h⟩
    exact (syntactic_stabilized L a w (Quotient.exact h)).mp ha
  · intro h
    exact ⟨w, h, rfl⟩

/-- Syntactic morphism -/
def syntacticMorphism (L : Set (UAMP_Free.FreeMonoid α)) :
    MonoidMorphism (UAMP_Free.FreeMonoid α) (SyntacticMonoid L) where
  toFun := mk (syntacticCongruence L)
  map_mul := fun _ _ => mk_mul (syntacticCongruence L) _ _
  map_one := mk_one (syntacticCongruence L)

/-- Syntactic DFA: states = syntactic monoid elements -/
def syntacticDFA (L : Set (UAMP_Free.FreeMonoid α)) [DecidableEq (SyntacticMonoid L)] :
    DFA α (SyntacticMonoid L) where
  δ := fun q a => q * mk (syntacticCongruence L) (of a)
  q₀ := 1
  F := syntacticAccepting L

/-- Прогон синтаксического автомата из состояния `q` даёт `q * [w]`. -/
theorem syntacticDFA_evalFrom (L : Set (UAMP_Free.FreeMonoid α))
    [DecidableEq (SyntacticMonoid L)] (q : SyntacticMonoid L) (w : UAMP_Free.FreeMonoid α) :
    evalFrom (syntacticDFA L) q w = q * mk (syntacticCongruence L) w := by
  induction w generalizing q with
  | nil =>
    have h0 : mk (syntacticCongruence L) ([] : UAMP_Free.FreeMonoid α) = 1 := mk_one _
    show q = q * mk (syntacticCongruence L) []
    rw [h0, mul_one]
  | cons a w ih =>
    show evalFrom (syntacticDFA L) (q * mk (syntacticCongruence L) (of a)) w
        = q * mk (syntacticCongruence L) (of a * w)
    rw [ih, mul_assoc, mk_mul]

theorem syntacticDFA_language (L : Set (UAMP_Free.FreeMonoid α))
    [DecidableEq (SyntacticMonoid L)] : language (syntacticDFA L) = L := by
  ext w
  show evalFrom (syntacticDFA L) (syntacticDFA L).q₀ w ∈ (syntacticDFA L).F ↔ w ∈ L
  rw [syntacticDFA_evalFrom]
  show (1 : SyntacticMonoid L) * mk (syntacticCongruence L) w ∈ syntacticAccepting L ↔ w ∈ L
  rw [one_mul]
  exact mem_syntacticAccepting L w

/-- Myhill-Nerode (⇐): if the syntactic monoid is finite, L is DFA-recognizable.
(В архиве доказательство отсутствовало.) -/
theorem myhillNerode_finite_syntactic (L : Set (UAMP_Free.FreeMonoid α))
    [DecidableEq (SyntacticMonoid L)] [Fintype (SyntacticMonoid L)] :
    ∃ (Q : Type u) (_ : DecidableEq Q) (_ : Fintype Q) (A : DFA α Q), language A = L :=
  ⟨SyntacticMonoid L, inferInstance, inferInstance, syntacticDFA L, syntacticDFA_language L⟩

/-- Complement DFA -/
def DFA.complement (A : DFA α Q) : DFA α Q where
  δ := A.δ
  q₀ := A.q₀
  F := {q | q ∉ A.F}

/-- Union DFA (cross product) -/
def DFA.union (A : DFA α Q) {Q₂ : Type u} [DecidableEq Q₂] (B : DFA α Q₂) :
    DFA α (Q × Q₂) where
  δ := fun (q, r) a => (A.δ q a, B.δ r a)
  q₀ := (A.q₀, B.q₀)
  F := {p | p.1 ∈ A.F ∨ p.2 ∈ B.F}

/-- Language concatenation -/
def languageConcat (L₁ L₂ : Set (UAMP_Free.FreeMonoid α)) : Set (UAMP_Free.FreeMonoid α) :=
  {w | ∃ u v, u ++ v = w ∧ u ∈ L₁ ∧ v ∈ L₂}

/-- Kleene star -/
def kleeneStar (L : Set (UAMP_Free.FreeMonoid α)) : Set (UAMP_Free.FreeMonoid α) :=
  {w | ∃ S : List (UAMP_Free.FreeMonoid α), S.foldr (· ++ ·) [] = w ∧ ∀ s ∈ S, s ∈ L}

end UAMP_RegularLanguages
