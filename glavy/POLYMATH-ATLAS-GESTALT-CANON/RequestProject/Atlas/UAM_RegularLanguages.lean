import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_Congruence
import RequestProject.Atlas.UAM_Morphism
import RequestProject.Atlas.UAM_DFAEval

/-!
# UAM — Layer 11 (Application): Регулярные языки (Regular Languages)

Прикладной слой, связывающий алгебраическую теорию моноидов (ядро UAM) с
теорией регулярных языков.

Содержание:
1. **DFA** — детерминированный конечный автомат.
2. **Язык автомата** `DFA.language`.
3. **Nerode-отношение** (правая инвариантность) и **синтаксическая конгруэнция**
   (двусторонняя) на свободном моноиде.
4. **Синтаксический моноид** языка как фактор свободного моноида.
5. **Теорема Майхилла–Нероуда** (направление ⇐): если синтаксический моноид
   конечен, язык распознаётся некоторым DFA.

Модуль зависит от слоёв 8 (`UAM_Free`) и 6 (`UAM_Congruence`, `UAM_Morphism`).

**Математическое замечание (важно).** Классическое «right Nerode»-отношение
`w1 ~ w2 ⇔ ∀ v, (w1 v ∈ L ↔ w2 v ∈ L)` является лишь *правой* конгруэнцией
(правоинвариантно), но НЕ является двусторонней конгруэнцией моноида: оно, вообще
говоря, несовместимо с умножением слева. Поэтому синтаксический моноид строится по
*двусторонней* синтаксической конгруэнции
`w1 ≈ w2 ⇔ ∀ p v, (p w1 v ∈ L ↔ p w2 v ∈ L)`,
которая является полноценной конгруэнцией. Правое Nerode-отношение сохранено
отдельно (см. `nerodeRel`) вместе с его свойствами правой инвариантности.
-/

namespace UAM_RegularLanguages

universe u

/-! ### §1–2. Канонический DFA и его семантика

Автоматы и вычисление импортируются из `UAM_DFAEval`; этот модуль не вводит
параллельного типа DFA. -/

open UAM_DFAEval

/-! ### §3. Правая инвариантность и стабилизация -/

variable {α : Type u}

/-- Правая инвариантность: отношение `R` неразличимо по языку `L` справа —
    для любого контекста `v` слова `w1 ++ v` и `w2 ++ v` одновременно (не) в `L`. -/
def IsRightInvariant (L : Set (UAM_Free.FreeMonoid α))
    (R : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α → Prop) : Prop :=
  ∀ w1 w2 : UAM_Free.FreeMonoid α, R w1 w2 →
    ∀ v : UAM_Free.FreeMonoid α, (w1 ++ v ∈ L) = (w2 ++ v ∈ L)

/-- Язык `L` стабилизируется морфизмом `f` через множество `S`,
    если `w ∈ L ↔ f w ∈ S`. -/
def StabilizedBy (L : Set (UAM_Free.FreeMonoid α)) (N : Type u) [Monoid N]
    (f : UAM_Morphism.MonoidMorphism (UAM_Free.FreeMonoid α) N) (S : Set N) : Prop :=
  ∀ w, w ∈ L ↔ f.toFun w ∈ S

/-- Ядро любого морфизма из свободного моноида правоинвариантно относительно
    языка, стабилизированного этим морфизмом. -/
theorem kernel_right_invariant (L : Set (UAM_Free.FreeMonoid α))
    {N : Type u} [Monoid N]
    (f : UAM_Morphism.MonoidMorphism (UAM_Free.FreeMonoid α) N)
    (S : Set N) (hstab : StabilizedBy L N f S) :
    IsRightInvariant L f.kernel.r := by
  intro w1 w2 hkw v
  rw [UAM_Morphism.MonoidMorphism.kernel_eq_iff] at hkw
  have h1 : w1 ++ v ∈ L ↔ f.toFun (w1 ++ v) ∈ S := hstab (w1 ++ v)
  have h2 : w2 ++ v ∈ L ↔ f.toFun (w2 ++ v) ∈ S := hstab (w2 ++ v)
  have hmul1 : f.toFun (w1 ++ v) = f.toFun w1 * f.toFun v := f.map_mul w1 v
  have hmul2 : f.toFun (w2 ++ v) = f.toFun w2 * f.toFun v := f.map_mul w2 v
  rw [hmul1, hkw] at h1
  rw [hmul2] at h2
  exact propext (h1.trans h2.symm)

/-! ### §4. Nerode-отношение, синтаксическая конгруэнция и синтаксический моноид -/

/-- Правое Nerode-отношение для языка `L`: два слова эквивалентны, если
    неразличимы по правым контекстам. Это лишь ПРАВАЯ конгруэнция. -/
def nerodeRel (L : Set (UAM_Free.FreeMonoid α)) :
    UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α → Prop :=
  fun w1 w2 => ∀ v : UAM_Free.FreeMonoid α, (w1 ++ v ∈ L) = (w2 ++ v ∈ L)

/-- Nerode-отношение рефлексивно. -/
theorem nerodeRel_refl (L : Set (UAM_Free.FreeMonoid α)) (w : UAM_Free.FreeMonoid α) :
    nerodeRel L w w := fun _ => rfl

/-- Nerode-отношение симметрично. -/
theorem nerodeRel_symm (L : Set (UAM_Free.FreeMonoid α)) (w1 w2 : UAM_Free.FreeMonoid α)
    (h : nerodeRel L w1 w2) : nerodeRel L w2 w1 :=
  fun v => (h v).symm

/-- Nerode-отношение транзитивно. -/
theorem nerodeRel_trans (L : Set (UAM_Free.FreeMonoid α)) (w1 w2 w3 : UAM_Free.FreeMonoid α)
    (h1 : nerodeRel L w1 w2) (h2 : nerodeRel L w2 w3) :
    nerodeRel L w1 w3 := fun v => (h1 v).trans (h2 v)

/-- Nerode-отношение правоинвариантно по определению. -/
theorem nerodeRel_right_invariant (L : Set (UAM_Free.FreeMonoid α)) :
    IsRightInvariant L (nerodeRel L) := by
  intro w1 w2 h v
  exact h v

/-- Двусторонняя синтаксическая эквивалентность: слова неразличимы во всех
    (левых и правых) контекстах. Это полноценная конгруэнция моноида. -/
def syntacticRel (L : Set (UAM_Free.FreeMonoid α)) :
    UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α → Prop :=
  fun w1 w2 => ∀ p v : UAM_Free.FreeMonoid α, (p ++ w1 ++ v ∈ L) = (p ++ w2 ++ v ∈ L)

/-- Синтаксическая конгруэнция языка `L` (двусторонняя). -/
def nerodeCongruence (L : Set (UAM_Free.FreeMonoid α)) :
    UAM_Congruence.IsCongruence (UAM_Free.FreeMonoid α) where
  r := syntacticRel L
  refl := fun _ _ _ => rfl
  symm := fun _ _ h p v => (h p v).symm
  trans := fun _ _ _ h1 h2 p v => (h1 p v).trans (h2 p v)
  mul_compat := by
    intro a b c d h1 h2 p v
    show (p ++ (a ++ c) ++ v ∈ L) = (p ++ (b ++ d) ++ v ∈ L)
    have s1 := h1 p (c ++ v)
    have s2 := h2 (p ++ b) v
    simp only [List.append_assoc] at s1 s2 ⊢
    rw [s1, s2]
  one_compat := fun _ _ => rfl

/-- Синтаксический моноид языка `L`: фактор свободного моноида по синтаксической
    конгруэнции. -/
abbrev SyntacticMonoid (L : Set (UAM_Free.FreeMonoid α)) :=
  UAM_Congruence.QuotientMonoid (nerodeCongruence L)

/-- Синтаксическая конгруэнция является конгруэнцией (формально). -/
def nerodeCongruence_isCongruence (L : Set (UAM_Free.FreeMonoid α)) :
    UAM_Congruence.IsCongruence (UAM_Free.FreeMonoid α) :=
  nerodeCongruence L

/-- Принимающее множество синтаксического моноида: классы слов из `L`. -/
def syntacticAccepting (L : Set (UAM_Free.FreeMonoid α)) :
    Set (SyntacticMonoid L) :=
  { q | ∃ w, q = UAM_Congruence.QuotientMonoid.mk w ∧ w ∈ L }

/-- Критерий принадлежности языку: `w ∈ L` тогда и только тогда, когда класс `w`
    в синтаксическом моноиде лежит в `syntacticAccepting`. -/
theorem mem_syntacticAccepting (L : Set (UAM_Free.FreeMonoid α)) (w : UAM_Free.FreeMonoid α) :
    w ∈ L ↔ UAM_Congruence.QuotientMonoid.mk w ∈ syntacticAccepting L := by
  constructor
  · intro hw
    exact ⟨w, rfl, hw⟩
  · intro h
    obtain ⟨u, hu, huL⟩ := h
    have hr : (nerodeCongruence L).r w u :=
      UAM_Congruence.QuotientMonoid.mk_eq_iff.mp hu
    have heq := hr [] []
    simp only [List.nil_append, List.append_nil] at heq
    rw [heq]
    exact huL

/-! ### §5. DFA стабилизирует Nerode-отношение -/

namespace DFA

variable {Q : Type u} [DecidableEq Q]

/-- Если `eval w1 = eval w2`, то для любого `v` имеем `eval (w1 ++ v) = eval (w2 ++ v)`. -/
theorem eval_eq_of_eval_eq (A : DFA α Q) (w1 w2 : UAM_Free.FreeMonoid α)
    (h : A.eval w1 = A.eval w2) (v : UAM_Free.FreeMonoid α) :
    A.eval (w1 ++ v) = A.eval (w2 ++ v) := by
  rw [A.eval_concat w1 v, A.eval_concat w2 v, h]

/-- Если два слова приводят автомат в одно состояние, они Nerode-эквивалентны
    относительно языка этого автомата. -/
theorem dfa_nerode_of_eval_eq (A : DFA α Q) (w1 w2 : UAM_Free.FreeMonoid α)
    (h : A.eval w1 = A.eval w2) :
    nerodeRel A.language w1 w2 := by
  intro v
  show (w1 ++ v ∈ A.language) = (w2 ++ v ∈ A.language)
  have := eval_eq_of_eval_eq A w1 w2 h v
  show (A.accepts (w1 ++ v)) = (A.accepts (w2 ++ v))
  show (A.eval (w1 ++ v) ∈ A.F) = (A.eval (w2 ++ v) ∈ A.F)
  rw [this]

end DFA

/-! ### §6. Теорема Майхилла–Нероуда (направление ⇐) -/

/-- Проекция в синтаксический моноид — морфизм моноидов. -/
def syntacticMorphism (L : Set (UAM_Free.FreeMonoid α)) :
    UAM_Morphism.MonoidMorphism (UAM_Free.FreeMonoid α) (SyntacticMonoid L) where
  toFun := UAM_Congruence.QuotientMonoid.mk
  map_mul := fun a b => UAM_Congruence.QuotientMonoid.mk_mul a b
  map_one := UAM_Congruence.QuotientMonoid.mk_one

/-- Язык стабилизируется проекцией в синтаксический моноид. -/
theorem syntactic_stabilized (L : Set (UAM_Free.FreeMonoid α)) :
    StabilizedBy L (SyntacticMonoid L) (syntacticMorphism L) (syntacticAccepting L) :=
  fun w => mem_syntacticAccepting L w

/-- DFA, построенный из конечного стабилизирующего моноида `N`.
    Состояния — элементы `N`, переход умножает справа на образ буквы. -/
def stabilizedDFA {N : Type u} [Monoid N] [DecidableEq N]
    (f : UAM_Morphism.MonoidMorphism (UAM_Free.FreeMonoid α) N)
    (S : Set N) (L : Set (UAM_Free.FreeMonoid α))
    (_hstab : StabilizedBy L N f S) :
    DFA α N where
  δ := fun q a => q * f.toFun (UAM_Free.FreeMonoid.of a)
  q₀ := 1
  F := S

/-- Вычисление `stabilizedDFA` из состояния `q`: домножение `q` на образ слова. -/
theorem stabilizedDFA_evalFrom {N : Type u} [Monoid N] [DecidableEq N]
    (f : UAM_Morphism.MonoidMorphism (UAM_Free.FreeMonoid α) N)
    (S : Set N) (L : Set (UAM_Free.FreeMonoid α))
    (hstab : StabilizedBy L N f S) (q : N) (w : UAM_Free.FreeMonoid α) :
    (stabilizedDFA f S L hstab).evalFrom q w = q * f.toFun w := by
  induction w generalizing q with
  | nil =>
    show q = q * f.toFun ([] : UAM_Free.FreeMonoid α)
    have h1 : f.toFun ([] : UAM_Free.FreeMonoid α) = 1 := f.map_one
    rw [h1, mul_one]
  | cons a ws ih =>
    show (stabilizedDFA f S L hstab).evalFrom
        ((stabilizedDFA f S L hstab).δ q a) ws = q * f.toFun (a :: ws)
    rw [ih]
    show (q * f.toFun (UAM_Free.FreeMonoid.of a)) * f.toFun ws = q * f.toFun (a :: ws)
    have hmul : f.toFun (a :: ws)
        = f.toFun (UAM_Free.FreeMonoid.of a) * f.toFun ws :=
      f.map_mul (UAM_Free.FreeMonoid.of a) ws
    rw [hmul, mul_assoc]

/-- Язык стабилизированного DFA совпадает с исходным языком `L`. -/
theorem stabilizedDFA_language {N : Type u} [Monoid N] [DecidableEq N]
    (f : UAM_Morphism.MonoidMorphism (UAM_Free.FreeMonoid α) N)
    (S : Set N) (L : Set (UAM_Free.FreeMonoid α))
    (hstab : StabilizedBy L N f S) :
    (stabilizedDFA f S L hstab).language = L := by
  ext w
  show (stabilizedDFA f S L hstab).accepts w ↔ w ∈ L
  show (stabilizedDFA f S L hstab).eval w ∈ S ↔ w ∈ L
  show (stabilizedDFA f S L hstab).evalFrom (stabilizedDFA f S L hstab).q₀ w ∈ S ↔ w ∈ L
  have hq : (stabilizedDFA f S L hstab).q₀ = (1 : N) := rfl
  rw [hq, stabilizedDFA_evalFrom, one_mul]
  exact (hstab w).symm

/-- DFA из синтаксического моноида (при его конечности): состояния — классы. -/
def syntacticDFA (L : Set (UAM_Free.FreeMonoid α))
    [DecidableEq (SyntacticMonoid L)] :
    DFA α (SyntacticMonoid L) :=
  stabilizedDFA (syntacticMorphism L) (syntacticAccepting L) L (syntactic_stabilized L)

/-- **Теорема Майхилла–Нероуда (направление ⇐).**
    Если синтаксический моноид языка `L` конечен, то `L` распознаётся некоторым DFA
    (в качестве состояний берутся классы синтаксической конгруэнции). -/
theorem myhillNerode_finite_syntactic (L : Set (UAM_Free.FreeMonoid α))
    [Fintype (SyntacticMonoid L)] [DecidableEq (SyntacticMonoid L)] :
    ∃ (Q : Type u) (_ : Fintype Q) (_ : DecidableEq Q) (A : DFA α Q), A.language = L :=
  ⟨SyntacticMonoid L, inferInstance, inferInstance, syntacticDFA L,
   stabilizedDFA_language (syntacticMorphism L) (syntacticAccepting L) L
     (syntactic_stabilized L)⟩

/-! ### §7. Примеры -/

/-- Пример: DFA, допускающий слова, оканчивающиеся на символ `a₀`. -/
def example_ends_with (α : Type) [DecidableEq α] (a₀ : α) :
    DFA α Bool where
  δ := fun q a => if a = a₀ then true else q
  q₀ := false
  F := {true}

/-- Пустой язык распознаётся DFA с одним непринимающим состоянием. -/
def emptyLanguageDFA (α : Type) : DFA α Unit where
  δ := fun _ _ => ()
  q₀ := ()
  F := ∅

/-- Язык всех слов распознаётся DFA с одним принимающим состоянием. -/
def universalLanguageDFA (α : Type) : DFA α Unit where
  δ := fun _ _ => ()
  q₀ := ()
  F := Set.univ

/-! ### §8. Замыкающие свойства -/

namespace DFA

variable {Q : Type u} [DecidableEq Q]

/-- Дополнение DFA: инвертируем принимающие состояния. -/
def complement (A : DFA α Q) : DFA α Q where
  δ := A.δ
  q₀ := A.q₀
  F := A.Fᶜ

/-- Язык дополнения — дополнение языка. -/
theorem language_complement (A : DFA α Q) :
    (complement A).language = A.languageᶜ := by
  ext w
  show (complement A).accepts w ↔ ¬ A.accepts w
  show (complement A).eval w ∈ A.Fᶜ ↔ ¬ (A.eval w ∈ A.F)
  have hev : (complement A).eval w = A.eval w := by
    show (complement A).evalFrom (complement A).q₀ w = A.evalFrom A.q₀ w
    have : ∀ (q : Q) (v : UAM_Free.FreeMonoid α),
        (complement A).evalFrom q v = A.evalFrom q v := by
      intro q v
      induction v generalizing q with
      | nil => rfl
      | cons a ws ih => exact ih (A.δ q a)
    exact this A.q₀ w
  rw [hev]
  exact Set.mem_compl_iff A.F (A.eval w)

/-- Объединение двух DFA через прямое произведение состояний. -/
def union {Q₁ Q₂ : Type u} [DecidableEq Q₁] [DecidableEq Q₂]
    (A : DFA α Q₁) (B : DFA α Q₂) :
    DFA α (Q₁ × Q₂) where
  δ := fun q a => (A.δ q.1 a, B.δ q.2 a)
  q₀ := (A.q₀, B.q₀)
  F := {p | p.1 ∈ A.F ∨ p.2 ∈ B.F}

end DFA

/-- Конкатенация языков: `L₁ ◦ L₂ = {w1 ++ w2 | w1 ∈ L₁, w2 ∈ L₂}`. -/
def languageConcat (L₁ L₂ : Set (UAM_Free.FreeMonoid α)) :
    Set (UAM_Free.FreeMonoid α) :=
  {w | ∃ w1 w2, w = w1 ++ w2 ∧ w1 ∈ L₁ ∧ w2 ∈ L₂}

/-- Звёздочка Клини, построенная без алгебраических типов Mathlib. -/
inductive KleeneStar (L : Set (UAM_Free.FreeMonoid α)) :
    UAM_Free.FreeMonoid α → Prop where
  | empty : KleeneStar L []
  | word (w : UAM_Free.FreeMonoid α) (h : w ∈ L) : KleeneStar L w
  | concat (w₁ w₂ : UAM_Free.FreeMonoid α)
      (h₁ : KleeneStar L w₁) (h₂ : KleeneStar L w₂) :
      KleeneStar L (w₁ ++ w₂)

/-- Совместимое имя для звёздочки Клини как языка. -/
abbrev kleeneStar (L : Set (UAM_Free.FreeMonoid α)) :
    Set (UAM_Free.FreeMonoid α) := KleeneStar L

/-- Kleene star содержит пустое слово. -/
theorem kleeneStar_empty (L : Set (UAM_Free.FreeMonoid α)) :
    ([] : UAM_Free.FreeMonoid α) ∈ kleeneStar L :=
  KleeneStar.empty

/-- Kleene star замкнут относительно конкатенации. -/
theorem kleeneStar_concat (L : Set (UAM_Free.FreeMonoid α))
    (w1 w2 : UAM_Free.FreeMonoid α)
    (h1 : w1 ∈ kleeneStar L) (h2 : w2 ∈ kleeneStar L) :
    w1 ++ w2 ∈ kleeneStar L :=
  KleeneStar.concat w1 w2 h1 h2

/-- Kleene star содержит `L`. -/
theorem kleeneStar_subset (L : Set (UAM_Free.FreeMonoid α)) : L ⊆ kleeneStar L := by
  intro w hw
  exact KleeneStar.word w hw

end UAM_RegularLanguages
