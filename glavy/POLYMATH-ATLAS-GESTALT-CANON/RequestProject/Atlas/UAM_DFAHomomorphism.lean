import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_DFAEval
import RequestProject.Atlas.UAM_RegularLanguages
import RequestProject.Atlas.UAM_Action
import RequestProject.Atlas.UAM_TransitionMonoid
import RequestProject.Atlas.UAM_ReverseMyhillNerode

/-!
# UAM — Гомоморфизмы DFA и минимизация (DFA Homomorphisms)

DFA-гомоморфизм — отображение состояний, коммутирующее с переходами, начальным
состоянием и принимающим множеством. Любой DFA-гомоморфизм сохраняет язык.

Отношение Нероуда на состояниях (`stateNerodeRel`) объявляет два состояния
эквивалентными, если из них принимаются одни и те же продолжения. Фактор-DFA по
этому отношению (`quotientDFA`) распознаёт тот же язык и является приведённым
(в нём нет двух различных эквивалентных состояний) — это минимальный автомат.
-/

namespace UAM_DFAHomomorphism
universe u

open UAM_DFAEval Classical

variable {α Q Q₁ Q₂ : Type u} [DecidableEq Q] [DecidableEq Q₁] [DecidableEq Q₂]

/-! ### §1. Гомоморфизмы DFA -/

/-- Гомоморфизм DFA: отображение состояний, согласованное с переходами,
    начальным состоянием и принимающим множеством. -/
structure DFAHom (A : DFA α Q₁) (B : DFA α Q₂) where
  /-- Отображение состояний. -/
  toFun : Q₁ → Q₂
  /-- Сохранение начального состояния. -/
  map_q₀ : toFun A.q₀ = B.q₀
  /-- Коммутирование с переходами. -/
  map_δ : ∀ q a, toFun (A.δ q a) = B.δ (toFun q) a
  /-- Согласованность принимающих множеств. -/
  map_F : ∀ q, q ∈ A.F ↔ toFun q ∈ B.F

namespace DFAHom
variable {A : DFA α Q₁} {B : DFA α Q₂}

/-- Гомоморфизм коммутирует с вычислением слова. -/
theorem evalFrom_map (φ : DFAHom A B) (q : Q₁) (w : UAM_Free.FreeMonoid α) :
    φ.toFun (A.evalFrom q w) = B.evalFrom (φ.toFun q) w := by
  induction w generalizing q with
  | nil => rfl
  | cons a ws ih =>
    show φ.toFun (A.evalFrom (A.δ q a) ws) = B.evalFrom (φ.toFun q) (a :: ws)
    rw [ih (A.δ q a)]
    show B.evalFrom (φ.toFun (A.δ q a)) ws = B.evalFrom (B.δ (φ.toFun q) a) ws
    rw [φ.map_δ]

/-- **Гомоморфизм DFA сохраняет язык.** -/
theorem language_eq (φ : DFAHom A B) : A.language = B.language := by
  ext w
  show A.accepts w ↔ B.accepts w
  show A.eval w ∈ A.F ↔ B.eval w ∈ B.F
  rw [φ.map_F (A.eval w)]
  have hev : φ.toFun (A.eval w) = B.eval w := by
    show φ.toFun (A.evalFrom A.q₀ w) = B.evalFrom B.q₀ w
    rw [evalFrom_map, φ.map_q₀]
  rw [hev]

end DFAHom

/-! ### §2. Отношение Нероуда на состояниях -/

/-- Отношение Нероуда на состояниях: `q₁` и `q₂` эквивалентны, если из них
    принимаются одни и те же слова. -/
def stateNerodeRel (A : DFA α Q) (q₁ q₂ : Q) : Prop :=
  ∀ w, A.evalFrom q₁ w ∈ A.F ↔ A.evalFrom q₂ w ∈ A.F

theorem stateNerodeRel_refl (A : DFA α Q) (q : Q) : stateNerodeRel A q q :=
  fun _ => Iff.rfl

theorem stateNerodeRel_symm (A : DFA α Q) {q₁ q₂ : Q}
    (h : stateNerodeRel A q₁ q₂) : stateNerodeRel A q₂ q₁ :=
  fun w => (h w).symm

theorem stateNerodeRel_trans (A : DFA α Q) {q₁ q₂ q₃ : Q}
    (h₁ : stateNerodeRel A q₁ q₂) (h₂ : stateNerodeRel A q₂ q₃) :
    stateNerodeRel A q₁ q₃ :=
  fun w => (h₁ w).trans (h₂ w)

/-- Setoid, задаваемый отношением Нероуда на состояниях. -/
def stateNerodeSetoid (A : DFA α Q) : Setoid Q where
  r := stateNerodeRel A
  iseqv := ⟨stateNerodeRel_refl A, stateNerodeRel_symm A, stateNerodeRel_trans A⟩

/-- Совместимость отношения Нероуда с переходами. -/
theorem nerode_delta {A : DFA α Q} {q₁ q₂ : Q} (h : stateNerodeRel A q₁ q₂) (a : α) :
    stateNerodeRel A (A.δ q₁ a) (A.δ q₂ a) :=
  fun w => h (a :: w)

/-- Совместимость отношения Нероуда с принимающим множеством. -/
theorem nerode_mem_F {A : DFA α Q} {q₁ q₂ : Q} (h : stateNerodeRel A q₁ q₂) :
    q₁ ∈ A.F ↔ q₂ ∈ A.F :=
  h []

/-! ### §3. Фактор-DFA (минимальный автомат) -/

/-- Фактор-DFA по отношению Нероуда на состояниях. -/
noncomputable def quotientDFA (A : DFA α Q) : DFA α (Quotient (stateNerodeSetoid A)) where
  δ := fun s a => Quotient.liftOn s
    (fun q => Quotient.mk (stateNerodeSetoid A) (A.δ q a))
    (fun _ _ hq => Quotient.sound (nerode_delta hq a))
  q₀ := Quotient.mk (stateNerodeSetoid A) A.q₀
  F := {s | Quotient.liftOn s (fun q => q ∈ A.F)
    (fun _ _ hq => propext (nerode_mem_F hq))}

/-- Вычисление фактор-DFA на классе состояния. -/
theorem quotientDFA_evalFrom (A : DFA α Q) (q : Q) (w : UAM_Free.FreeMonoid α) :
    (quotientDFA A).evalFrom (Quotient.mk (stateNerodeSetoid A) q) w
      = Quotient.mk (stateNerodeSetoid A) (A.evalFrom q w) := by
  induction w generalizing q with
  | nil => rfl
  | cons a ws ih => exact ih (A.δ q a)

/-- Каноническая проекция `A → quotientDFA A` как гомоморфизм DFA. -/
noncomputable def quotientHom (A : DFA α Q) : DFAHom A (quotientDFA A) where
  toFun := Quotient.mk (stateNerodeSetoid A)
  map_q₀ := rfl
  map_δ := fun _ _ => rfl
  map_F := fun _ => Iff.rfl

/-- **Фактор-DFA распознаёт тот же язык, что и исходный.** -/
theorem quotientDFA_language (A : DFA α Q) :
    (quotientDFA A).language = A.language :=
  (DFAHom.language_eq (quotientHom A)).symm

/-- **Минимальность (приведённость):** в фактор-DFA нет двух различных
    Нероуд-эквивалентных состояний. -/
theorem quotientDFA_reduced (A : DFA α Q)
    (S₁ S₂ : Quotient (stateNerodeSetoid A))
    (h : stateNerodeRel (quotientDFA A) S₁ S₂) : S₁ = S₂ := by
  refine Quotient.inductionOn₂ S₁ S₂ ?_ h
  intro q₁ q₂ hq
  apply Quotient.sound
  intro w
  have h1 := hq w
  rw [quotientDFA_evalFrom, quotientDFA_evalFrom] at h1
  exact h1

end UAM_DFAHomomorphism
