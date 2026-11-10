import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Morphism
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_MonoidAction

/-!
# UAM — Полупрямое произведение моноидов (Semidirect Product)

Полупрямое произведение `M ⋊ N` строится по действию моноида `N` на моноиде `M`
эндоморфизмами. Действие задаётся моноидным морфизмом `N → (M → M)` (порядок
композиции — из `UAM_Action`), причём каждый `α n` обязан быть эндоморфизмом
моноида `M` (сохранять умножение и единицу) — это необходимо для ассоциативности
произведения.

**Замечание о порядке.** Так как `UAM_Action` использует порядок
`α (n₁ * n₂) = α n₂ ∘ α n₁`, корректная (ассоциативная) формула умножения имеет
вид `(m₁, n₁) * (m₂, n₂) = (α n₂ m₁ * m₂, n₁ * n₂)`.
-/

namespace UAM_SemidirectProduct
universe u

open UAM_Action UAM_Morphism

variable {M N : Type u} [Monoid M] [Monoid N]

/-- Действие `N` на `M` эндоморфизмами: моноидный морфизм `N → (M → M)` плюс
    условия, что каждый `α n` — эндоморфизм моноида `M`. -/
structure ScalarAction (M N : Type u) [Monoid M] [Monoid N] where
  /-- Морфизм действия (порядок `UAM_Action`). -/
  toMorphism : MonoidMorphism N (M → M)
  /-- Каждый `α n` сохраняет умножение. -/
  map_mul : ∀ (n : N) (x y : M),
    toMorphism.toFun n (x * y) = toMorphism.toFun n x * toMorphism.toFun n y
  /-- Каждый `α n` сохраняет единицу. -/
  map_one : ∀ (n : N), toMorphism.toFun n 1 = 1

namespace ScalarAction
variable (σ : ScalarAction M N)

/-- Действие элемента `n` на `x`. -/
def act (n : N) (x : M) : M := σ.toMorphism.toFun n x

@[simp] theorem act_def (n : N) (x : M) : σ.act n x = σ.toMorphism.toFun n x := rfl

theorem act_one_left (x : M) : σ.act 1 x = x := by
  show σ.toMorphism.toFun 1 x = x
  rw [σ.toMorphism.map_one]; rfl

theorem act_mul_left (n₁ n₂ : N) (x : M) :
    σ.act (n₁ * n₂) x = σ.act n₂ (σ.act n₁ x) := by
  show σ.toMorphism.toFun (n₁ * n₂) x = σ.toMorphism.toFun n₂ (σ.toMorphism.toFun n₁ x)
  rw [σ.toMorphism.map_mul]; rfl

theorem act_mul_right (n : N) (x y : M) :
    σ.act n (x * y) = σ.act n x * σ.act n y := σ.map_mul n x y

theorem act_one_right (n : N) : σ.act n 1 = 1 := σ.map_one n

end ScalarAction

/-! ### §1. Полупрямое произведение -/

/-- Полупрямое произведение `M ⋊ N` относительно действия `σ`. -/
structure SemidirectProduct (σ : ScalarAction M N) where
  /-- Компонента в `M`. -/
  fst : M
  /-- Компонента в `N`. -/
  snd : N

namespace SemidirectProduct
variable {σ : ScalarAction M N}

@[ext] theorem ext {a b : SemidirectProduct σ}
    (h1 : a.fst = b.fst) (h2 : a.snd = b.snd) : a = b := by
  cases a; cases b; simp_all

/-- Моноидная структура полупрямого произведения. -/
instance instMonoid (σ : ScalarAction M N) : Monoid (SemidirectProduct σ) where
  mul a b := ⟨σ.act b.snd a.fst * b.fst, a.snd * b.snd⟩
  one := ⟨1, 1⟩
  mul_assoc a b c := by
    apply ext
    · show σ.act c.snd (σ.act b.snd a.fst * b.fst) * c.fst
        = σ.act (b.snd * c.snd) a.fst * (σ.act c.snd b.fst * c.fst)
      rw [σ.act_mul_right, σ.act_mul_left, mul_assoc]
    · show a.snd * b.snd * c.snd = a.snd * (b.snd * c.snd)
      rw [mul_assoc]
  one_mul a := by
    apply ext
    · show σ.act a.snd 1 * a.fst = a.fst
      rw [σ.act_one_right, one_mul]
    · show 1 * a.snd = a.snd
      rw [one_mul]
  mul_one a := by
    apply ext
    · show σ.act 1 a.fst * 1 = a.fst
      rw [σ.act_one_left, mul_one]
    · show a.snd * 1 = a.snd
      rw [mul_one]

@[simp] theorem mul_fst (a b : SemidirectProduct σ) :
    (a * b).fst = σ.act b.snd a.fst * b.fst := rfl

@[simp] theorem mul_snd (a b : SemidirectProduct σ) :
    (a * b).snd = a.snd * b.snd := rfl

@[simp] theorem one_fst : (1 : SemidirectProduct σ).fst = 1 := rfl
@[simp] theorem one_snd : (1 : SemidirectProduct σ).snd = 1 := rfl

/-! ### §2. Проекция на `N` как морфизм -/

/-- Проекция `M ⋊ N → N` — моноидный морфизм. -/
def sndMorphism (σ : ScalarAction M N) : MonoidMorphism (SemidirectProduct σ) N where
  toFun := SemidirectProduct.snd
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- Вложение `N → M ⋊ N`, `n ↦ (1, n)`, — моноидный морфизм (сечение проекции). -/
def inrMorphism (σ : ScalarAction M N) : MonoidMorphism N (SemidirectProduct σ) where
  toFun := fun n => ⟨1, n⟩
  map_mul := fun n₁ n₂ => by
    apply ext
    · show (1 : M) = σ.act n₂ 1 * 1
      rw [σ.act_one_right, mul_one]
    · rfl
  map_one := rfl

/-- Проекция после вложения — тождество на `N` (расщепляемое расширение). -/
theorem sndMorphism_comp_inrMorphism (σ : ScalarAction M N) (n : N) :
    (sndMorphism σ).toFun ((inrMorphism σ).toFun n) = n := rfl

end SemidirectProduct
end UAM_SemidirectProduct
