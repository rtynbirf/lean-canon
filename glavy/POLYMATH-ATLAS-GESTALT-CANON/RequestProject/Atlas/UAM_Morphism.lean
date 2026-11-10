import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Group            -- IsUnit'
import RequestProject.Atlas.UAM_Regular          -- IsRegular, IsZero
import RequestProject.Atlas.UAM_Congruence      -- IsCongruence, QuotientMonoid

/-!
# UAM — Layer 6: Морфизмы (Morphism)

Морфизмы моноидов (собственное определение, не Mathlib `MonoidHom`).
Ядро морфизма — конгруэнция. Основная теорема о гомоморфизме: сюръективный
морфизм индуцирует изоморфизм фактор-моноида по ядру на всю область значений.
-/

namespace UAM_Morphism
universe u

open UAM_Idempotent UAM_Group UAM_Regular UAM_Congruence

/-- Морфизм моноидов: сохраняет умножение и единицу. -/
structure MonoidMorphism (M N : Type u) [Monoid M] [Monoid N] where
  toFun : M → N
  map_mul : ∀ a b : M, toFun (a * b) = toFun a * toFun b
  map_one : toFun 1 = 1

namespace MonoidMorphism
variable {M N P : Type u} [Monoid M] [Monoid N] [Monoid P]

instance : CoeFun (MonoidMorphism M N) (fun _ => M → N) := ⟨MonoidMorphism.toFun⟩

/-- Ядро морфизма как конгруэнция. -/
def kernel (f : MonoidMorphism M N) : IsCongruence M where
  r a b := f a = f b
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  trans := fun _ _ _ h1 h2 => h1.trans h2
  mul_compat := fun _ _ _ _ h1 h2 => by rw [f.map_mul, f.map_mul, h1, h2]
  one_compat := rfl

/-- Образ морфизма. -/
def range (f : MonoidMorphism M N) : Set N := Set.range f.toFun

/-! ### §1. Базовые свойства морфизмов -/

/-- Образ идемпотента — идемпотент. -/
theorem map_idempotent {f : MonoidMorphism M N} {a : M}
    (h : IsIdempotent a) : IsIdempotent (f a) := by
  unfold IsIdempotent at h ⊢
  rw [← f.map_mul, h]

/-- Образ обратимого элемента обратим. -/
theorem map_isUnit {f : MonoidMorphism M N} {a : M}
    (h : IsUnit' a) : IsUnit' (f a) := by
  obtain ⟨b, h1, h2⟩ := h
  exact ⟨f b, by rw [← f.map_mul, h1, f.map_one],
               by rw [← f.map_mul, h2, f.map_one]⟩

/-- Композиция морфизмов — морфизм. -/
def comp (f : MonoidMorphism M N) (g : MonoidMorphism N P) :
    MonoidMorphism M P where
  toFun := g.toFun ∘ f.toFun
  map_mul := by
    intro a b
    simp only [Function.comp_apply, f.map_mul, g.map_mul]
  map_one := by simp only [Function.comp_apply, f.map_one, g.map_one]

/-- Тождественный морфизм. -/
def idMorphism : MonoidMorphism M M where
  toFun := id
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- Композиция с тождественным справа. -/
theorem comp_id (f : MonoidMorphism M N) :
    (f.comp idMorphism).toFun = f.toFun := by
  ext a; rfl

/-- Композиция с тождественным слева. -/
theorem id_comp (f : MonoidMorphism M N) :
    (idMorphism.comp f).toFun = f.toFun := by
  ext a; rfl

/-! ### §2. Ядро и образ -/

/-- Отношение ядра — равенство образов. -/
theorem kernel_eq_iff {f : MonoidMorphism M N} {a b : M} :
    f.kernel.r a b ↔ f a = f b := Iff.rfl

/-- Ядро содержит `(1, 1)`. -/
theorem kernel_contains_one (f : MonoidMorphism M N) : f.kernel.r 1 1 := rfl

/-- Принадлежность области значений. -/
theorem mem_range_iff {f : MonoidMorphism M N} {b : N} :
    b ∈ f.range ↔ ∃ a, f a = b := Iff.rfl

/-- Рефлексивность ядра. -/
theorem kernel_refl (f : MonoidMorphism M N) (a : M) : f.kernel.r a a := f.kernel.refl a

/-! ### §3. Факторизация -/

/-- Если `g` постоянна на классах ядра `f` и мультипликативна, то она
факторизуется через `M / ker f`. -/
def liftThroughQuotient {f : MonoidMorphism M N} (g : M → P)
    (h_const : ∀ a b, f a = f b → g a = g b)
    (h_mul : ∀ a b, g (a * b) = g a * g b) (h_one : g 1 = 1) :
    MonoidMorphism (QuotientMonoid f.kernel) P where
  toFun := Quotient.lift (s := congruenceSetoid f.kernel) g (by
    intro a b hab
    exact h_const a b (kernel_eq_iff.mp hab))
  map_mul := by
    refine fun x y => Quotient.inductionOn₂ x y ?_
    intro a b
    show g (a * b) = g a * g b
    exact h_mul a b
  map_one := h_one

/-- Факторизованный морфизм согласован с проекцией. -/
theorem lift_mk {f : MonoidMorphism M N} (g : M → P)
    (h_const : ∀ a b, f a = f b → g a = g b)
    (h_mul : ∀ a b, g (a * b) = g a * g b) (h_one : g 1 = 1) (a : M) :
    (liftThroughQuotient g h_const h_mul h_one).toFun
      (QuotientMonoid.mk a) = g a := rfl

/-! ### §4. Свойства, сохраняемые морфизмами -/

/-- Образ регулярного элемента регулярен. -/
theorem map_isRegular {f : MonoidMorphism M N} {a : M}
    (h : UAM_Regular.IsRegular a) : UAM_Regular.IsRegular (f a) := by
  obtain ⟨x, hx⟩ := h
  exact ⟨f x, by rw [← f.map_mul, ← f.map_mul, hx]⟩

/-- Образ регулярного «внутреннего обратного» удовлетворяет тому же тождеству. -/
theorem map_regular_idempotent {f : MonoidMorphism M N} {a x : M}
    (h : a * x * a = a) : f a * f x * f a = f a := by
  rw [← f.map_mul, ← f.map_mul, h]

/-- Образ нуля — нуль в области значений.

    **ЗАМЕЧАНИЕ.** Исходная формулировка `IsZero z → IsZero (f z)` без
    дополнительных условий ложна: `f z` поглощает лишь элементы образа, а не
    произвольные элементы `N`. Поэтому добавлена гипотеза сюръективности `hf`;
    для сюръективного морфизма образ нуля действительно является нулём. -/
theorem map_isZero {f : MonoidMorphism M N} {z : M}
    (hf : Function.Surjective f.toFun) (h : IsZero z) : IsZero (f z) := by
  refine ⟨fun y => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := hf y
    rw [← f.map_mul, h.1 a]
  · obtain ⟨a, rfl⟩ := hf y
    rw [← f.map_mul, h.2 a]

/-! ### §5. Основная теорема о гомоморфизме -/

/-- Основная теорема о гомоморфизме.
    Если `f : M → N` — сюръективный морфизм моноидов, то фактор-моноид
    `M / ker f` изоморфен `N` (как мультипликативная структура). -/
noncomputable def firstIso (f : MonoidMorphism M N) (hf : Function.Surjective f.toFun) :
    QuotientMonoid f.kernel ≃* N where
  toFun := Quotient.lift (s := congruenceSetoid f.kernel) f.toFun (by
    intro a b hab
    exact kernel_eq_iff.mp hab)
  invFun := fun n => QuotientMonoid.mk (Function.surjInv hf n)
  left_inv := by
    refine fun x => Quotient.inductionOn x ?_
    intro a
    show QuotientMonoid.mk (Function.surjInv hf (f.toFun a)) = QuotientMonoid.mk a
    exact QuotientMonoid.mk_eq_iff.mpr (Function.surjInv_eq hf (f.toFun a))
  right_inv := by
    intro n
    show f.toFun (Function.surjInv hf n) = n
    exact Function.surjInv_eq hf n
  map_mul' := by
    refine fun x y => Quotient.inductionOn₂ x y ?_
    intro a b
    show f.toFun (a * b) = f.toFun a * f.toFun b
    exact f.map_mul a b

end MonoidMorphism
end UAM_Morphism
