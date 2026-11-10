import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Group            -- IsUnit'
import RequestProject.Atlas.UAM_Morphism         -- MonoidMorphism

/-!
# UAM — Теорема Кэли для моноидов (Cayley)

Каждый моноид `M` вкладывается в моноид преобразований своего носителя.

Роль моноида преобразований играет обёртка `Transform M` над функциями
`M → M` с умножением-композицией в порядке «сначала левый сомножитель»
(`f * g = g ∘ f`) и тождественной функцией в качестве единицы. Такая обёртка
(вместо голого `M → M`) выбрана, чтобы не конфликтовать с поточечной
моноидной структурой `Pi.monoid`, которую Mathlib синтезирует на `M → M`,
когда `M` — моноид.

## Идея

Берётся **правое регулярное представление** `rho a := (x ↦ x * a)`. При
выбранном порядке композиции оно является моноидным гомоморфизмом:
`rho (a * b) = rho a * rho b`, поскольку
`x * (a * b) = (x * a) * b = (rho b ∘ rho a) x`. Оно инъективно, так как
значение `rho a` на единице равно `a`. Отсюда — вложение `M ↪ Transform M`.

(Левое регулярное представление `x ↦ a * x` при этом порядке композиции даёт
*анти*гомоморфизм; см. `lambdaMap_antihom`.)
-/

namespace UAM_Cayley
universe u

open UAM_Morphism

/-- Обёртка над функциями `M → M` — носитель моноида преобразований. -/
structure Transform (M : Type u) where
  /-- Функция преобразования. -/
  toFun : M → M

namespace Transform
variable {M : Type u}

@[ext] theorem ext {f g : Transform M} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; simp only [Transform.mk.injEq]; exact h

/-- Моноид преобразований: `f * g = g ∘ f`, единица — тождество. -/
instance instMonoid : Monoid (Transform M) where
  mul f g := ⟨g.toFun ∘ f.toFun⟩
  one := ⟨id⟩
  mul_assoc := fun _ _ _ => rfl
  one_mul := fun _ => rfl
  mul_one := fun _ => rfl

@[simp] theorem mul_toFun (f g : Transform M) :
    (f * g).toFun = g.toFun ∘ f.toFun := rfl

@[simp] theorem one_toFun : (1 : Transform M).toFun = id := rfl

end Transform

variable {M : Type u} [Monoid M]

/-! ### §1. Правое регулярное представление -/

/-- Правое регулярное представление как моноидный морфизм
    `M → Transform M`, `rho a = (x ↦ x * a)`. -/
def rho : MonoidMorphism M (Transform M) where
  toFun := fun a => ⟨fun x => x * a⟩
  map_mul := fun a b => by
    apply Transform.ext
    funext x
    simp only [Transform.mul_toFun, Function.comp_apply, mul_assoc]
  map_one := by
    apply Transform.ext
    funext x
    simp only [Transform.one_toFun, mul_one, id]

@[simp] theorem rho_apply (a x : M) : (rho a).toFun x = x * a := rfl

/-- Значение `rho a` на единице моноида возвращает сам элемент `a`. -/
theorem rho_one (a : M) : (rho a).toFun 1 = a := by
  simp only [rho_apply, one_mul]

/-- Правое регулярное представление инъективно. -/
theorem rho_injective : Function.Injective (rho (M := M)).toFun := by
  intro a b h
  have : (rho a).toFun 1 = (rho b).toFun 1 := by rw [h]
  rwa [rho_one, rho_one] at this

/-! ### §2. Теорема Кэли -/

/-- **Теорема Кэли для моноидов.** Существует инъективный моноидный морфизм
    из `M` в моноид преобразований `Transform M`, то есть каждый моноид
    вкладывается в моноид преобразований своего носителя. -/
theorem cayley_embedding :
    ∃ f : MonoidMorphism M (Transform M), Function.Injective f.toFun :=
  ⟨rho, rho_injective⟩

/-! ### §3. Левое регулярное представление как антигомоморфизм -/

/-- Левый сдвиг `lambdaMap a = (x ↦ a * x)`. -/
def lambdaMap (a : M) : Transform M := ⟨fun x => a * x⟩

@[simp] theorem lambdaMap_apply (a x : M) : (lambdaMap a).toFun x = a * x := rfl

/-- При выбранном порядке композиции левое регулярное представление —
    антигомоморфизм: `lambdaMap (a * b) = lambdaMap b * lambdaMap a`. -/
theorem lambdaMap_antihom (a b : M) :
    lambdaMap (a * b) = lambdaMap b * lambdaMap a := by
  apply Transform.ext
  funext x
  simp only [lambdaMap_apply, Transform.mul_toFun, Function.comp_apply, mul_assoc]

/-- Левое регулярное представление также инъективно. -/
theorem lambdaMap_injective : Function.Injective (lambdaMap (M := M)) := by
  intro a b h
  have : (lambdaMap a).toFun 1 = (lambdaMap b).toFun 1 := by rw [h]
  simpa only [lambdaMap_apply, mul_one] using this

end UAM_Cayley
