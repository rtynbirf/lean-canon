import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_Free             -- FreeMonoid, lift, of, empty
import RequestProject.Atlas.UAM_Congruence       -- IsCongruence, QuotientMonoid
import RequestProject.Atlas.UAM_Morphism         -- MonoidMorphism, comp

/-!
# UAM — Layer 9: Презентации моноидов (Presentation)

Презентация моноида `⟨X | R⟩` — это фактор свободного моноида `FreeMonoid X`
по наименьшей конгруэнции, содержащей заданные соотношения `R`.

Наименьшая такая конгруэнция строится как пересечение всех конгруэнций,
содержащих `R` (нормальное замыкание). Затем доказывается универсальное
свойство презентации.

Замечание об именах: тип свободного моноида везде записан полностью как
`UAM_Free.FreeMonoid`, чтобы избежать неоднозначности с `_root_.FreeMonoid`
из Mathlib.
-/

namespace UAM_Presentation
universe u

open UAM_Idempotent UAM_Congruence UAM_Morphism

variable {α : Type u}

/-! ### Определения -/

/-- Соотношение: пара слов свободного моноида. -/
abbrev Relation (α : Type u) := UAM_Free.FreeMonoid α × UAM_Free.FreeMonoid α

/-- Множество всех конгруэнций на `FreeMonoid α`, содержащих все соотношения из `R`. -/
def congruencesContaining (R : Set (Relation α)) :
    Set (IsCongruence (UAM_Free.FreeMonoid α)) :=
  { θ | ∀ r ∈ R, θ.r r.1 r.2 }

/-- Конгруэнция, порождённая `R`: пересечение всех конгруэнций, содержащих `R`.
    Это наименьшая конгруэнция, содержащая `R`. -/
def normalClosure (R : Set (Relation α)) :
    IsCongruence (UAM_Free.FreeMonoid α) where
  r w1 w2 := ∀ θ ∈ congruencesContaining R, θ.r w1 w2
  refl := fun _ θ _ => θ.refl _
  symm := fun _ _ h θ hθ => θ.symm _ _ (h θ hθ)
  trans := fun _ _ _ h1 h2 θ hθ => θ.trans _ _ _ (h1 θ hθ) (h2 θ hθ)
  mul_compat := fun _ _ _ _ h1 h2 θ hθ =>
    θ.mul_compat _ _ _ _ (h1 θ hθ) (h2 θ hθ)
  one_compat := fun θ _ => θ.one_compat

/-- Презентация моноида: генераторы `α` и соотношения `R`.
    Представленный моноид — фактор свободного моноида по нормальному замыканию `R`. -/
abbrev PresentedMonoid (α : Type u) (R : Set (Relation α)) :=
  QuotientMonoid (normalClosure R)

/-! ### §1. Свойства нормального замыкания -/

/-- `normalClosure R` содержится в любой конгруэнции, содержащей `R`. -/
theorem normalClosure_minimal (R : Set (Relation α))
    (θ : IsCongruence (UAM_Free.FreeMonoid α))
    (hθ : θ ∈ congruencesContaining R) :
    ∀ w1 w2, (normalClosure R).r w1 w2 → θ.r w1 w2 :=
  fun _ _ h => h θ hθ

/-- Каждое соотношение из `R` выполнено в `normalClosure R`. -/
theorem normalClosure_contains_R (R : Set (Relation α)) {r : Relation α} (hr : r ∈ R) :
    (normalClosure R).r r.1 r.2 :=
  fun _ hθ => hθ r hr

/-- Характеризация нормального замыкания (тавтология из определения):
    `w1 ~ w2` тогда и только тогда, когда это выполнено во всех конгруэнциях,
    содержащих `R`. -/
theorem normalClosure_universal (R : Set (Relation α)) (w1 w2 : UAM_Free.FreeMonoid α) :
    (normalClosure R).r w1 w2 ↔ ∀ θ ∈ congruencesContaining R, θ.r w1 w2 :=
  Iff.rfl

/-- Любое слово из `R` лежит в замыкании (частный случай `normalClosure_contains_R`). -/
theorem normalClosure_singleton (R : Set (Relation α)) (r : Relation α) (hr : r ∈ R) :
    (normalClosure R).r r.1 r.2 :=
  normalClosure_contains_R R hr

/-- Монотонность: если `R ⊆ S`, то `normalClosure S` грубее `normalClosure R`. -/
theorem normalClosure_mono (R S : Set (Relation α)) (hRS : R ⊆ S) :
    ∀ w1 w2, (normalClosure R).r w1 w2 → (normalClosure S).r w1 w2 := by
  intro w1 w2 h θ hθ
  exact h θ (fun r hr => hθ r (hRS hr))

/-- Нормальное замыкание пустого множества соотношений — равенство слов. -/
theorem normalClosure_empty (w1 w2 : UAM_Free.FreeMonoid α) :
    (normalClosure (∅ : Set (Relation α))).r w1 w2 ↔ w1 = w2 := by
  constructor
  · intro h
    exact h (trivial_congruence (UAM_Free.FreeMonoid α))
      (fun _ hr => hr.elim)
  · intro h
    rw [h]
    exact (normalClosure (∅ : Set (Relation α))).refl w2

/-- Из конгруэнтности в замыкании пустого множества следует равенство слов. -/
theorem normalClosure_empty_imp {w1 w2 : UAM_Free.FreeMonoid α}
    (h : (normalClosure (∅ : Set (Relation α))).r w1 w2) : w1 = w2 :=
  (normalClosure_empty w1 w2).mp h

/-! ### §2. Универсальное свойство презентации -/

variable {N : Type u} [Monoid N]

/-- Морфизм `f` «убивает» соотношения `R`, если `f r.1 = f r.2` для всех `r ∈ R`. -/
def killsRelations (R : Set (Relation α))
    (f : MonoidMorphism (UAM_Free.FreeMonoid α) N) : Prop :=
  ∀ r ∈ R, f.toFun r.1 = f.toFun r.2

/-- Ядро морфизма, убивающего `R`, содержит все соотношения `R`. -/
theorem kernel_mem_congruencesContaining (R : Set (Relation α))
    (f : MonoidMorphism (UAM_Free.FreeMonoid α) N) (hf : killsRelations R f) :
    f.kernel ∈ congruencesContaining R :=
  fun r hr => hf r hr

/-- Универсальное свойство презентации: если морфизм `f` убивает все
    соотношения из `R`, то он факторизуется через `PresentedMonoid α R`. -/
def presentedLift (R : Set (Relation α)) (f : MonoidMorphism (UAM_Free.FreeMonoid α) N)
    (hf : killsRelations R f) : MonoidMorphism (PresentedMonoid α R) N where
  toFun := Quotient.lift (s := congruenceSetoid (normalClosure R)) f.toFun (by
    intro a b hab
    exact hab f.kernel (kernel_mem_congruencesContaining R f hf))
  map_mul := by
    refine fun x y => Quotient.inductionOn₂ x y ?_
    intro a b
    show f.toFun (a * b) = f.toFun a * f.toFun b
    exact f.map_mul a b
  map_one := f.map_one

/-- Факторизованный морфизм согласован с канонической проекцией. -/
theorem presentedLift_mk (R : Set (Relation α))
    (f : MonoidMorphism (UAM_Free.FreeMonoid α) N)
    (hf : killsRelations R f) (w : UAM_Free.FreeMonoid α) :
    (presentedLift R f hf).toFun (QuotientMonoid.mk w) = f.toFun w := rfl

/-- Универсальное свойство на уровне алфавита: любое `f : α → N`, порождающее
    морфизм, убивающий `R`, факторизуется через `α → PresentedMonoid α R`. -/
theorem presentedLift_of (R : Set (Relation α)) (f : α → N)
    (hf : killsRelations R (UAM_Free.FreeMonoid.lift f)) (a : α) :
    (presentedLift R (UAM_Free.FreeMonoid.lift f) hf).toFun
      (QuotientMonoid.mk (UAM_Free.FreeMonoid.of a)) = f a := by
  rw [presentedLift_mk]
  exact UAM_Free.FreeMonoid.lift_of f a

/-- Единственность факторизации через `PresentedMonoid`. -/
theorem presentedLift_unique (R : Set (Relation α))
    (f : MonoidMorphism (UAM_Free.FreeMonoid α) N)
    (hf : killsRelations R f)
    (g : MonoidMorphism (PresentedMonoid α R) N)
    (hg : ∀ w, g.toFun (QuotientMonoid.mk w) = f.toFun w) :
    g.toFun = (presentedLift R f hf).toFun := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w => exact (hg w).trans (presentedLift_mk R f hf w).symm

/-! ### §3. Примеры презентаций -/

variable {a₁ a₂ a : α}

/-- Презентация с соотношением `ab = ba` делает `a` и `b` коммутирующими
    в представленном моноиде. -/
theorem presentation_commutative (R : Set (Relation α))
    (hab : (([a₁, a₂] : UAM_Free.FreeMonoid α), ([a₂, a₁] : UAM_Free.FreeMonoid α)) ∈ R) :
    (QuotientMonoid.mk [a₁] : PresentedMonoid α R) * QuotientMonoid.mk [a₂]
      = QuotientMonoid.mk [a₂] * QuotientMonoid.mk [a₁] := by
  rw [← QuotientMonoid.mk_mul, ← QuotientMonoid.mk_mul]
  exact QuotientMonoid.mk_eq_iff.mpr (normalClosure_contains_R R hab)

/-- Презентация с соотношением `a*a = 1`: в фактор-моноиде `a² = 1`. -/
theorem presentation_group_one_rel (R : Set (Relation α))
    (hrel : ((UAM_Free.FreeMonoid.of a ++ UAM_Free.FreeMonoid.of a),
      (UAM_Free.FreeMonoid.empty : UAM_Free.FreeMonoid α)) ∈ R) :
    (QuotientMonoid.mk (UAM_Free.FreeMonoid.of a) : PresentedMonoid α R)
      * QuotientMonoid.mk (UAM_Free.FreeMonoid.of a) = 1 := by
  rw [← QuotientMonoid.mk_mul]
  show (QuotientMonoid.mk (UAM_Free.FreeMonoid.of a ++ UAM_Free.FreeMonoid.of a)
    : PresentedMonoid α R) = 1
  rw [← QuotientMonoid.mk_one]
  exact QuotientMonoid.mk_eq_iff.mpr (normalClosure_contains_R R hrel)

/-- Презентация без соотношений — свободный моноид: фактор по тривиальной
    конгруэнции изоморфен исходному свободному моноиду. -/
def presentation_no_relations : PresentedMonoid α ∅ ≃* UAM_Free.FreeMonoid α where
  toFun := Quotient.lift (s := congruenceSetoid (normalClosure ∅)) id
    (fun _ _ h => normalClosure_empty_imp h)
  invFun := QuotientMonoid.mk
  left_inv := by
    refine fun x => Quotient.inductionOn x ?_
    intro a
    rfl
  right_inv := fun _ => rfl
  map_mul' := by
    refine fun x y => Quotient.inductionOn₂ x y ?_
    intro a b
    rfl

/-! ### §4. Связь со свободным моноидом -/

/-- Свободный моноид изоморфен презентации `⟨α | ∅⟩`. -/
def free_as_presented : PresentedMonoid α ∅ ≃* UAM_Free.FreeMonoid α :=
  presentation_no_relations

end UAM_Presentation
