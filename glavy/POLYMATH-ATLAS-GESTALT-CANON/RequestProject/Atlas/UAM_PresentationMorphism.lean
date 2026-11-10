import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_Congruence
import RequestProject.Atlas.UAM_Morphism
import RequestProject.Atlas.UAM_Presentation

/-!
# UAM — Морфизмы презентаций (Presentation Morphisms)

Отображение генераторов `f : α → FreeMonoid β`, согласованное с соотношениями,
индуцирует моноидный морфизм между представленными моноидами
`PresentedMonoid α R → PresentedMonoid β S`. Конструкция сводится к
универсальному свойству презентации (`presentedLift`).
-/

namespace UAM_PresentationMorphism
universe u

open UAM_Congruence UAM_Morphism UAM_Presentation

variable {α β : Type u}

/-- Морфизм свободных моноидов, индуцированный отображением генераторов
    `f : α → FreeMonoid β` (продолжение `f` до морфизма слов). -/
def letterMap (f : α → UAM_Free.FreeMonoid β) :
    MonoidMorphism (UAM_Free.FreeMonoid α) (UAM_Free.FreeMonoid β) :=
  UAM_Free.FreeMonoid.lift f

/-- «Сырое» отображение: слова из `α` → представленный моноид `⟨β | S⟩`. -/
def inducedRaw (f : α → UAM_Free.FreeMonoid β) (S : Set (Relation β)) :
    MonoidMorphism (UAM_Free.FreeMonoid α) (PresentedMonoid β S) where
  toFun := fun w => QuotientMonoid.mk ((letterMap f).toFun w)
  map_mul := by
    intro w1 w2
    show QuotientMonoid.mk ((letterMap f).toFun (w1 * w2))
      = QuotientMonoid.mk ((letterMap f).toFun w1)
        * QuotientMonoid.mk ((letterMap f).toFun w2)
    rw [(letterMap f).map_mul, QuotientMonoid.mk_mul]
  map_one := by
    show QuotientMonoid.mk ((letterMap f).toFun 1) = 1
    rw [(letterMap f).map_one, QuotientMonoid.mk_one]

/-- Если `f` переводит каждое соотношение из `R` в конгруэнтную пару относительно
    `S`, то `inducedRaw f S` убивает `R`. -/
theorem inducedRaw_kills (f : α → UAM_Free.FreeMonoid β)
    {R : Set (Relation α)} {S : Set (Relation β)}
    (h_compat : ∀ r ∈ R,
      (normalClosure S).r ((letterMap f).toFun r.1) ((letterMap f).toFun r.2)) :
    killsRelations R (inducedRaw f S) := by
  intro r hr
  show QuotientMonoid.mk ((letterMap f).toFun r.1)
    = QuotientMonoid.mk ((letterMap f).toFun r.2)
  exact QuotientMonoid.mk_eq_iff.mpr (h_compat r hr)

/-- **Морфизм презентаций**, индуцированный согласованным отображением
    генераторов. -/
def presentedMap (f : α → UAM_Free.FreeMonoid β)
    {R : Set (Relation α)} {S : Set (Relation β)}
    (h_compat : ∀ r ∈ R,
      (normalClosure S).r ((letterMap f).toFun r.1) ((letterMap f).toFun r.2)) :
    MonoidMorphism (PresentedMonoid α R) (PresentedMonoid β S) :=
  presentedLift R (inducedRaw f S) (inducedRaw_kills f h_compat)

/-- Действие морфизма презентаций на классе слова. -/
theorem presentedMap_mk (f : α → UAM_Free.FreeMonoid β)
    {R : Set (Relation α)} {S : Set (Relation β)}
    (h_compat : ∀ r ∈ R,
      (normalClosure S).r ((letterMap f).toFun r.1) ((letterMap f).toFun r.2))
    (w : UAM_Free.FreeMonoid α) :
    (presentedMap f h_compat).toFun (QuotientMonoid.mk w)
      = QuotientMonoid.mk ((letterMap f).toFun w) := rfl

/-- Действие на генераторе `a`. -/
theorem presentedMap_of (f : α → UAM_Free.FreeMonoid β)
    {R : Set (Relation α)} {S : Set (Relation β)}
    (h_compat : ∀ r ∈ R,
      (normalClosure S).r ((letterMap f).toFun r.1) ((letterMap f).toFun r.2))
    (a : α) :
    (presentedMap f h_compat).toFun (QuotientMonoid.mk (UAM_Free.FreeMonoid.of a))
      = QuotientMonoid.mk (f a) := by
  rw [presentedMap_mk]
  show QuotientMonoid.mk ((UAM_Free.FreeMonoid.lift f).toFun (UAM_Free.FreeMonoid.of a))
    = QuotientMonoid.mk (f a)
  rw [UAM_Free.FreeMonoid.lift_of]

/-- Тождественное отображение генераторов `a ↦ [a]` индуцирует тождественный
    морфизм на классах. -/
theorem presentedMap_id {R : Set (Relation α)}
    (h_compat : ∀ r ∈ R,
      (normalClosure R).r ((letterMap (UAM_Free.FreeMonoid.of)).toFun r.1)
        ((letterMap (UAM_Free.FreeMonoid.of)).toFun r.2))
    (w : UAM_Free.FreeMonoid α) :
    (presentedMap (UAM_Free.FreeMonoid.of) h_compat).toFun (QuotientMonoid.mk w)
      = (QuotientMonoid.mk w : PresentedMonoid α R) := by
  rw [presentedMap_mk]
  apply QuotientMonoid.mk_eq_iff.mpr
  have hid : (letterMap (UAM_Free.FreeMonoid.of)).toFun w = w := by
    show (UAM_Free.FreeMonoid.lift (UAM_Free.FreeMonoid.of)).toFun w = w
    exact (UAM_Free.FreeMonoid.lift_unique (UAM_Free.FreeMonoid.of)
      UAM_Morphism.MonoidMorphism.idMorphism (fun a => rfl) w).symm
  rw [hid]
  exact (normalClosure R).refl w

end UAM_PresentationMorphism
