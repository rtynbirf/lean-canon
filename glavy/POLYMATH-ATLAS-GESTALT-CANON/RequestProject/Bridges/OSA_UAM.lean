/-
# Мост 3: OSA-4 (операторы и цепочки) ↔ UAM (свободный моноид, Майхилл–Нероуд)

Цепочка операторов OSA — это слово свободного моноида `List Op`, а исполнение
`execChain` — действие этого моноида на пространстве состояний `KState`.
Мост делает соответствие точным:

* `execChain_append` / `execAction_hom` — исполнение есть **гомоморфизм
  свободного моноида цепочек в моноид преобразований состояния**
  (представление Кэли для операторного слоя);
* `ChainEquiv` — отношение «цепочки приводят к одному состоянию» — это
  конгруэнция; `chainEquiv_right_congruence` — правая инвариантность,
  то есть условие Майхилла–Нероуда;
* `opLanguage` — язык успешных цепочек для цели; `opLanguage_union_of_classes`:
  он является объединением классов эквивалентности (насыщен относительно
  `ChainEquiv`), то есть допускает автоматное описание в точности так же,
  как регулярный язык описывается классами Нероуда;
* `chainEquiv_refines_nerode` — эквивалентность по состоянию сильнее
  эквивалентности по языку: различие состояний — единственный источник
  различия поведения.
-/
import RequestProject.OSA5.Repair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.Bridges.OSA_UAM

open Polymath.OSA4
open Polymath.OSA5

/-! ## Исполнение цепочки как действие свободного моноида -/

/-- Действие цепочки на состояниях. -/
def execAction (ops : List Op) : KState → KState := fun s => execChain ops s

/-- Пустая цепочка действует тождественно. -/
@[simp] theorem execAction_nil : execAction [] = id := rfl

/-- **Гомоморфизм свободного моноида.**  Действие конкатенации цепочек равно
композиции действий: `execAction (x ++ y) = execAction y ∘ execAction x`. -/
theorem execAction_hom (x y : List Op) :
    execAction (x ++ y) = execAction y ∘ execAction x := by
  funext s
  simp [execAction, Polymath.OSA5.execChain_append]

/-! ## Эквивалентность цепочек по состоянию (Майхилл–Нероуд для операторов) -/

/-- Цепочки эквивалентны в состоянии `s`, если приводят в одно и то же
состояние. -/
def ChainEquiv (s : KState) (x y : List Op) : Prop :=
  execChain x s = execChain y s

theorem chainEquiv_refl (s : KState) (x : List Op) : ChainEquiv s x x := rfl

theorem chainEquiv_symm {s : KState} {x y : List Op} (h : ChainEquiv s x y) :
    ChainEquiv s y x := h.symm

theorem chainEquiv_trans {s : KState} {x y z : List Op}
    (h₁ : ChainEquiv s x y) (h₂ : ChainEquiv s y z) : ChainEquiv s x z := h₁.trans h₂

/-- **Правая инвариантность (условие Майхилла–Нероуда).**  Эквивалентные
цепочки остаются эквивалентными после любого продолжения. -/
theorem chainEquiv_right_congruence {s : KState} {x y : List Op}
    (h : ChainEquiv s x y) (z : List Op) : ChainEquiv s (x ++ z) (y ++ z) := by
  unfold ChainEquiv at *
  rw [Polymath.OSA5.execChain_append, Polymath.OSA5.execChain_append, h]

/-- Эквивалентные цепочки допускают ровно одни и те же продолжения. -/
theorem chainEquiv_enabled_iff {s : KState} {x y : List Op}
    (h : ChainEquiv s x y) (z : List Op) :
    chainEnabled z (execChain x s) ↔ chainEnabled z (execChain y s) := by
  rw [h]

/-! ## Язык успешных цепочек -/

/-- Язык цели: цепочки, исполнимые из `s` и доказывающие `goal`. -/
def opLanguage (s : KState) (goal : Pred) : Set (List Op) :=
  {ops | chainEnabled ops s ∧ eval (execChain ops s) goal = .TRUE_KNOWN}

/-- Успешная цепочка компилируется в `PASS`, если структурные проверки
пройдены: язык цели — это в точности множество принимаемых компилятором
цепочек. -/
theorem mem_opLanguage_compiles_pass (reg : List Op) (s : KState) (goal : Pred)
    (ops : List Op) (hops : ops ∈ opLanguage s goal)
    (hu : unknownOperator reg ops = none)
    (hd : doubleConsume [] ops = none)
    (hl : livenessViolation goal ops = none) :
    compile ⟨reg, s, ops, goal⟩ = ⟨.PASS, none, none⟩ :=
  Polymath.OSA5.compile_pass_of_chainEnabled ⟨reg, s, ops, goal⟩ hu hd hl hops.1 hops.2

/-- **Насыщенность языка классами эквивалентности.**  Если цепочка принадлежит
языку цели, то любая эквивалентная ей *исполнимая* цепочка тоже принадлежит:
язык — объединение классов `ChainEquiv`. -/
theorem opLanguage_union_of_classes {s : KState} {goal : Pred} {x y : List Op}
    (hx : x ∈ opLanguage s goal) (hy : chainEnabled y s) (h : ChainEquiv s x y) :
    y ∈ opLanguage s goal := by
  refine ⟨hy, ?_⟩
  rw [← h]
  exact hx.2

/-- Эквивалентность по цели: цепочки неразличимы, если любое продолжение даёт
один и тот же вердикт достижения цели. -/
def GoalEquiv (s : KState) (goal : Pred) (x y : List Op) : Prop :=
  ∀ z : List Op, (eval (execChain z (execChain x s)) goal = .TRUE_KNOWN ↔
    eval (execChain z (execChain y s)) goal = .TRUE_KNOWN)

/-- **Эквивалентность по состоянию уточняет эквивалентность по цели.**
Различие поведения цепочек может происходить только из различия состояний —
это в точности содержание теоремы Майхилла–Нероуда для операторного слоя. -/
theorem chainEquiv_refines_nerode {s : KState} {goal : Pred} {x y : List Op}
    (h : ChainEquiv s x y) : GoalEquiv s goal x y := by
  intro z
  rw [h]

end Polymath.Bridges.OSA_UAM
