/-
# OSA-4.0 — аудит системы типов (ось D)

Запрос аудита: «проверь antisymmetry: `IsSubtype a b → IsSubtype b a → a = b`»
и «валидируй TypeLattice: `CalibratedValue ⊑ MeasuredValue ⊑ Datum`».

**Результат аудита.**  Антисимметрия **не является** свойством произвольной
решётки типов: `IsSubtype` определена как рефлексивно-транзитивное замыкание
объявленных рёбер, поэтому объявление цикла `A ⊑ B`, `B ⊑ A` даёт
`IsSubtype A B ∧ IsSubtype B A` при `A ≠ B`
(`isSubtype_not_antisymmetric` — доказанный контрпример).

Точная граница найдена и доказана: антисимметрия влечёт отсутствие
объявленных двухзвенных циклов и **следует** из существования градуировки —
функции ранга, строго возрастающей вдоль объявленных рёбер
(`TypeLattice.antisymmetric_of_graded`).  Рабочая решётка кодекса
`CalibratedValue ⊑ MeasuredValue ⊑ Datum` градуирована, поэтому для неё
антисимметрия доказана (`demoLattice_antisymmetric`), как и отсутствие
обратных отношений (`demoLattice_no_reverse`).
-/
import RequestProject.OSA4.BasisWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

namespace TypeLattice

/-- Антисимметрия отношения подтипизации как свойство конкретной решётки. -/
def Antisymmetric (L : TypeLattice) : Prop :=
  ∀ a b : TypeTag, L.IsSubtype a b → L.IsSubtype b a → a = b

/-- Градуировка решётки: функция ранга, строго возрастающая вдоль каждого
объявленного ребра подтипизации. -/
def Graded (L : TypeLattice) (r : TypeTag → ℕ) : Prop :=
  ∀ p ∈ L.edges, r p.1 < r p.2

/-- Вдоль подтипизации ранг не убывает. -/
theorem rank_le_of_isSubtype {L : TypeLattice} {r : TypeTag → ℕ} (hg : Graded L r)
    {a b : TypeTag} (hab : L.IsSubtype a b) : r a ≤ r b := by
  induction hab with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_of_lt (lt_of_le_of_lt ih (hg _ hstep))

/-- Для различных меток ранг вдоль подтипизации возрастает строго. -/
theorem rank_lt_of_isSubtype_of_ne {L : TypeLattice} {r : TypeTag → ℕ} (hg : Graded L r)
    {a b : TypeTag} (hab : L.IsSubtype a b) (hne : a ≠ b) : r a < r b := by
  rcases Relation.ReflTransGen.cases_head hab with h | ⟨c, hac, hcb⟩
  · exact absurd h hne
  · exact lt_of_lt_of_le (hg _ hac) (rank_le_of_isSubtype hg hcb)

/-- **Достаточное условие антисимметрии.**  Градуированная решётка типов
антисимметрична. -/
theorem antisymmetric_of_graded {L : TypeLattice} {r : TypeTag → ℕ} (hg : Graded L r) :
    L.Antisymmetric := by
  intro a b hab hba
  by_contra hne
  have h₁ : r a < r b := rank_lt_of_isSubtype_of_ne hg hab hne
  have h₂ : r b < r a := rank_lt_of_isSubtype_of_ne hg hba (Ne.symm hne)
  omega

/-- **Необходимое условие антисимметрии.**  Антисимметричная решётка не
содержит объявленного цикла из двух различных меток. -/
theorem no_two_cycle_of_antisymmetric {L : TypeLattice} (h : L.Antisymmetric)
    {a b : TypeTag} (hab : L.Edge a b) (hba : L.Edge b a) : a = b :=
  h a b (isSubtype_of_edge _ hab) (isSubtype_of_edge _ hba)

end TypeLattice

/-! ## Контрпример: антисимметрия не выводится из LAW-001/LAW-002 -/

/-- Решётка с объявленным циклом `A ⊑ B`, `B ⊑ A`. -/
def cyclicLattice : TypeLattice := ⟨[("A", "B"), ("B", "A")]⟩

/-- В циклической решётке обе метки — подтипы друг друга. -/
theorem cyclicLattice_both :
    cyclicLattice.IsSubtype "A" "B" ∧ cyclicLattice.IsSubtype "B" "A" := by
  constructor
  · exact TypeLattice.isSubtype_of_edge _ (by simp [TypeLattice.Edge, cyclicLattice])
  · exact TypeLattice.isSubtype_of_edge _ (by simp [TypeLattice.Edge, cyclicLattice])

/-- **Аудит: антисимметрия НЕ выполняется для произвольной решётки типов.**
Законы LAW-001 (рефлексивность) и LAW-002 (транзитивность) её не влекут:
объявление цикла даёт контрпример. -/
theorem isSubtype_not_antisymmetric :
    ¬ ∀ (L : TypeLattice) (a b : TypeTag), L.IsSubtype a b → L.IsSubtype b a → a = b := by
  intro h
  have := h cyclicLattice "A" "B" cyclicLattice_both.1 cyclicLattice_both.2
  exact absurd this (by decide)

/-- Циклическая решётка не градуирована — то есть контрпример не нарушает
`antisymmetric_of_graded`. -/
theorem cyclicLattice_not_graded : ¬ ∃ r : TypeTag → ℕ, TypeLattice.Graded cyclicLattice r := by
  rintro ⟨r, hg⟩
  have h₁ : r "A" < r "B" := hg ("A", "B") (by simp [cyclicLattice])
  have h₂ : r "B" < r "A" := hg ("B", "A") (by simp [cyclicLattice])
  omega

/-! ## Валидация рабочей решётки `CalibratedValue ⊑ MeasuredValue ⊑ Datum` -/

/-- Ранг меток рабочей решётки: чем конкретнее тип, тем меньше ранг. -/
def demoRank (t : TypeTag) : ℕ :=
  if t = "CalibratedValue" then 0
  else if t = "MeasuredValue" then 1
  else if t = "Datum" then 2
  else 3

/-- Рабочая решётка градуирована рангом `demoRank`. -/
theorem demoLattice_graded : TypeLattice.Graded demoLattice demoRank := by
  intro p hp
  simp only [demoLattice, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp [demoRank]

/-- **Аудит: рабочая решётка типов антисимметрична.** -/
theorem demoLattice_antisymmetric : demoLattice.Antisymmetric :=
  TypeLattice.antisymmetric_of_graded demoLattice_graded

/-- Объявленная цепочка выводится полностью: оба ребра и их композиция. -/
theorem demoLattice_chain :
    demoLattice.IsSubtype "CalibratedValue" "MeasuredValue" ∧
    demoLattice.IsSubtype "MeasuredValue" "Datum" ∧
    demoLattice.IsSubtype "CalibratedValue" "Datum" :=
  ⟨TypeLattice.isSubtype_of_edge _ (by simp [TypeLattice.Edge, demoLattice]),
    TypeLattice.isSubtype_of_edge _ (by simp [TypeLattice.Edge, demoLattice]),
    basis_law002_positive⟩

/-- Обратных отношений в рабочей решётке нет: надтип не является подтипом. -/
theorem demoLattice_no_reverse :
    ¬ demoLattice.IsSubtype "Datum" "CalibratedValue" ∧
    ¬ demoLattice.IsSubtype "MeasuredValue" "CalibratedValue" ∧
    ¬ demoLattice.IsSubtype "Datum" "MeasuredValue" := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;>
    · have := TypeLattice.rank_le_of_isSubtype demoLattice_graded h
      simp [demoRank] at this

/-- Метка, не объявленная в решётке, ни с чем не сравнима, кроме себя:
решётка не «додумывает» отношения. -/
theorem demoLattice_unheard :
    demoLattice.IsSubtype "Unheard" "Unheard" ∧ ¬ demoLattice.IsSubtype "Unheard" "Datum" := by
  refine ⟨demoLattice.isSubtype_refl _, ?_⟩
  intro h
  have := TypeLattice.rank_le_of_isSubtype demoLattice_graded h
  simp [demoRank] at this

end Polymath.OSA4
