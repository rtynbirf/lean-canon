import Mathlib

/-!
# UAM Project: «Путь» — что связывает Начало и Конец

Этот файл замыкает триаду UAM:

```
Начало (x₀ ≤ x)  →  Путь (x ≤ y, y ≤ z)  →  Конец (x ≤ x∞)
   UAM_Directionality        UAM_Path           UAM_End
```

Мы формализуем понятие «Путь» тремя способами:

1. **Существительное (объект):** путь — это свидетель `c` в определении `algLe a b := ∃ c, a * c = b`.
2. **Глагол (действие):** «пройти путь» — это операция `step a s = a * s`.
3. **Результат:** конечное состояние `b`, достигнутое из `a`.

Для содержательной теории вводятся **генераторы** (`Generators`) — атомарные шаги, из
которых строятся все пути (`Path`). Свободный моноид `FreeMonoid` играет роль
пространства **всех** путей над алфавитом генераторов.

Комментарии на русском языке.
-/

open scoped Classical

namespace UAM_Path_ns

/-! ## Базовые определения (продублированы из `UAM_Directionality` и `UAM_End`) -/

section Basic

variable {M : Type*} [Monoid M]

/-- Алгебраический порядок: `a ≤ₘ b`, если существует «путь» `c` из `a` в `b`
    (то есть элемент `c`, «достраивающий» `a` до `b`). -/
def algLe (a b : M) : Prop := ∃ c : M, a * c = b

/-- «Начало» — элемент, из которого достижим любой элемент моноида. -/
def IsBeginning (e : M) : Prop := ∀ x, algLe e x

/-- «Конец» — элемент, достижимый из любого элемента моноида. -/
def IsEnd (e : M) : Prop := ∀ x, algLe x e

/-- Ограниченный моноид: моноид с правым поглощающим элементом (Концом). -/
class Bounded (M : Type*) [Monoid M] where
  end_ : M
  absorbing : ∀ x : M, x * end_ = end_

/-- Рефлексивность: пустой путь `c = 1` ведёт из `a` в `a`. -/
theorem algLe_refl (a : M) : algLe a a := ⟨1, mul_one a⟩

/-- Транзитивность: пути можно склеивать (конкатенация свидетелей). -/
theorem algLe_trans {a b c : M} (h1 : algLe a b) (h2 : algLe b c) : algLe a c := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  exact ⟨u * v, by rw [← mul_assoc, hu, hv]⟩

/-- Единица `1` — это Начало: из неё достижимо всё (`1 · x = x`). -/
theorem one_isBeginning : IsBeginning (1 : M) := fun x => ⟨x, one_mul x⟩

end Basic

/-! ## Шаг и путь через генераторы -/

section Steps

variable {M : Type*} [Monoid M]

/-- «Шаг» из состояния `a`: применение одного генератора `s`.
    В алгебраических терминах: `a → a · s`. Это «Путь-глагол» (действие). -/
def step (a : M) (s : M) : M := a * s

/-- Множество генераторов моноида `M`: элементы `carrier` — «атомарные шаги»,
    из которых строится любой элемент моноида (свойство `spanning`). -/
structure Generators (M : Type*) [Monoid M] where
  /-- Множество генераторов. -/
  carrier : Set M
  /-- Каждый элемент моноида есть произведение генераторов. -/
  spanning : ∀ x : M, x ∈ Submonoid.closure carrier

/-- «Путь-объект» от `a` до `b` над множеством генераторов `S`:
    слово `word` из генераторов, произведение которого переводит `a` в `b`. -/
structure Path (M : Type*) [Monoid M] (S : Set M) (a b : M) where
  /-- Слово генераторов (последовательность атомарных шагов). -/
  word : List {s : M // s ∈ S}
  /-- Проходя все шаги слова из `a`, попадаем в `b`. -/
  evals : a * (word.map (fun σ => σ.1)).prod = b

/-- Длина пути — число элементарных шагов в слове. -/
def Path.length {S : Set M} {a b : M} (p : Path M S a b) : ℕ := p.word.length

/-- Каждый путь (объект) порождает свидетеля алгебраического порядка:
    «Путь» ⇒ `a ≤ₘ b`. -/
theorem Path.toAlgLe {S : Set M} {a b : M} (p : Path M S a b) : algLe a b :=
  ⟨(p.word.map (fun σ => σ.1)).prod, p.evals⟩

/-- Пустой путь (слово длины 0) ведёт из `a` в `a`. -/
def Path.nil {S : Set M} (a : M) : Path M S a a where
  word := []
  evals := by simp

/-- Единичный шаг генератором `s ∈ S` — путь из `a` в `a · s` длины 1. -/
def Path.single {S : Set M} (a : M) {s : M} (hs : s ∈ S) : Path M S a (a * s) where
  word := [⟨s, hs⟩]
  evals := by simp

/-- Конкатенация путей: путь из `a` в `b` и путь из `b` в `c` дают путь из `a` в `c`.
    Длина результата — сумма длин. -/
def Path.append {S : Set M} {a b c : M} (p : Path M S a b) (q : Path M S b c) :
    Path M S a c where
  word := p.word ++ q.word
  evals := by
    have hp := p.evals
    have hq := q.evals
    simp only [List.map_append, List.prod_append]
    rw [← mul_assoc, hp, hq]

@[simp] theorem Path.length_append {S : Set M} {a b c : M}
    (p : Path M S a b) (q : Path M S b c) :
    (p.append q).length = p.length + q.length := by
  simp [Path.append, Path.length]

end Steps

/-! ## Путь как свидетель `algLe` -/

section Witness

variable {M : Type*} [Monoid M]

/-- Упрощённое понятие: «Путь» от `a` до `b` = наличие свидетеля `c` с `a · c = b`. -/
def pathFrom (a b : M) : Prop := algLe a b

/-- Путь от Начала всегда существует: `1 ≤ₘ x` (свидетель — сам `x`). -/
theorem path_from_beginning (x : M) : algLe (1 : M) x := ⟨x, one_mul x⟩

/-! ### Теорема B: тривиальность пути до Конца

Если `M` ограничен (есть поглощающий Конец `e`), то путь до Конца существует
для любого `x`, но он **тривиален**: свидетель всегда равен самому Концу. -/

/-- Для любого `x` существует путь до Конца: `x · e = e` (берём `c = e`). -/
theorem trivial_path_to_end [Bounded M] (x : M) : ∃ c, x * c = Bounded.end_ :=
  ⟨Bounded.end_, Bounded.absorbing x⟩

/-- Поглощающий элемент действительно является Концом. -/
theorem end_isEnd [Bounded M] : IsEnd (Bounded.end_ : M) :=
  fun x => trivial_path_to_end x

/-- Канонический путь до Конца всегда один и тот же — сам Конец (`c = e`).
    Поэтому «путь до Конца» не несёт информации, и для нетривиальной теории
    путей нужны ограничения на допустимые промежуточные шаги. -/
theorem path_to_end_canonical [Bounded M] (x : M) :
    x * Bounded.end_ = Bounded.end_ := Bounded.absorbing x

end Witness

/-! ## Теорема A: единственность пути и роль сокращаемости -/

section Uniqueness

/-- **Единственность при сокращаемости.** В моноиде с левым сокращением путь
    от `a` до `b` единствен: если `a · c₁ = b` и `a · c₂ = b`, то `c₁ = c₂`.
    (Направленность / trivial units сами по себе этого не гарантируют.) -/
theorem path_unique {M : Type*} [LeftCancelMonoid M] {a b c₁ c₂ : M}
    (h1 : a * c₁ = b) (h2 : a * c₂ = b) : c₁ = c₂ :=
  mul_left_cancel (h1.trans h2.symm)

/-- **Множественность в общем моноиде.** Без сокращаемости путей может быть много:
    в `(ℕ, ·)` из `0` в `0` ведут разные свидетели (`1 ≠ 2`), ибо `0` поглощает. -/
theorem path_not_unique :
    ∃ (a b c₁ c₂ : ℕ), a * c₁ = b ∧ a * c₂ = b ∧ c₁ ≠ c₂ :=
  ⟨0, 0, 1, 2, by norm_num, by norm_num, by norm_num⟩

end Uniqueness

/-! ## Свободный моноид как пространство всех путей -/

section Free

variable {M : Type*} [Monoid M]

/-- Гомоморфизм вычисления `eval f : FreeMonoid α →* M`: отправляет каждый путь
    (слово над алфавитом `α`) в элемент моноида, который он порождает.
    Общий моноид `M` — это фактор свободного моноида по отношениям. -/
def eval {α : Type*} (f : α → M) : FreeMonoid α →* M := FreeMonoid.lift f

@[simp] theorem eval_of {α : Type*} (f : α → M) (a : α) :
    eval f (FreeMonoid.of a) = f a := by
  simp [eval]

/-- Вычисление уважает конкатенацию путей (моноидный гомоморфизм). -/
theorem eval_mul {α : Type*} (f : α → M) (u v : FreeMonoid α) :
    eval f (u * v) = eval f u * eval f v := by
  simp [eval]

/-- Если генераторы порождают весь моноид (`f` сюръективна на порождающих),
    то `eval` сюръективен: любой элемент `M` есть образ некоторого пути. -/
theorem eval_surjective {α : Type*} (f : α → M)
    (hf : ∀ x : M, x ∈ Submonoid.closure (Set.range f)) :
    Function.Surjective (eval f) := by
  intro x
  have hx : x ∈ Submonoid.closure (Set.range f) := hf x
  induction hx using Submonoid.closure_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact ⟨FreeMonoid.of a, by simp [eval]⟩
  | one => exact ⟨1, by simp⟩
  | mul a b _ _ ha hb =>
      obtain ⟨u, rfl⟩ := ha; obtain ⟨v, rfl⟩ := hb
      exact ⟨u * v, by rw [map_mul]⟩

end Free

/-! ### В свободном моноиде путь единствен

Свободный моноид сокращаем, поэтому в нём разные слова дают разные элементы,
и путь от `a` до `b` единствен. Это и есть «строгость» порядка на путях:
направленность = нетривиальность порядка на путях. -/

/-- В свободном моноиде путь единствен: `x · c₁ = x · c₂ → c₁ = c₂`. -/
theorem freeMonoid_path_unique {α : Type*} {x c₁ c₂ : FreeMonoid α}
    (h1 : x * c₁ = x * c₂) : c₁ = c₂ := mul_left_cancel h1

/-- В частности, путь от единицы `1` до `x` единствен и равен `x`. -/
theorem freeMonoid_path_from_one {α : Type*} {x c : FreeMonoid α}
    (h : (1 : FreeMonoid α) * c = x) : c = x := by simpa using h

/-! ## Категорная интерпретация: морфизм = путь

Рассмотрим моноид `M` как категорию с одним объектом (или как preorder-категорию
через `algLe`). Тогда:

* `f : 1 → x` есть всегда (`f = x`, ибо `1 · x = x`) — путь от Начала;
* `h : y → e` есть всегда для Конца `e` (`h = e`, ибо `y · e = e`) — путь до Конца;
* `g : x → y` существует ⇔ `x ≤ₘ y`.

Ключевое наблюдение: в этой картине морфизмы **тривиальны** — каждый задаётся одним
элементом моноида. Содержательность появляется при ограничении морфизмов до
генераторов (`Path` над `Generators`). -/

section Category

variable {M : Type*} [Monoid M]

/-- Морфизм-путь от Начала к `x` существует всегда. -/
theorem morphism_from_beginning (x : M) : algLe (1 : M) x := path_from_beginning x

/-- Морфизм-путь до Конца существует всегда (в ограниченном моноиде). -/
theorem morphism_to_end [Bounded M] (x : M) : algLe x (Bounded.end_) :=
  end_isEnd x

/-- Композиция морфизмов-путей = транзитивность `algLe` = склейка путей. -/
theorem morphism_comp {x y z : M} (g : algLe x y) (h : algLe y z) : algLe x z :=
  algLe_trans g h

/-- Тождественный морфизм-путь = рефлексивность `algLe` = пустой путь. -/
theorem morphism_id (x : M) : algLe x x := algLe_refl x

end Category

end UAM_Path_ns
