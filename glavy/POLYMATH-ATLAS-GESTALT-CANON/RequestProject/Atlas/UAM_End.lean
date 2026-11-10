import Mathlib

/-!
# UAM — «Конец» как двойственное понятие к «Началу»

Этот файл замыкает уравнение процесса

```
Начало → ... → Конец
```

формализуя понятие **«Конец»** двойственно к уже построенной теории **«Начала»**.

## Теория «Начала» (кратко напоминание)

В любом моноиде `M` определён *алгебраический порядок*
`a ≤ₘ b := ∃ c, a * c = b` (из `a` можно «дойти» до `b`, домножив справа).

* «Начало» = наименьший элемент: `IsBeginning e := ∀ x, e ≤ₘ x`.
* Ключевая теорема: `1` — всегда «Начало», и оно **единственно** тогда и только
  тогда, когда моноид *направлен* (нет нетривиальных единиц, `u * v = 1 → u = 1`).

Здесь мы дублируем эти определения (файл самодостаточен) и строим двойственную
теорию «Конца».

## Что доказано про «Конец»

* `IsEnd e := ∀ x, x ≤ₘ e` — наибольший элемент.
* «Конец» устроен НЕ симметрично «Началу»: `1` всегда «Начало», а канонического
  «конца» нет — «Конец» существует лишь при наличии глобального правого кратного
  (например, поглощающего/нулевого элемента).
* Двойственность через противоположный моноид `Mᵒᵖ` даёт лево-правую двойственность
  (условие «правых» тривиальных единиц `u * v = 1 → v = 1`).
* Для `CommMonoid` условие направленности **самодвойственно**.
* Приведены примеры, показывающие, что «Начало» и «Конец» существуют/единственны
  **независимо**.

## Итоговая таблица

| Структура                        | Начало? | Конец? | Почему                                   |
|----------------------------------|---------|--------|------------------------------------------|
| `(ℕ, +)` (`Multiplicative ℕ`)     | ✓ (0)   | ✗      | `∀ a, a ≤ e` невозможно (неограниченно)  |
| `(List α, ++)` (`FreeMonoid α`)   | ✓ ([])  | ✗      | слова сколь угодно длинные               |
| `(ℕ, ·)`                          | ✓ (1)   | ✓ (0)  | `0` поглощает: `x * 0 = 0`               |
| `WithZero (Multiplicative ℤ/2)`   | ✗(¬!)   | ✓ (0)  | нетривиальные единицы, но есть нуль       |

(«✗(¬!)» означает: «Начало» существует, но НЕ единственно.)
-/

namespace UAM_End_ns

open scoped Classical

/-! ## Часть 0. Алгебраический порядок и определения -/

section Monoid
variable {M : Type*} [Monoid M]

/-- Алгебраический порядок «`a ≤ₘ b`»: из `a` можно «дойти» до `b`,
домножив справа на некоторый `c`. -/
def algLe (a b : M) : Prop := ∃ c : M, a * c = b

/-- Двойственный алгебраический порядок «`a ≥ₘ b`» := «`b ≤ₘ a`». -/
def algGe (a b : M) : Prop := algLe b a

/-- «Начало»: наименьший элемент — из него можно дойти до любого `x`. -/
def IsBeginning (e : M) : Prop := ∀ x : M, algLe e x

/-- «Конец»: наибольший элемент — до него можно дойти из любого `x`. -/
def IsEnd (e : M) : Prop := ∀ x : M, algLe x e

@[simp] theorem algGe_iff {a b : M} : algGe a b ↔ algLe b a := Iff.rfl

/-- «Конец» через двойственный порядок: `IsEnd e ↔ ∀ x, e ≥ₘ x`. -/
theorem isEnd_iff_forall_algGe {e : M} : IsEnd e ↔ ∀ x, algGe e x := Iff.rfl

/-! ## Часть 1. «Начало»: `1` — всегда начало, единственность = направленность -/

/-- `1` — всегда «Начало». -/
theorem isBeginning_one : IsBeginning (1 : M) := fun x => ⟨x, one_mul x⟩

/-
**Ключевая теорема о «Начале».**
Моноид *направлен* (тривиальные единицы: `u * v = 1 → u = 1`) тогда и только тогда,
когда «Начало» существует и единственно.
-/
theorem hasDirection_iff_uniqueBeginning :
    (∀ u v : M, u * v = 1 → u = 1) ↔ (∃! e : M, IsBeginning e) := by
  constructor <;> intro h;
  · refine' ⟨ 1, _, _ ⟩;
    · exact isBeginning_one;
    · exact fun y hy => h y ( Classical.choose ( hy 1 ) ) ( by simpa using Classical.choose_spec ( hy 1 ) );
  · -- If there exists a unique beginning $e$, then $e = 1$.
    obtain ⟨e, he_unique⟩ := h
    have he_one : e = 1 := by
      exact he_unique.2 1 isBeginning_one ▸ rfl;
    intro u v huv
    have hu_beginning : IsBeginning u := by
      intro x
      use v * x
      rw [← mul_assoc, huv]
      simp;
    grind

/-! ## Часть 2. «Конец»: существование не автоматическое -/

/-- Правостороннее «поглощающее» (absorbing) `z` — всегда «Конец»:
до `z` можно дойти из любого `x`, взяв `c = z`. -/
theorem isEnd_of_rightAbsorbing {z : M} (hz : ∀ x, x * z = z) : IsEnd z :=
  fun x => ⟨z, hz x⟩

end Monoid

/-! ## Часть 3. Лево-правая двойственность (противоположный моноид) -/

section OppositeDuality
variable {M : Type*} [Monoid M]

/-- Левосторонний алгебраический порядок — порядок в противоположном моноиде `Mᵒᵖ`. -/
def algLe' (a b : M) : Prop := ∃ c : M, c * a = b

/-- «Левое начало» (начало в `Mᵒᵖ`): из `e` можно дойти до любого `x`
домножением **слева**. -/
def IsBeginning' (e : M) : Prop := ∀ x : M, algLe' e x

theorem isBeginning'_one : IsBeginning' (1 : M) := fun x => ⟨x, mul_one x⟩

/-
Двойственная («левая») версия ключевой теоремы: «правые» тривиальные единицы
(`u * v = 1 → v = 1`) равносильны единственности «левого начала».
-/
theorem hasCoDirection_iff_uniqueBeginning' :
    (∀ u v : M, u * v = 1 → v = 1) ↔ (∃! e : M, IsBeginning' e) := by
  refine' ⟨ fun h => ⟨ 1, isBeginning'_one, fun e he => _ ⟩, fun h => _ ⟩;
  · exact h _ _ ( he 1 |> Classical.choose_spec );
  · intro u v huv;
    convert h.unique _ _;
    · exact fun x => ⟨ x * u, by simp +decide [ mul_assoc, huv ] ⟩;
    · exact isBeginning'_one

end OppositeDuality

/-! ## Часть 4. Коммутативный случай: условие направленности самодвойственно -/

section CommMonoid
variable {M : Type*} [CommMonoid M]

/-- В коммутативном моноиде левый и правый алгебраические порядки совпадают. -/
theorem algLe_iff_algLe' (a b : M) : algLe a b ↔ algLe' a b := by
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [mul_comm]; exact hc⟩
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [mul_comm]; exact hc⟩

/-
В коммутативном моноиде условие направленности самодвойственно:
«левые» и «правые» тривиальные единицы — одно и то же условие.
-/
theorem trivialUnits_selfDual :
    (∀ u v : M, u * v = 1 → u = 1) ↔ (∀ u v : M, u * v = 1 → v = 1) := by
  grind +qlia

/-
Замечание. Исходная неформальная гипотеза «для коммутативного моноида
Начало ↔ Конец (одно условие)» в буквальном прочтении НЕВЕРНА: «Начало» всегда
существует (`1`), поэтому «существование начала» не может быть равносильно
«существованию конца» (которого может не быть, см. `(ℕ, +)`). Корректная
самодвойственность — это `trivialUnits_selfDual` выше: направленность как условие
не различает левое и правое в коммутативном случае. -/

end CommMonoid

/-! ## Часть 5. Примеры для конкретных структур -/

section Examples

/-- `(ℕ, ·)`: `0` поглощает, значит `0` — «Конец». -/
theorem nat_mul_isEnd_zero : IsEnd (0 : ℕ) :=
  isEnd_of_rightAbsorbing (fun x => mul_zero x)

/-
`(ℕ, ·)`: `0` — единственный «Конец».
-/
theorem nat_mul_uniqueEnd : ∃! e : ℕ, IsEnd e := by
  exact ⟨ 0, nat_mul_isEnd_zero, fun e he => by obtain ⟨ c, hc ⟩ := he 0; aesop ⟩

/-
`(ℕ, ·)`: `1` — единственное «Начало» (направленность мультипликативного `ℕ`).
-/
theorem nat_mul_uniqueBeginning : ∃! e : ℕ, IsBeginning e := by
  refine' ⟨ 1, _, _ ⟩;
  · exact fun x => ⟨ x, one_mul x ⟩;
  · intro y hy;
    cases' hy 1 with x hx ; cases' hy 0 with y hy ; aesop

/-
`(ℕ, +)` как `Multiplicative ℕ`: «Начало» = `0`, единственно.
-/
theorem addNat_uniqueBeginning : ∃! e : Multiplicative ℕ, IsBeginning e := by
  simp +decide [ IsBeginning ];
  refine' ⟨ Multiplicative.ofAdd 0, _, _ ⟩ <;> simp +decide [ algLe ];
  intro a ha; specialize ha 0; aesop;

/-
`(ℕ, +)`: «Конца» НЕ существует (нет наибольшего элемента).
-/
theorem addNat_no_end : ¬ ∃ e : Multiplicative ℕ, IsEnd e := by
  -- Assume for contradiction that there exists a right-absorbing element $e$ in the multiplicative monoid of natural numbers.
  by_contra h
  obtain ⟨e, he⟩ := h;
  have := he ( Multiplicative.ofAdd ( Multiplicative.toAdd e + 1 ) ) ; simp_all +decide [ IsEnd ] ;
  obtain ⟨ c, hc ⟩ := this;
  replace hc := congr_arg Multiplicative.toAdd hc ; simp_all +decide [ mul_assoc ]

/-
`(List α, ++)` = `FreeMonoid α`: «Начало» = `[]`, единственно.
-/
theorem freeMonoid_uniqueBeginning {α : Type*} :
    ∃! e : FreeMonoid α, IsBeginning e := by
  refine' ⟨ 1, _, _ ⟩ <;> simp +decide [ IsBeginning ];
  · exact fun x => ⟨ x, by simp +decide ⟩;
  · intro y hy; specialize hy 1; obtain ⟨ c, hc ⟩ := hy; simp_all +decide;

/-
`(List α, ++)` с непустым алфавитом: «Конца» НЕ существует.
-/
theorem freeMonoid_no_end {α : Type*} [Nonempty α] :
    ¬ ∃ e : FreeMonoid α, IsEnd e := by
  rintro ⟨ e, he ⟩;
  -- By definition of `IsEnd`, every word `x` is a prefix of `e`.
  have h_prefix : ∀ x : FreeMonoid α, x.toList.length ≤ e.toList.length := by
    intro x
    obtain ⟨ c, hc ⟩ := he x;
    simp +decide [ ← hc ];
  contrapose! h_prefix;
  obtain ⟨ a ⟩ := ‹Nonempty α›; use FreeMonoid.ofList ( List.replicate ( e.toList.length + 1 ) a ) ; simp +decide ;

/-! ### Независимость «Начала» и «Конца»

`WithZero (Multiplicative (ZMod 2))` — коммутативный моноид с нулём. У него
есть единственный «Конец» (`0`, поглощающий), но «Начало» НЕ единственно
(нетривиальные единицы: элементы группы `ℤ/2` обратимы). Это показывает, что
единственность «Начала» и существование/единственность «Конца» независимы. -/

/-- Сокращение для примера независимости. -/
abbrev GZ : Type := WithZero (Multiplicative (ZMod 2))

/-
В `WithZero (Multiplicative ℤ/2)` «Конец» единственен и равен `0`.
-/
theorem gz_uniqueEnd : ∃! e : GZ, IsEnd e := by
  -- Exists: We show that `0` is a 'Yes' answer. Take any `x : GZ`. It suffices to show `algLe x 0`: there exists `c : GZ` with `x * c = 0`. Take `c = 0`, then `x * 0 = 0` (by `mul_zero`).
  use 0
  constructor
  · intro x
    use 0
    exact mul_zero x
  · intro e' h'end
    have := h'end 0 |>.choose_spec
    exact this ▸ zero_mul _

/-
В `WithZero (Multiplicative ℤ/2)` «Начало» существует, но НЕ единственно.
-/
theorem gz_not_uniqueBeginning : ¬ ∃! e : GZ, IsBeginning e := by
  rintro ⟨e, -, huniq⟩
  set a : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2) with ha
  set g : GZ := (a : GZ) with hg
  -- `g` — нетривиальная единица, `g * g = 1` (порядок 2)
  have hgg : g * g = 1 := by
    rw [hg, ← WithZero.coe_mul]
    norm_cast
  -- значит `g` тоже «Начало»: путь до `x` — это `g * x`
  have hgb : IsBeginning g := by
    intro x
    exact ⟨g * x, by rw [← mul_assoc, hgg, one_mul]⟩
  have h1 : (1 : GZ) = e := huniq 1 isBeginning_one
  have h2 : g = e := huniq g hgb
  have hcon : g = (1 : GZ) := h2.trans h1.symm
  rw [hg, show (1 : GZ) = ((1 : Multiplicative (ZMod 2)) : GZ) from (WithZero.coe_one).symm,
      WithZero.coe_inj] at hcon
  exact absurd hcon (by decide)

end Examples

/-! ## Часть 6. Классы структур с началом / концом / обоими -/

section Classes
variable (M : Type*)

/-- Структура «с началом»: выделенный элемент, являющийся «Началом». -/
class Beginning [Monoid M] where
  begin_ : M
  isBeginning_begin_ : IsBeginning begin_

/-- Структура «с концом»: выделенный элемент, являющийся «Концом». -/
class Ending [Monoid M] where
  end_ : M
  isEnd_end_ : IsEnd end_

/-- «Ограниченная» структура — процесс с точным стартом И финишем:
есть и «Начало», и «Конец». -/
class Bounded [Monoid M] where
  begin_ : M
  end_ : M
  isBeginning_begin_ : IsBeginning begin_
  isEnd_end_ : IsEnd end_

end Classes

/-- Любой моноид имеет «Начало» (это `1`). -/
instance instBeginningOfMonoid (M : Type*) [Monoid M] : Beginning M :=
  ⟨1, isBeginning_one⟩

/-- `(ℕ, ·)` имеет «Конец» (`0`). -/
instance : Ending ℕ := ⟨0, nat_mul_isEnd_zero⟩

/-- `(ℕ, ·)` — ограниченная структура: «Начало» `1`, «Конец» `0`. -/
instance : Bounded ℕ := ⟨1, 0, isBeginning_one, nat_mul_isEnd_zero⟩

/-! ## Часть 7. Три смысла «Конца» (существительное / глагол / прошедшее)

* **Существительное (точка):** сам элемент-конец — это `IsEnd e` (наибольший).
* **Глагол (действие):** для конца `e` и любого `x` есть «путь» `c`, ведущий в `e`
  (`x * c = e`). Функция `finishPath` выбирает такой путь.
* **Прошедшее (результат):** результат действия — это достигнутый элемент `e`
  (`finishPath_spec`: `x * finishPath = e`).

Ниже — соответствующие функции (и двойственные для «Начала»). -/

section Meanings
variable {M : Type*} [Monoid M]

/-- «Конец» как ГЛАГОЛ: выбор «пути» `c` с `x * c = e` для конца `e`. -/
noncomputable def finishPath {e : M} (he : IsEnd e) (x : M) : M := (he x).choose

/-- «Конец» как ПРОШЕДШЕЕ (результат): путь действительно приводит в `e`. -/
theorem finishPath_spec {e : M} (he : IsEnd e) (x : M) :
    x * finishPath he x = e := (he x).choose_spec

/-- «Начало» как ГЛАГОЛ: выбор «пути» `c` с `e * c = x` для начала `e`. -/
noncomputable def startPath {e : M} (he : IsBeginning e) (x : M) : M := (he x).choose

/-- «Начало» как ПРОШЕДШЕЕ (результат): путь ведёт из `e` в `x`. -/
theorem startPath_spec {e : M} (he : IsBeginning e) (x : M) :
    e * startPath he x = x := (he x).choose_spec

end Meanings

end UAM_End_ns