import Mathlib

/-!
# UAM_Loop.lean — Петля (Loop)

Это самодостаточный файл в рамках проекта **UAM (Universal Algebra of Models)**.
Он формализует понятие *петли* (loop) — нетривиального пути от элемента к самому себе.

Тетрада UAM:

```
Источник (Beginning)  →  Путь (Path)  →  Сток (End)  →  Цикл (Loop)
    algLe e x              algLe a b        algLe x e       algLe a a (c ≠ 1)
```

Поскольку предыдущие файлы UAM недоступны для импорта в этой сборке, необходимые
определения (`algLe`, `IsBeginning`, `IsEnd`) продублированы ниже с пометкой
`-- duplicated from UAM_...`.

Все результаты собраны в пространстве имён `UAM`, чтобы избежать коллизий с Mathlib.
-/

namespace UAM_Loop_ns

variable {M : Type*}

/-! ## §0. Продублированные определения UAM

`algLe a b := ∃ c, a * c = b` — алгебраический (правый делимостный) порядок.
Свидетель `c` называется «путём» от `a` к `b`. -/

/-- Алгебраический порядок: `a ≤ b`, если существует путь (свидетель) `c` с `a * c = b`.
    -- duplicated from UAM_Path / UAM_Directionality -/
def algLe [Monoid M] (a b : M) : Prop := ∃ c : M, a * c = b

/-- `e` — Начало (Beginning): из него достижим любой элемент, `algLe e x` для всех `x`.
    -- duplicated from UAM_Directionality -/
def IsBeginning [Monoid M] (e : M) : Prop := ∀ x : M, algLe e x

/-- `e` — Конец (End): правый поглощающий элемент, `x * e = e` для всех `x`
    (правый ноль). Тогда `algLe x e` для всех `x` — конец является стоком.
    -- duplicated from UAM_End -/
def IsEnd [Monoid M] (e : M) : Prop := ∀ x : M, x * e = e

/-! ## §1. Определения: Петля, Жёсткость, Стабилизатор -/

/-- У элемента `a` есть нетривиальная петля: существует `c ≠ 1` с `a * c = a`. -/
def HasLoop [Monoid M] (a : M) : Prop :=
  ∃ c : M, c ≠ 1 ∧ a * c = a

/-- Элемент `a` жёсткий (rigid): у него нет нетривиальных петель. -/
def IsRigid [Monoid M] (a : M) : Prop :=
  ¬ HasLoop a

/-- Правый стабилизатор элемента `a`: все `c` такие, что `a * c = a`.
    Это подмоноид — содержит `1` и замкнут относительно умножения. -/
def rightStabilizer [Monoid M] (a : M) : Submonoid M where
  carrier := { c : M | a * c = a }
  one_mem' := by simp
  mul_mem' := by
    intro c d hc hd
    show a * (c * d) = a
    rw [← mul_assoc, hc, hd]

/-! ### Базовые связи -/

/-- `algLe a a` всегда выполняется (свидетель `= 1`). Рефлексивность алгебраического порядка. -/
theorem algLe_refl [Monoid M] (a : M) : algLe a a := ⟨1, mul_one a⟩

/-- Наличие петли ⟺ стабилизатор нетривиален (содержит не только `1`). -/
theorem hasLoop_iff_stabilizer_ne_bot [Monoid M] (a : M) :
    HasLoop a ↔ rightStabilizer a ≠ ⊥ := by
  constructor
  · rintro ⟨c, hc1, hc⟩ hbot
    rw [Submonoid.eq_bot_iff_forall] at hbot
    exact hc1 (hbot c hc)
  · intro hne
    rw [ne_eq, Submonoid.eq_bot_iff_forall] at hne
    push_neg at hne
    obtain ⟨c, hc, hc1⟩ := hne
    exact ⟨c, hc1, hc⟩

/-- Жёсткость ⟺ стабилизатор тривиален (равен `{1} = ⊥`). -/
theorem isRigid_iff_stabilizer_eq_bot [Monoid M] (a : M) :
    IsRigid a ↔ rightStabilizer a = ⊥ := by
  rw [IsRigid, hasLoop_iff_stabilizer_ne_bot, not_not]

/-- Наличие петли ⟺ у пути `a → a` есть два РАЗНЫХ свидетеля.

    (Исправление формулировки из плана: исходное `∃ c ≠ 1, algLe a a ∧ c ≠ 1`
    ничего не говорило об `a`, так как `algLe a a` истинно всегда. Точный смысл
    петли — *неединственность* пути `a → a`.) -/
theorem hasLoop_iff_nontrivial_self_path [Monoid M] (a : M) :
    HasLoop a ↔ ∃ c d : M, c ≠ d ∧ a * c = a ∧ a * d = a := by
  constructor
  · rintro ⟨c, hc1, hc⟩
    exact ⟨c, 1, hc1, hc, mul_one a⟩
  · rintro ⟨c, d, hne, hc, hd⟩
    by_cases hc1 : c = 1
    · refine ⟨d, ?_, hd⟩
      intro hd1
      exact hne (by rw [hc1, hd1])
    · exact ⟨c, hc1, hc⟩

/-! ## §2. Начало жёсткое, Конец — нет -/

/-- Начало (`= 1`) всегда жёсткое: `1 * c = 1` влечёт `c = 1`. -/
theorem one_is_rigid [Monoid M] : IsRigid (1 : M) := by
  rintro ⟨c, hc1, hc⟩
  rw [one_mul] at hc
  exact hc1 hc

/-- Единица является Началом: `algLe 1 x` для всех `x` (свидетель `x`). -/
theorem one_isBeginning [Monoid M] : IsBeginning (1 : M) :=
  fun x => ⟨x, one_mul x⟩

/-- Конец (правый поглощающий элемент) имеет петлю: так как `e * e = e`
    (частный случай `x * e = e` при `x = e`), достаточно `e ≠ 1`.
    Данная `c ≠ 1` служит свидетелем нетривиальности моноида, из чего следует `e ≠ 1`. -/
theorem end_has_all_loops [Monoid M] {e : M} (h : IsEnd e) (c : M) (hc : c ≠ 1) :
    HasLoop e := by
  have he : e ≠ 1 := by
    rintro rfl
    exact hc (by have := h c; simpa using this)
  exact ⟨e, he, h e⟩

/-- Если моноид нетривиален (есть элемент `≠ 1`), то Конец имеет нетривиальную петлю. -/
theorem end_has_loop_of_nontrivial [Monoid M] {e : M} (h : IsEnd e)
    (h_exists : ∃ x : M, x ≠ 1) : HasLoop e := by
  obtain ⟨x, hx⟩ := h_exists
  exact end_has_all_loops h x hx

/-! ## §3. Группы и лево-сократимые моноиды жёсткие -/

/-- В группе все элементы жёсткие: `a * c = a` влечёт `c = 1`. -/
theorem Group.isRigid {G : Type*} [Group G] (a : G) : IsRigid a := by
  rintro ⟨c, hc1, hc⟩
  exact hc1 (mul_left_cancel (hc.trans (mul_one a).symm))

/-- В лево-сократимом моноиде все элементы жёсткие. -/
theorem LeftCancelMonoid.isRigid [LeftCancelMonoid M] (a : M) : IsRigid a := by
  rintro ⟨c, hc1, hc⟩
  exact hc1 (mul_left_cancel (hc.trans (mul_one a).symm))

/-- В свободном моноиде все элементы жёсткие (частный случай лево-сократимости). -/
theorem FreeMonoid.isRigid (α : Type*) (w : FreeMonoid α) : IsRigid w :=
  LeftCancelMonoid.isRigid w

/-- Аналог жёсткости для `List α` (у которого нет инстанса `Monoid`, но есть `++`):
    `l ++ c = l` влечёт `c = []`. Единственная петля списка тривиальна. -/
theorem list_isRigid {α : Type*} (l c : List α) (h : l ++ c = l) : c = [] :=
  List.append_right_eq_self.mp h

/-! ## §4. Конкретные примеры с петлями

В мультипликативном моноиде `ℕ` (стандартный инстанс `Monoid ℕ` — это умножение)
элемент `0` поглощающий: `0 * c = 0`. Поэтому `0` имеет нетривиальную петлю. -/

/-- В `(ℕ, *, 1)` элемент `0` имеет нетривиальную петлю: `0 * 0 = 0` и `0 ≠ 1`. -/
theorem nat_zero_hasLoop : HasLoop (0 : ℕ) :=
  ⟨0, by decide, by decide⟩

/-- В `(ℕ, *, 1)` любой ненулевой элемент жёсткий: `a * c = a` при `a ≠ 0` влечёт `c = 1`. -/
theorem nat_isRigid_of_ne_zero {a : ℕ} (ha : a ≠ 0) : IsRigid a := by
  rintro ⟨c, hc1, hc⟩
  exact hc1 (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) (hc.trans (mul_one a).symm))

/-! ## §5. Структура стабилизатора -/

namespace rightStabilizer

variable [Monoid M] (a : M)

/-- Стабилизатор содержит `1`. -/
theorem one_mem : (1 : M) ∈ rightStabilizer a := (rightStabilizer a).one_mem

variable {a}

/-- Стабилизатор замкнут относительно умножения. -/
theorem mul_mem {c d : M} (hc : c ∈ rightStabilizer a) (hd : d ∈ rightStabilizer a) :
    d * c ∈ rightStabilizer a := (rightStabilizer a).mul_mem hd hc

/-- Если `b ∈ rightStabilizer a`, то `a * b = a`. -/
theorem mul_eq_of_mem {b : M} (hb : b ∈ rightStabilizer a) : a * b = a := hb

/-- Все степени свидетеля петли тоже свидетели: если `a * c = a`, то `a * c ^ n = a`. -/
theorem pow_mem {c : M} (hc : c ∈ rightStabilizer a) (n : ℕ) :
    c ^ n ∈ rightStabilizer a := (rightStabilizer a).pow_mem hc n

/- Замечание. Формулировка из плана «`a * c ∈ rightStabilizer a` при `c ∈ stab`»
   в общем случае ЛОЖНА: из `c ∈ stab` следует `a * c = a`, поэтому утверждение
   свелось бы к `a ∈ stab a`, т.е. `a * a = a` (идемпотентность), что верно не для
   всех `a`. Поэтому эта лемма опущена. -/

end rightStabilizer

/-! ## §6. Петля и антисимметричность `algLe`

Алгебраический порядок `algLe` в общем случае — только предпорядок (рефлексивен
и транзитивен). Вопрос о его антисимметричности тонок. -/

/-- Если `algLe a b` и `algLe b a` со свидетелями `c, d`, то `c * d` — свидетель
    петли в `a`: `a * (c * d) = a`. -/
theorem algLe_loop_witness [Monoid M] {a b : M}
    (h1 : algLe a b) (h2 : algLe b a) :
    ∃ c d : M, a * c = b ∧ b * d = a ∧ a * (c * d) = a := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  exact ⟨c, d, hc, hd, by rw [← mul_assoc, hc, hd]⟩

/-- Если все элементы жёсткие И единственный элемент с правым обратным — это `1`
    (`c * d = 1 → c = 1`, т.е. нет нетривиальных единиц), то `algLe` антисимметричен.

    (Уточнение к плану: одной жёсткости НЕДОСТАТОЧНО — в группе все элементы жёсткие,
    но `algLe` там тотален и не антисимметричен. Нужна также тривиальность единиц.) -/
theorem algLe_antisymm_of_rigid [Monoid M]
    (h_rigid : ∀ a : M, IsRigid a)
    (h_units : ∀ c d : M, c * d = 1 → c = 1)
    {a b : M} (h1 : algLe a b) (h2 : algLe b a) : a = b := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  have hloop : a * (c * d) = a := by rw [← mul_assoc, hc, hd]
  have hcd1 : c * d = 1 := by
    by_contra hne
    exact h_rigid a ⟨c * d, hne, hloop⟩
  have hc1 : c = 1 := h_units c d hcd1
  rw [hc1, mul_one] at hc
  exact hc

/- Замечание. Обратное утверждение из плана — «`algLe` антисимметричен ⟹ все элементы
   жёсткие» — ЛОЖНО. Контрпример: мультипликативный моноид `({0, 1}, *)` (например `ℕ`,
   ограниченный до `0, 1`, или `Bool` с `∧`). Элемент `0` не жёсткий (`0 * 0 = 0`,
   `0 ≠ 1`), однако `algLe` антисимметричен: единственные пары `a, b` с `algLe a b`
   и `algLe b a` — это `a = b`. Поэтому доказываем только прямое направление. -/

/-! ## §7. Петли и морфизмы

Строгие морфизмы моделей UAM недоступны для импорта, но их ключевое свойство
формализуется напрямую через `MonoidHom`. -/

/-- Инъективный гомоморфизм моноидов сохраняет петли: если `a` имеет петлю,
    то и `f a` имеет петлю. -/
theorem hasLoop_map_of_injective [Monoid M] {N : Type*} [Monoid N]
    (f : M →* N) (hf : Function.Injective f) {a : M} (h : HasLoop a) :
    HasLoop (f a) := by
  obtain ⟨c, hc1, hc⟩ := h
  refine ⟨f c, ?_, ?_⟩
  · intro hfc
    exact hc1 (hf (by rw [hfc, map_one]))
  · rw [← map_mul, hc]

/-- Инъективный гомоморфизм отражает жёсткость: если `f a` жёсткий, то и `a` жёсткий. -/
theorem isRigid_of_injective [Monoid M] {N : Type*} [Monoid N]
    (f : M →* N) (hf : Function.Injective f) {a : M} (h : IsRigid (f a)) :
    IsRigid a :=
  fun hl => h (hasLoop_map_of_injective f hf hl)

/-! ## §8. Три смысла петли (Noun — Verb — Result)

Петля в UAM, как и каждое фундаментальное понятие, существует в трёх смыслах:

1. **Существование (Noun)**: `HasLoop a` — факт наличия нетривиального пути `a → a`.
   Это свойство ЭЛЕМЕНТА, а не всего моноида: в `(ℕ, *)` элемент `0` не жёсткий
   (`nat_zero_hasLoop`), а все ненулевые — жёсткие (`nat_isRigid_of_ne_zero`).

2. **Стабилизатор (Verb/Action)**: `rightStabilizer a` — подмоноид всех «петельных»
   свидетелей. Это АЛГЕБРАИЧЕСКАЯ СТРУКТУРА: подмоноид с `1`, замкнутый относительно
   умножения (`rightStabilizer.mul_mem`) и степеней (`rightStabilizer.pow_mem`).

3. **Жёсткость (Result)**: `IsRigid a` — отсутствие петель, «нормальная форма»
   элемента, для которого путь к себе ЕДИНСТВЕНЕН (свидетель `= 1`).

Связь с предыдущими концепциями:
* `IsBeginning`/`1` → `one_is_rigid` (начало жёсткое);
* `IsEnd e` → `end_has_loop_of_nontrivial` (конец имеет петлю);
* `LeftCancelMonoid`, `Group`, `FreeMonoid` → все элементы жёсткие;
* `algLe` антисимметричен ⟸ жёсткость + тривиальность единиц (`algLe_antisymm_of_rigid`).
-/

end UAM_Loop_ns
