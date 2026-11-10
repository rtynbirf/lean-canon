import Mathlib

/-!
# UAM_Duality.lean — Двойственность (Duality)

Формализация двойственности между «правым» и «левым» мирами UAM через
противоположный моноид `Mᵒᵖ`.

Ключевая идея: `op : M → Mᵒᵖ` — анти-изоморфизм (`op (a * b) = op b * op a`),
поэтому каждое «правое» понятие (правая делимость, правая петля, правый конец…)
переходит в двойственное «левое» понятие для `op a` в `Mᵒᵖ`.

Файл самодостаточен: необходимые определения правого мира продублированы
(с пометкой `-- дублировано из UAM_...`). Всё в namespace `UAM`.
-/

open MulOpposite

namespace UAM_Duality_ns

variable {M : Type*} {G : Type*}

/-! ## §0. Дублированные определения правого мира -/

/-- Правый алгебраический порядок: `a ≤ b`, если существует `c` с `a * c = b`.
    (Свидетель стоит СПРАВА.) — дублировано из UAM_Path. -/
def algLe [Monoid M] (a b : M) : Prop := ∃ c : M, a * c = b

/-- Правое начало: из `e` достижим любой элемент правым умножением.
    — дублировано из UAM_Directionality. -/
def IsBeginning [Monoid M] (e : M) : Prop := ∀ x : M, algLe e x

/-- Правый конец: `e` — ПРАВЫЙ поглощающий элемент. — дублировано из UAM_End. -/
def IsEnd [Monoid M] (e : M) : Prop := ∀ x : M, x * e = e

/-- Правая петля: `a * c = a` с нетривиальным `c`. — дублировано из UAM_Loop. -/
def HasLoop [Monoid M] (a : M) : Prop := ∃ c : M, c ≠ 1 ∧ a * c = a

/-- Правая жёсткость: нет правых нетривиальных петель. — дублировано из UAM_Loop. -/
def IsRigid [Monoid M] (a : M) : Prop := ¬ HasLoop a

/-- Правый стабилизатор: все `c` такие, что `a * c = a`. — дублировано из UAM_Loop. -/
def rightStabilizer [Monoid M] (a : M) : Submonoid M where
  carrier := { c : M | a * c = a }
  one_mem' := by simp
  mul_mem' := by
    intro c d hc hd
    simp only [Set.mem_setOf_eq] at *
    rw [← mul_assoc, hc, hd]

/-! ## §1. Левый мир: определения и базовые свойства -/

/-- Левый алгебраический порядок: `a ≤ₗ b`, если существует `c` с `c * a = b`.
    (Свидетель стоит СЛЕВА, в отличие от `algLe`.) -/
def leftAlgLe [Monoid M] (a b : M) : Prop := ∃ c : M, c * a = b

/-- Левое начало: из `e` достижим любой элемент ЛЕВЫМ умножением. -/
def IsLeftBeginning [Monoid M] (e : M) : Prop := ∀ x : M, leftAlgLe e x

/-- Левый конец: `e` — ЛЕВЫЙ поглощающий элемент. -/
def IsLeftEnd [Monoid M] (e : M) : Prop := ∀ x : M, e * x = e

/-- Левая петля: `c * a = a` с нетривиальным `c`. -/
def HasLeftLoop [Monoid M] (a : M) : Prop := ∃ c : M, c ≠ 1 ∧ c * a = a

/-- Левая жёсткость: нет левых нетривиальных петель. -/
def IsLeftRigid [Monoid M] (a : M) : Prop := ¬ HasLeftLoop a

/-- Левый стабилизатор: все `c` такие, что `c * a = a`. -/
def leftStabilizer [Monoid M] (a : M) : Submonoid M where
  carrier := { c : M | c * a = a }
  one_mem' := by simp
  mul_mem' := by
    intro c d hc hd
    simp only [Set.mem_setOf_eq] at *
    rw [mul_assoc, hd, hc]

/-- Левый порядок рефлексивен. -/
theorem leftAlgLe_refl [Monoid M] (a : M) : leftAlgLe a a := ⟨1, one_mul a⟩

/-
`1` левожёсткий: `c * 1 = 1` влечёт `c = 1`.
-/
theorem one_is_leftRigid [Monoid M] : IsLeftRigid (1 : M) := by
  exact fun ⟨ c, hc, hc' ⟩ => hc ( by simpa using hc' )

/-
Левый конец порождает левую петлю (сам `e` — нетривиальный свидетель,
    если существует хоть один нетривиальный элемент).
-/
theorem leftEnd_has_loop [Monoid M] {e : M} (h : IsLeftEnd e) (c : M) (hc : c ≠ 1) :
    HasLeftLoop e := by
  -- Consider $c = e$. Since $e$ is a left end,
  have he_loop : e * e = e := by
    exact h e
  exact ⟨e, by
    exact ⟨ by rintro rfl; exact hc ( by simpa using h c ), he_loop ⟩⟩

/-
В моноиде с ПРАВЫМ сокращением все элементы левожёсткие.
    (Замечание: черновик промпта требовал `LeftCancelMonoid`, но левая петля
    `c * a = a` устраняется именно ПРАВЫМ сокращением элемента `a`
    (`c * a = 1 * a ⟹ c = 1`), поэтому правильная гипотеза — `RightCancelMonoid`.
    Это зеркально правому миру, где `IsRigid` держится в `LeftCancelMonoid`.)
-/
theorem rightCancelMonoid_isLeftRigid [RightCancelMonoid M] (a : M) : IsLeftRigid a := by
  rintro ⟨ c, hc, hc' ⟩;
  exact hc ( by simpa using mul_right_cancel ( by simp +decide [ hc' ] : c * a = 1 * a ) )

/-
В группе все элементы левожёсткие.
-/
theorem group_isLeftRigid [Group G] (a : G) : IsLeftRigid a := by
  exact fun ⟨ c, hc, hc' ⟩ => hc ( by simpa using congr_arg ( fun x => x * a⁻¹ ) hc' )

/-! ## §2. Противоположный моноид и основная теорема двойственности

`op : M → Mᵒᵖ` — анти-изоморфизм (`op (a * b) = op b * op a`). Поэтому правое
понятие для `a` переходит в ЛЕВОЕ понятие для `op a` в `Mᵒᵖ`.

**Замечание о формулировке `algLe`.** Исходный черновик промпта предлагал
`algLe a b ↔ leftAlgLe (op b) (op a)`, но это, если раскрыть определения,
равносильно `algLe b a` и в общем случае ЛОЖНО. Правильная (и совпадающая с
рассуждением-подсказкой из промпта) формулировка — `leftAlgLe (op a) (op b)`:
из `a * c = b` следует `op c * op a = op b`, т.е. свидетель `op c` стоит слева. -/

/-
Основная теорема двойственности: правый путь в `M` ↔ левый путь в `Mᵒᵖ`.
-/
theorem algLe_iff_leftAlgLe_op [Monoid M] (a b : M) :
    algLe a b ↔ leftAlgLe (op a) (op b) := by
  exact ⟨ fun ⟨ c, hc ⟩ => ⟨ op c, by simpa using congr_arg MulOpposite.op hc ⟩, fun ⟨ c, hc ⟩ => ⟨ MulOpposite.unop c, by simpa using congr_arg MulOpposite.unop hc ⟩ ⟩

/-
Правая петля в `M` ↔ левая петля в `Mᵒᵖ`.
-/
theorem hasLoop_iff_hasLeftLoop_op [Monoid M] (a : M) :
    HasLoop a ↔ HasLeftLoop (op a) := by
  constructor;
  · exact fun ⟨ c, hc, hc' ⟩ => ⟨ op c, by simpa using hc, by simpa using congr_arg MulOpposite.op hc' ⟩;
  · rintro ⟨ c, hc, hc' ⟩;
    refine' ⟨ MulOpposite.unop c, _, _ ⟩;
    · exact fun h => hc ( by simpa using congr_arg op h );
    · simpa using congr_arg MulOpposite.unop hc'

/-
Правая жёсткость в `M` ↔ левая жёсткость в `Mᵒᵖ`.
-/
theorem isRigid_iff_isLeftRigid_op [Monoid M] (a : M) :
    IsRigid a ↔ IsLeftRigid (op a) := by
  unfold IsRigid IsLeftRigid;
  simp +decide [ hasLoop_iff_hasLeftLoop_op ]

/-
Правое начало в `M` ↔ левое начало в `Mᵒᵖ`.
-/
theorem isBeginning_iff_isLeftBeginning_op [Monoid M] (e : M) :
    IsBeginning e ↔ IsLeftBeginning (op e) := by
  exact ⟨ fun h x => by obtain ⟨ c, hc ⟩ := h ( MulOpposite.unop x ) ; exact ⟨ op c, by simpa using congr_arg MulOpposite.op hc ⟩, fun h x => by obtain ⟨ c, hc ⟩ := h ( op x ) ; exact ⟨ MulOpposite.unop c, by simpa using congr_arg MulOpposite.unop hc ⟩ ⟩

/-
Правый конец в `M` ↔ левый конец в `Mᵒᵖ`.
-/
theorem isEnd_iff_isLeftEnd_op [Monoid M] (e : M) :
    IsEnd e ↔ IsLeftEnd (op e) := by
  simp +decide [ IsEnd, IsLeftEnd ];
  simp +decide [ ← op_mul ]

/-! ## §3. Перекрёстные двойственности (замечание)

Двойственность через `Mᵒᵖ` СОХРАНЯЕТ «сторону» и МЕНЯЕТ только направление
умножения:

* правое начало ↔ левое начало (`isBeginning_iff_isLeftBeginning_op`),
* правый конец ↔ левый конец (`isEnd_iff_isLeftEnd_op`).

«Перекрёстная» связь Beginning ↔ End через `Mᵒᵖ` НЕ работает.

`IsBeginning e` = `∀ x, ∃ c, e * c = x` — достижимость из `e` (∃-квантор).
`IsEnd (op e)` в `Mᵒᵖ` разворачивается в `∀ x, e * x = e` — левое поглощение
в `M` (∀-квантор). Это разные кванторные структуры, поэтому предполагаемые
теоремы `IsBeginning e → IsEnd (op e)` и `IsEnd e → IsBeginning (op e)` ЛОЖНЫ.

Контрпример к `IsBeginning e → IsEnd (op e)`: в моноиде `(ℤ, +)` (аддитивно,
единица `0`) элемент `e = 0` является началом (`∀ x, ∃ c, 0 + c = x`, взять
`c = x`), но `IsEnd (op 0)` требовало бы `∀ x, x + 0 = 0`, т.е. `∀ x, x = 0`,
что ложно. Поэтому здесь нет теоремы — только это замечание. -/

/-! ## §4. Самодвойственные свойства -/

/-- Элемент является И правым, И левым началом (двустороннее начало). -/
def IsTwoSidedBeginning [Monoid M] (e : M) : Prop :=
  IsBeginning e ∧ IsLeftBeginning e

/-- Элемент является И правым, И левым концом (двусторонний поглощающий). -/
def IsTwoSidedEnd [Monoid M] (e : M) : Prop :=
  IsEnd e ∧ IsLeftEnd e

/-- Элемент жёсткий с обеих сторон. -/
def IsTwoSidedRigid [Monoid M] (a : M) : Prop :=
  IsRigid a ∧ IsLeftRigid a

/-
В коммутативном моноиде правый и левый порядки совпадают.
-/
theorem commMonoid_algLe_iff_leftAlgLe [CommMonoid M] (a b : M) :
    algLe a b ↔ leftAlgLe a b := by
  constructor <;> intro h;
  · exact ⟨ h.choose, by rw [ mul_comm, h.choose_spec ] ⟩;
  · exact h.imp fun x hx => by rw [ mul_comm, hx ]

/-
В коммутативном моноиде правая и левая жёсткость совпадают.
-/
theorem commMonoid_isRigid_iff_isLeftRigid [CommMonoid M] (a : M) :
    IsRigid a ↔ IsLeftRigid a := by
  simp +decide only [IsRigid, HasLoop, IsLeftRigid, HasLeftLoop];
  simp +decide only [mul_comm]

/-
В коммутативном моноиде правый и левый конец совпадают.
-/
theorem commMonoid_isEnd_iff_isLeftEnd [CommMonoid M] (e : M) :
    IsEnd e ↔ IsLeftEnd e := by
  simp +decide only [IsEnd, IsLeftEnd, mul_comm e]

/-
В коммутативном моноиде правое и левое начало совпадают.
-/
theorem commMonoid_isBeginning_iff_isLeftBeginning [CommMonoid M] (e : M) :
    IsBeginning e ↔ IsLeftBeginning e := by
  constructor;
  · intro h x;
    exact h x |> fun ⟨ c, hc ⟩ => ⟨ c, by rw [ mul_comm, hc ] ⟩;
  · intro h x; obtain ⟨ c, hc ⟩ := h x; exact ⟨ c, by rw [ mul_comm, hc ] ⟩ ;

/-
В группе все элементы двусторонне жёсткие.
-/
theorem group_isTwoSidedRigid [Group G] (a : G) : IsTwoSidedRigid a := by
  constructor;
  · exact fun ⟨ c, hc, hc' ⟩ => hc ( by simpa using congr_arg ( fun x => x * a⁻¹ ) hc' );
  · exact group_isLeftRigid a

/-
`1` всегда двустороннее начало.
-/
theorem one_isTwoSidedBeginning [Monoid M] : IsTwoSidedBeginning (1 : M) := by
  constructor;
  · exact fun x => ⟨ x, one_mul x ⟩;
  · exact fun x => ⟨ x, mul_one x ⟩

/-! ## §5. Двусторонние концепции -/

/-- Двусторонняя петля: `∃ c ≠ 1`, И `a * c = a`, И `c * a = a`.
    Такой `c` — «локальная единица» для `a`. -/
def HasTwoSidedLoop [Monoid M] (a : M) : Prop :=
  ∃ c : M, c ≠ 1 ∧ a * c = a ∧ c * a = a

/-
Правая петля + левая петля с ОДНИМ И ТЕМ ЖЕ свидетелем = двусторонняя.
-/
theorem hasTwoSidedLoop_of_hasLoop_hasLeftLoop_same_witness [Monoid M] {a c : M}
    (hr : a * c = a) (hl : c * a = a) (hc : c ≠ 1) :
    HasTwoSidedLoop a := by
  exact ⟨ c, hc, hr, hl ⟩

/-
В коммутативном моноиде правая петля = двусторонняя петля.
-/
theorem commMonoid_hasLoop_iff_hasTwoSidedLoop [CommMonoid M] (a : M) :
    HasLoop a ↔ HasTwoSidedLoop a := by
  constructor <;> intro h;
  · exact ⟨ h.choose, h.choose_spec.1, h.choose_spec.2, by rw [ mul_comm, h.choose_spec.2 ] ⟩;
  · exact ⟨ h.choose, h.choose_spec.1, h.choose_spec.2.1 ⟩

/-! ## §6. Двойственная модель (conceptual)

Дана модель `Mod : Model α` с `evalMap : FreeMonoid α →* M`.
Двойственная модель имела бы носитель `Mᵒᵖ` и `evalMap : FreeMonoid α →* Mᵒᵖ`.

Проблема: `MulOpposite.op ∘ evalMap` — АНТИ-гомоморфизм (`op` обращает умножение).
Для получения гомоморфизма нужно также обратить свободный моноид
(`FreeMonoid.reverse`) и отождествить `(FreeMonoid α)ᵒᵖ` с `FreeMonoid α`.
Технические детали зависят от API Mathlib; здесь ограничиваемся замечанием.

## §7. Три смысла двойственности

1. **Отражение (Noun)**: `Mᵒᵖ` — зеркальный двойник `M`; каждому `a` отвечает
   `op a`, каждому правому свойству — двойственное левое.
2. **Перевод (Verb)**: каждая теорема о правых понятиях автоматически порождает
   двойственную теорему о левых — через `op` «бесплатно».
3. **Самодвойственность (Result)**: свойства, совпадающие со своими
   двойственными (коммутативность, группы, жёсткость), — самые фундаментальные:
   они не зависят от выбора направления чтения моноида.

Асимметрия Beginning vs End объясняется кванторной структурой (∃ против ∀),
а не выбором стороны умножения. -/

end UAM_Duality_ns