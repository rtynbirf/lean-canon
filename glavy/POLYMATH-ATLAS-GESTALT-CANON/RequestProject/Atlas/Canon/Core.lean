import Mathlib

/-!
# Канон Горизонтов — Правило Сдвига

## Комментарий-шов: карта соответствия текста и Lean

### Имена канонов

* Первый слой: «Толчок», «Чекан», «Нить», «Вязь», «Рок» — `Layer1`.
* Второй слой: «Шов», «Линия», «Вязь», «Рубеж», «Предел» —
  `layer2Names` и `Layer2`.
* Третий слой: «Нить памяти», «Вал вмещения», «Рубец», «Предел», «Чекан» —
  `layer3Names` и `Layer3`.
* Четвёртый слой: «Вал валов», «Рок рубежа», «Предел памяти»,
  «Чекан чекана чекана», «Нить, забывшая о забвении» —
  `layer4Names` и `Layer4`.
* Пятый слой сохраняет имена четвёртого — `Layer5`.
* Переходы между перечисленными именами — `NameTransform`.

### Свойства канона

* Размер и каноническая арность — `shift_preserves_size`,
  `five_has_canonical_arity`, `nonfive_lacks_canonical_arity`,
  `layer_above_five_lacks_canonical_arity`, `five_canon_shift_closed`.
* Рост, порядок и равномерность — `shift_increases_selfReferenceLevel`,
  `shift_monotone`, `shift_preserves_order`, `shift_preserves_uniform`.
* Структурная эквивалентность — `Layer.structurallyEquivalent_refl`,
  `Layer.structurallyEquivalent_symm`, `Layer.structurallyEquivalent_trans`.
* Структурная форма и четыре сдвига — `shift_structurally_equivalent`,
  `shift_iterate_structurally_equivalent`, `shift_four_structurally_cyclic`,
  `shift_iterate_fields`, `shift_four`, `shift_rule`.
* Переименование и числовая связь слоёв — `rename_preserves_numeric_fields`,
  `rename_numerically_equivalent`, `layer2_shift_equivalent`,
  `layer3_shift_equivalent`, `layer4_shift_equivalent`.
* Переходы и различие имён — `layer1_layer2_nameTransform`,
  `layer2_layer3_nameTransform`, `layer3_layer4_nameTransform`,
  `nameTransform_incomplete`, `adjacent_layer_names_differ`,
  `canonicalLayer_selfReferenceLevel`,
  `canonical_name_uniqueness_or_different_level`, `spiral_not_cycle`.

### Границы канона

* Самореференция не задаёт неподвижную точку — раздел
  «Самореференция и неподвижные точки» в `Canon/MetaObservations.lean`.
* Незамкнутость имён и повторяемость числового правила — раздел
  «Спираль имён и чисел» там же.
* Предел требует внешних типов `WithTop Nat` и `Option String` — раздел
  «Структура, предполагаемая спиралью» там же.
* Топология и сходимость не заданы каноном — раздел «Топология» там же.

Числа `5` и `4` зафиксированы как параметры канонического текста.
Размер семейства канонов параметризован, а каноническая арность выделена
отдельным свойством. Четыре сдвига сохраняют структурную форму слоя.
-/

/-- Канон — именованная операция с номером слоя и уровнем самовмещения. -/
structure Canon where
  name : String
  layer : Nat
  selfReferenceLevel : Nat
deriving Repr

/-- Слой размера `n` — семейство канонов с индексами `Fin n`. -/
structure Layer (n : Nat) where
  idx : Nat
  canons : Fin n → Canon
deriving Repr

/-- Число канонов в слое, зафиксированное каноническим текстом. -/
def canonicalArity : Nat := 5

/-- Число последовательных слоёв, зафиксированное каноническим текстом. -/
def canonicalShiftCount : Nat := 4

/-- Каноническая арность означает наличие ровно пяти позиций. -/
def Layer.HasCanonicalArity {n : Nat} (_L : Layer n) : Prop := n = canonicalArity

/-- Все каноны слоя имеют одинаковый уровень самовмещения. -/
def Layer.uniform {n : Nat} (L : Layer n) : Prop :=
  ∀ i j : Fin n,
    (L.canons i).selfReferenceLevel = (L.canons j).selfReferenceLevel

/-- Уровни самовмещения канонов строго возрастают вместе с индексами. -/
def Layer.StrictlyOrdered {n : Nat} (L : Layer n) : Prop :=
  ∀ ⦃i j : Fin n⦄, i < j →
    (L.canons i).selfReferenceLevel < (L.canons j).selfReferenceLevel

/-- Сдвиг добавляет единицу к номеру слоя, слою канона и уровню самовмещения. -/
def shift {n : Nat} (L : Layer n) : Layer n where
  idx := L.idx + 1
  canons := fun i =>
    let c := L.canons i
    { c with
      layer := c.layer + 1
      selfReferenceLevel := c.selfReferenceLevel + 1 }

/-- Сдвиг сохраняет число позиций параметризованного слоя. -/
theorem shift_preserves_size (n : Nat) : Fintype.card (Fin n) = n := by
  simp

/-- Уровень самовмещения каждого канона после сдвига увеличен на один. -/
theorem shift_increases_selfReferenceLevel {n : Nat} (L : Layer n) (i : Fin n) :
    ((shift L).canons i).selfReferenceLevel =
      (L.canons i).selfReferenceLevel + 1 := by
  rfl

/-- Строгий порядок уровней самовмещения сохраняется сдвигом. -/
theorem shift_preserves_order {n : Nat} (L : Layer n) (h : L.StrictlyOrdered) :
    (shift L).StrictlyOrdered := by
  intro i j hij
  rw [shift_increases_selfReferenceLevel, shift_increases_selfReferenceLevel]
  exact Nat.add_lt_add_right (h hij) 1

/-- Равенство уровней самовмещения внутри слоя сохраняется сдвигом. -/
theorem shift_preserves_uniform {n : Nat} (L : Layer n) (h : L.uniform) :
    (shift L).uniform := by
  intro i j
  rw [shift_increases_selfReferenceLevel, shift_increases_selfReferenceLevel, h i j]

/-- Уровень самовмещения строго возрастает при сдвиге. -/
theorem shift_monotone {n : Nat} (L : Layer n) (i : Fin n) :
    (L.canons i).selfReferenceLevel < ((shift L).canons i).selfReferenceLevel := by
  rw [shift_increases_selfReferenceLevel]
  omega

/-- Структурная эквивалентность игнорирует `idx`, `layer` и
`selfReferenceLevel`, сохраняя имена в соответствующих позициях. -/
def Layer.StructurallyEquivalent {n : Nat} (L K : Layer n) : Prop :=
  ∀ i : Fin n, (L.canons i).name = (K.canons i).name

instance Layer.structurallyEquivalentDecidable {n : Nat} (L K : Layer n) :
    Decidable (L.StructurallyEquivalent K) := by
  unfold Layer.StructurallyEquivalent
  infer_instance

/-- Структурная эквивалентность рефлексивна. -/
theorem Layer.structurallyEquivalent_refl {n : Nat} (L : Layer n) :
    L.StructurallyEquivalent L := by
  intro i
  rfl

/-- Структурная эквивалентность симметрична. -/
theorem Layer.structurallyEquivalent_symm {n : Nat} {L K : Layer n}
    (h : L.StructurallyEquivalent K) : K.StructurallyEquivalent L := by
  intro i
  exact (h i).symm

/-- Структурная эквивалентность транзитивна. -/
theorem Layer.structurallyEquivalent_trans {n : Nat} {L K M : Layer n}
    (h₁ : L.StructurallyEquivalent K) (h₂ : K.StructurallyEquivalent M) :
    L.StructurallyEquivalent M := by
  intro i
  exact (h₁ i).trans (h₂ i)

instance {n : Nat} : Setoid (Layer n) where
  r := Layer.StructurallyEquivalent
  iseqv := ⟨Layer.structurallyEquivalent_refl,
    Layer.structurallyEquivalent_symm, Layer.structurallyEquivalent_trans⟩

/-- Один сдвиг сохраняет структурную форму слоя. -/
theorem shift_structurally_equivalent {n : Nat} (L : Layer n) : shift L ≈ L := by
  intro i
  rfl

/-- Итерация сдвига сохраняет структурную форму слоя. -/
theorem shift_iterate_structurally_equivalent {n : Nat} (L : Layer n) (k : Nat) :
    (shift^[k]) L ≈ L := by
  induction k with
  | zero => exact Layer.structurallyEquivalent_refl L
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Layer.structurallyEquivalent_trans
        (shift_structurally_equivalent ((shift^[k]) L)) ih

/-- Четыре сдвига сохраняют структурную форму исходного слоя. -/
theorem shift_four_structurally_cyclic {n : Nat} (L : Layer n) :
    (shift^[canonicalShiftCount]) L ≈ L := by
  exact shift_iterate_structurally_equivalent L canonicalShiftCount

/-- После `k` сдвигов числовые поля увеличены на `k`, а имя сохранено. -/
theorem shift_iterate_fields {n : Nat} (L : Layer n) (k : Nat) :
    ((shift^[k]) L).idx = L.idx + k ∧
    ∀ i : Fin n,
      (((shift^[k]) L).canons i).name = (L.canons i).name ∧
      (((shift^[k]) L).canons i).layer = (L.canons i).layer + k ∧
      (((shift^[k]) L).canons i).selfReferenceLevel =
        (L.canons i).selfReferenceLevel + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with ⟨hidx, hfields⟩
      constructor
      · simp [shift, hidx, Nat.add_assoc]
      · intro i
        specialize hfields i
        simp only [shift]
        simp [hfields.1, hfields.2.1, hfields.2.2, Nat.add_assoc]

/-- Закон четырёх сдвигов сохраняет имена и добавляет четыре к счётчикам. -/
def FourShiftLaw {n : Nat} (L : Layer n) : Prop :=
  let L4 := (shift^[canonicalShiftCount]) L
  L4.idx = L.idx + canonicalShiftCount ∧
    ∀ i : Fin n,
      (L4.canons i).name = (L.canons i).name ∧
      (L4.canons i).layer = (L.canons i).layer + canonicalShiftCount ∧
      (L4.canons i).selfReferenceLevel =
        (L.canons i).selfReferenceLevel + canonicalShiftCount

/-- Четыре последовательных сдвига удовлетворяют `FourShiftLaw`. -/
theorem shift_four {n : Nat} (L : Layer n) : FourShiftLaw L := by
  exact shift_iterate_fields L canonicalShiftCount

/-- Правило сдвига объединяет сохранение равномерности, рост уровней,
структурный возврат и закон четырёх сдвигов. -/
theorem shift_rule {n : Nat} (L : Layer n) (h : L.uniform) :
    (shift L).uniform ∧
    (∀ i, ((shift L).canons i).selfReferenceLevel =
      (L.canons i).selfReferenceLevel + 1) ∧
    (shift^[canonicalShiftCount]) L ≈ L ∧ FourShiftLaw L := by
  exact ⟨shift_preserves_uniform L h, shift_increases_selfReferenceLevel L,
    shift_four_structurally_cyclic L, shift_four L⟩

/-- Слой размера пять имеет каноническую арность. -/
theorem five_has_canonical_arity (L : Layer 5) : L.HasCanonicalArity := by
  rfl

/-- При параметре, отличном от пяти, свойство канонической арности не выполняется. -/
theorem nonfive_lacks_canonical_arity {n : Nat} (hn : n ≠ 5) (L : Layer n) :
    ¬ L.HasCanonicalArity := by
  simpa [Layer.HasCanonicalArity, canonicalArity] using hn

/-- Утверждение для каждого размера больше пяти: слой не имеет канонической
арности. -/
theorem layer_above_five_lacks_canonical_arity :
    ∀ n, n > 5 → ∀ L : Layer n, ¬ L.HasCanonicalArity := by
  intro n hn L
  exact nonfive_lacks_canonical_arity (Nat.ne_of_gt hn) L

/-- Для пяти позиций сохраняются каноническая арность и все свойства правила
сдвига. -/
theorem five_canon_shift_closed (L : Layer 5) (h : L.uniform) :
    L.HasCanonicalArity ∧ (shift L).HasCanonicalArity ∧
    (shift L).uniform ∧
    (∀ i, ((shift L).canons i).selfReferenceLevel =
      (L.canons i).selfReferenceLevel + 1) ∧
    (shift^[canonicalShiftCount]) L ≈ L ∧ FourShiftLaw L := by
  exact ⟨five_has_canonical_arity L, five_has_canonical_arity (shift L),
    shift_preserves_uniform L h, shift_increases_selfReferenceLevel L,
    shift_four_structurally_cyclic L, shift_four L⟩

/-- Пример первого слоя с пятью канонами. -/
def Layer1 : Layer 5 where
  idx := 1
  canons := fun i =>
    match i with
    | 0 => { name := "Толчок", layer := 1, selfReferenceLevel := 0 }
    | 1 => { name := "Чекан", layer := 1, selfReferenceLevel := 0 }
    | 2 => { name := "Нить", layer := 1, selfReferenceLevel := 0 }
    | 3 => { name := "Вязь", layer := 1, selfReferenceLevel := 0 }
    | 4 => { name := "Рок", layer := 1, selfReferenceLevel := 0 }

/-- Переименование заменяет имена канонов и сохраняет все числовые поля слоя. -/
def rename {n : Nat} (L : Layer n) (names : Fin n → String) : Layer n where
  idx := L.idx
  canons := fun i => { L.canons i with name := names i }

/-- Канонические имена второго слоя. -/
def layer2Names : Fin 5 → String
  | 0 => "Шов"
  | 1 => "Линия"
  | 2 => "Вязь"
  | 3 => "Рубеж"
  | 4 => "Предел"

/-- Второй слой: числовой сдвиг первого слоя с каноническими именами. -/
def Layer2 : Layer 5 := rename (shift Layer1) layer2Names

/-- Канонические имена третьего слоя. -/
def layer3Names : Fin 5 → String
  | 0 => "Нить памяти"
  | 1 => "Вал вмещения"
  | 2 => "Рубец"
  | 3 => "Предел"
  | 4 => "Чекан"

/-- Третий слой: числовой сдвиг второго слоя с каноническими именами. -/
def Layer3 : Layer 5 := rename (shift Layer2) layer3Names

/-- Канонические имена четвёртого слоя. -/
def layer4Names : Fin 5 → String
  | 0 => "Вал валов"
  | 1 => "Рок рубежа"
  | 2 => "Предел памяти"
  | 3 => "Чекан чекана чекана"
  | 4 => "Нить, забывшая о забвении"

/-- Четвёртый слой: числовой сдвиг третьего слоя с каноническими именами. -/
def Layer4 : Layer 5 := rename (shift Layer3) layer4Names

/-- Пятый слой получается сдвигом четвёртого без переименования. -/
def Layer5 : Layer 5 := shift Layer4

/-- Отношение перехода имён между соседними каноническими слоями. -/
def NameTransform (s t : String) : Prop :=
  (s = "Толчок" ∧ t = "Шов") ∨
  (s = "Чекан" ∧ t = "Линия") ∨
  (s = "Нить" ∧ t = "Вязь") ∨
  (s = "Вязь" ∧ t = "Рубеж") ∨
  (s = "Рок" ∧ t = "Предел") ∨
  (s = "Шов" ∧ t = "Нить памяти") ∨
  (s = "Линия" ∧ t = "Вал вмещения") ∨
  (s = "Вязь" ∧ t = "Рубец") ∨
  (s = "Рубеж" ∧ t = "Предел") ∨
  (s = "Предел" ∧ t = "Чекан") ∨
  (s = "Нить памяти" ∧ t = "Вал валов") ∨
  (s = "Вал вмещения" ∧ t = "Рок рубежа") ∨
  (s = "Рубец" ∧ t = "Предел памяти") ∨
  (s = "Предел" ∧ t = "Чекан чекана чекана") ∨
  (s = "Чекан" ∧ t = "Нить, забывшая о забвении")

instance nameTransformDecidable (s t : String) : Decidable (NameTransform s t) := by
  unfold NameTransform
  infer_instance

/-- Переименование сохраняет номер слоя и числовые поля канонов. -/
theorem rename_preserves_numeric_fields {n : Nat} (L : Layer n)
    (names : Fin n → String) :
    (rename L names).idx = L.idx ∧
      ∀ i, ((rename L names).canons i).layer = (L.canons i).layer ∧
        ((rename L names).canons i).selfReferenceLevel =
          (L.canons i).selfReferenceLevel := by
  simp [rename]

/-- Числовая эквивалентность слоёв игнорирует имена и сравнивает номер слоя,
номер каждого канона и уровень самовмещения. Она используется для точной связи
именованных слоёв со сдвигом, поскольку прежняя `StructurallyEquivalent`
по определению сравнивает именно имена. -/
def Layer.NumericallyEquivalent {n : Nat} (L K : Layer n) : Prop :=
  L.idx = K.idx ∧ ∀ i, (L.canons i).layer = (K.canons i).layer ∧
    (L.canons i).selfReferenceLevel = (K.canons i).selfReferenceLevel

instance Layer.numericallyEquivalentDecidable {n : Nat} (L K : Layer n) :
    Decidable (L.NumericallyEquivalent K) := by
  unfold Layer.NumericallyEquivalent
  infer_instance

/-- Любое переименование численно эквивалентно исходному слою. -/
theorem rename_numerically_equivalent {n : Nat} (L : Layer n)
    (names : Fin n → String) :
    (rename L names).NumericallyEquivalent L := by
  exact rename_preserves_numeric_fields L names

/-- Второй слой численно эквивалентен сдвигу первого. -/
theorem layer2_shift_equivalent :
    Layer2.NumericallyEquivalent (shift Layer1) := by
  exact rename_numerically_equivalent (shift Layer1) layer2Names

/-- Третий слой численно эквивалентен сдвигу второго. -/
theorem layer3_shift_equivalent :
    Layer3.NumericallyEquivalent (shift Layer2) := by
  exact rename_numerically_equivalent (shift Layer2) layer3Names

/-- Четвёртый слой численно эквивалентен сдвигу третьего. -/
theorem layer4_shift_equivalent :
    Layer4.NumericallyEquivalent (shift Layer3) := by
  exact rename_numerically_equivalent (shift Layer3) layer4Names

/-- Имена первого и второго слоёв связаны отношением перехода. -/
theorem layer1_layer2_nameTransform :
    ∀ i, NameTransform (Layer1.canons i).name (Layer2.canons i).name := by
  intro i
  fin_cases i <;> simp [NameTransform, Layer1, Layer2, rename, layer2Names, shift]

/-- Имена второго и третьего слоёв связаны отношением перехода. -/
theorem layer2_layer3_nameTransform :
    ∀ i, NameTransform (Layer2.canons i).name (Layer3.canons i).name := by
  intro i
  fin_cases i <;>
    simp [NameTransform, Layer1, Layer2, Layer3, rename, layer2Names, layer3Names, shift]

/-- Имена третьего и четвёртого слоёв связаны отношением перехода. -/
theorem layer3_layer4_nameTransform :
    ∀ i, NameTransform (Layer3.canons i).name (Layer4.canons i).name := by
  intro i
  fin_cases i <;>
    simp [NameTransform, Layer1, Layer2, Layer3, Layer4, rename, layer2Names,
      layer3Names, layer4Names, shift]

/-- Утверждение о неполноте отношения: существуют строки, не связанные
`NameTransform`. -/
theorem nameTransform_incomplete : ∃ s t : String, ¬ NameTransform s t := by
  exact ⟨"", "", by simp [NameTransform]⟩

/-- Соответствующие имена соседних канонических слоёв различны. -/
theorem adjacent_layer_names_differ :
    (∀ i, (Layer1.canons i).name ≠ (Layer2.canons i).name) ∧
    (∀ i, (Layer2.canons i).name ≠ (Layer3.canons i).name) ∧
    (∀ i, (Layer3.canons i).name ≠ (Layer4.canons i).name) := by
  constructor
  · intro i
    fin_cases i <;> simp [Layer1, Layer2, rename, layer2Names, shift]
  constructor
  · intro i
    fin_cases i <;>
      simp [Layer1, Layer2, Layer3, rename, layer2Names, layer3Names, shift]
  · intro i
    fin_cases i <;>
      simp [Layer1, Layer2, Layer3, Layer4, rename, layer2Names, layer3Names,
        layer4Names, shift]

/-- Вычисляемое семейство четырёх канонических слоёв. -/
def canonicalLayer : Fin 4 → Layer 5
  | 0 => Layer1
  | 1 => Layer2
  | 2 => Layer3
  | 3 => Layer4

/-- Уровень самовмещения позиции канонического слоя равен номеру слоя
в семействе, отсчитываемому от нуля. -/
theorem canonicalLayer_selfReferenceLevel (N : Fin 4) (i : Fin 5) :
    ((canonicalLayer N).canons i).selfReferenceLevel = N.val := by
  fin_cases N <;> fin_cases i <;>
    simp [canonicalLayer, Layer1, Layer2, Layer3, Layer4, rename, layer2Names,
      layer3Names, layer4Names, shift]

/-- Совпадение имён в четырёх канонических слоях либо определяет одну и ту же
позицию одного слоя, либо происходит в разных слоях с разными уровнями
самовмещения. -/
theorem canonical_name_uniqueness_or_different_level :
    ∀ N M : Fin 4, ∀ i j : Fin 5,
      ((canonicalLayer N).canons i).name = ((canonicalLayer M).canons j).name →
        (N = M ∧ i = j) ∨
        (N ≠ M ∧ ((canonicalLayer N).canons i).name =
          ((canonicalLayer M).canons j).name ∧
          ((canonicalLayer N).canons i).selfReferenceLevel ≠
            ((canonicalLayer M).canons j).selfReferenceLevel) := by
  intro N M i j h
  by_cases hNM : N = M
  · left
    subst M
    refine ⟨rfl, ?_⟩
    fin_cases N <;> fin_cases i <;> fin_cases j <;>
      simp [canonicalLayer, Layer1, Layer2, Layer3, Layer4, rename, layer2Names,
        layer3Names, layer4Names, shift] at h ⊢
  · right
    refine ⟨hNM, h, ?_⟩
    rw [canonicalLayer_selfReferenceLevel, canonicalLayer_selfReferenceLevel]
    intro hval
    apply hNM
    exact Fin.ext hval

/-- Пятый слой отличается от первого именами, но его числовые поля совпадают
с результатом четырёх сдвигов первого слоя. -/
theorem spiral_not_cycle :
    ¬ Layer5.StructurallyEquivalent Layer1 ∧
      ((shift^[canonicalShiftCount]) Layer1).NumericallyEquivalent (shift Layer4) := by
  constructor
  · intro h
    have h0 := h (0 : Fin 5)
    simp [Layer5, Layer4, Layer3, Layer2, Layer1, rename, layer4Names,
      layer3Names, layer2Names, shift] at h0
  · simp [Layer.NumericallyEquivalent, canonicalShiftCount, Layer4,
      Layer3, Layer2, Layer1, rename, layer4Names, layer3Names, layer2Names,
      shift, Function.iterate_succ_apply']

/-- Канон во внешнем расширении. Числовые поля принимают значения в
`WithTop Nat`, а отсутствие имени выражается через `Option`. -/
structure LimitCanon where
  name : Option String
  layer : WithTop Nat
  selfReferenceLevel : WithTop Nat

/-- Внешнее расширение слоя, допускающее значение `⊤`. -/
structure LimitLayer (n : Nat) where
  idx : WithTop Nat
  canons : Fin n → LimitCanon

/-- Структура, предполагаемая спиралью: числовые поля равны `⊤`, а имена
не заданы. Она не является пределом в каноне. -/
def spiralLimit (n : Nat) : LimitLayer n where
  idx := ⊤
  canons := fun _ =>
    { name := none, layer := ⊤, selfReferenceLevel := ⊤ }
