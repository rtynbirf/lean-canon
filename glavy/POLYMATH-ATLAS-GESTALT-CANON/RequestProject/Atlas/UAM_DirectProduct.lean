import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_Morphism         -- MonoidMorphism (и транзитивно IsUnit', IsRegular, IsZero)

/-!
# UAM — Layer 8: Прямое произведение (DirectProduct)

Прямое произведение двух моноидов `M × N` с поточечным умножением. Проекции —
морфизмы моноидов, диагональное вложение — морфизм, пара морфизмов порождает
морфизм в произведение (универсальное свойство произведения).
-/

namespace UAM_DirectProduct
universe u

open UAM_Idempotent UAM_Group UAM_Regular UAM_Morphism

variable {M N P : Type u} [Monoid M] [Monoid N] [Monoid P]

/-- Прямое произведение моноидов (встроенный `Prod` с поточечным умножением). -/
abbrev DirectProduct (M N : Type u) [Monoid M] [Monoid N] := M × N

/-! ### §1. Инстанс моноида и базовые свойства -/

/-- Единица произведения — пара единиц. -/
theorem prod_one_eq : ((1 : M), (1 : N)) = (1 : M × N) := rfl

/-- Поточечное умножение пар. -/
theorem prod_mul_eq (a c : M) (b d : N) : (a, b) * (c, d) = (a * c, b * d) := rfl

/-- Первая компонента произведения. -/
theorem prod_fst_mul (a b : M) (c d : N) : ((a * b, c * d) : M × N).1 = a * b := rfl

/-! ### §2. Проекции -/

/-- Первая проекция `M × N → M` — морфизм моноидов. -/
def fstMorphism : MonoidMorphism (M × N) M where
  toFun := Prod.fst
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- Вторая проекция `M × N → N` — морфизм моноидов. -/
def sndMorphism : MonoidMorphism (M × N) N where
  toFun := Prod.snd
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- Первая проекция сюръективна. -/
theorem fst_surjective : Function.Surjective (fstMorphism : MonoidMorphism (M × N) M).toFun :=
  fun a => ⟨(a, 1), rfl⟩

/-! ### §3. Диагональ и пары -/

/-- Диагональное вложение `M → M × N`, `a ↦ (a, 1)`. -/
def diagMorphism : MonoidMorphism M (M × N) where
  toFun := fun a => (a, 1)
  map_mul := fun _ _ => by rw [prod_mul_eq, mul_one]
  map_one := rfl

/-- Пара морфизмов `f : M → N`, `g : M → P` порождает морфизм `M → N × P`. -/
def pairMorphism (f : MonoidMorphism M N) (g : MonoidMorphism M P) :
    MonoidMorphism M (N × P) where
  toFun := fun a => (f.toFun a, g.toFun a)
  map_mul := fun a b => by rw [f.map_mul, g.map_mul, prod_mul_eq]
  map_one := by rw [f.map_one, g.map_one]; rfl

/-- Первая проекция пары морфизмов даёт первый морфизм. -/
theorem fst_comp_pair (f : MonoidMorphism M N) (g : MonoidMorphism M P) :
    ((pairMorphism f g).comp fstMorphism).toFun = f.toFun := by
  funext a; rfl

/-- Вторая проекция пары морфизмов даёт второй морфизм. -/
theorem snd_comp_pair (f : MonoidMorphism M N) (g : MonoidMorphism M P) :
    ((pairMorphism f g).comp sndMorphism).toFun = g.toFun := by
  funext a; rfl

/-- Единственность пары: любой морфизм в произведение с заданными проекциями
    совпадает с `pairMorphism`. -/
theorem pair_unique (f : MonoidMorphism M N) (g : MonoidMorphism M P)
    (h : MonoidMorphism M (N × P))
    (hf : (h.comp fstMorphism).toFun = f.toFun)
    (hg : (h.comp sndMorphism).toFun = g.toFun) :
    h.toFun = (pairMorphism f g).toFun := by
  funext a
  have h1 : (h.toFun a).1 = f.toFun a := congrFun hf a
  have h2 : (h.toFun a).2 = g.toFun a := congrFun hg a
  exact Prod.ext h1 h2

/-! ### §4. Свойства элементов произведения -/

/-- Пара идемпотентна тогда и только тогда, когда идемпотентны обе компоненты. -/
theorem prod_isIdempotent {p : M × N} :
    IsIdempotent p ↔ IsIdempotent p.1 ∧ IsIdempotent p.2 := by
  obtain ⟨a, b⟩ := p
  exact Prod.ext_iff

/-- Пара обратима тогда и только тогда, когда обратимы обе компоненты. -/
theorem prod_isUnit' {p : M × N} :
    IsUnit' p ↔ IsUnit' p.1 ∧ IsUnit' p.2 := by
  obtain ⟨a, b⟩ := p
  constructor
  · rintro ⟨⟨c, d⟩, h1, h2⟩
    exact ⟨⟨c, congrArg Prod.fst h1, congrArg Prod.fst h2⟩,
           ⟨d, congrArg Prod.snd h1, congrArg Prod.snd h2⟩⟩
  · rintro ⟨⟨c, hc1, hc2⟩, ⟨d, hd1, hd2⟩⟩
    exact ⟨(c, d), Prod.ext hc1 hd1, Prod.ext hc2 hd2⟩

/-- Пара регулярна тогда и только тогда, когда регулярны обе компоненты. -/
theorem prod_isRegular {p : M × N} :
    UAM_Regular.IsRegular p ↔ UAM_Regular.IsRegular p.1 ∧ UAM_Regular.IsRegular p.2 := by
  obtain ⟨a, b⟩ := p
  constructor
  · rintro ⟨⟨c, d⟩, h⟩
    exact ⟨⟨c, congrArg Prod.fst h⟩, ⟨d, congrArg Prod.snd h⟩⟩
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact ⟨(c, d), Prod.ext hc hd⟩

/-- Пара — нуль тогда и только тогда, когда обе компоненты — нули. -/
theorem prod_isZero {p : M × N} :
    IsZero p ↔ IsZero p.1 ∧ IsZero p.2 := by
  obtain ⟨a, b⟩ := p
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun x => congrArg Prod.fst (h1 (x, b)),
            fun x => congrArg Prod.fst (h2 (x, b))⟩,
           ⟨fun y => congrArg Prod.snd (h1 (a, y)),
            fun y => congrArg Prod.snd (h2 (a, y))⟩⟩
  · rintro ⟨⟨h1l, h1r⟩, ⟨h2l, h2r⟩⟩
    refine ⟨fun q => ?_, fun q => ?_⟩
    · exact Prod.ext (h1l q.1) (h2l q.2)
    · exact Prod.ext (h1r q.1) (h2r q.2)

end UAM_DirectProduct
