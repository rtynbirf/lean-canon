import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe, reach, reachLeft (транзитивно)
import RequestProject.Atlas.UAM_Green            -- R_eq, L_eq, H_eq
import RequestProject.Atlas.UAM_Morphism         -- MonoidMorphism (собственный морфизм UAM)

/-!
# UAM — Layer 3: Подмоноиды (Submonoid)

Подмоноиды моноида и их связь с достижимостью и отношениями Грина.
Файл импортирует канонические определения и не переопределяет их.

Морфизмы здесь — собственные морфизмы UAM (`UAM_Morphism.MonoidMorphism`),
а не `MonoidHom` из Mathlib: слой подмоноидов не зависит от алгебраической
иерархии Mathlib сверх самого класса `Monoid`.
-/

namespace UAM_Submonoid
universe u

open UAM_Directionality UAM_Reachability UAM_Green

/-- Подмоноид `S` моноида `M`: подмножество с `1`, замкнутое
    относительно умножения. -/
structure Submonoid (M : Type u) [Monoid M] where
  carrier : Set M
  one_mem : (1 : M) ∈ carrier
  mul_mem : ∀ a b : M, a ∈ carrier → b ∈ carrier → a * b ∈ carrier

namespace Submonoid
variable {M : Type u} [Monoid M] {S : Submonoid M}

theorem mem_one : (1 : M) ∈ S.carrier := S.one_mem

theorem mem_mul {a b : M} : a ∈ S.carrier → b ∈ S.carrier → a * b ∈ S.carrier :=
  S.mul_mem a b

end Submonoid

/-! ### §1. Базовые конструкции -/

/-- Тривиальный подмоноид `{1}`. -/
def trivial (M : Type u) [Monoid M] : Submonoid M where
  carrier := {1}
  one_mem := rfl
  mul_mem := fun a b ha hb => by
    rw [Set.mem_singleton_iff] at ha hb ⊢
    rw [ha, hb, mul_one]

/-- Весь моноид как подмоноид. -/
def top (M : Type u) [Monoid M] : Submonoid M where
  carrier := Set.univ
  one_mem := Set.mem_univ 1
  mul_mem := fun _ _ _ _ => Set.mem_univ _

/-- Пересечение двух подмоноидов. -/
def inter {M : Type u} [Monoid M] (S T : Submonoid M) : Submonoid M where
  carrier := S.carrier ∩ T.carrier
  one_mem := ⟨S.one_mem, T.one_mem⟩
  mul_mem := fun a b ha hb =>
    ⟨S.mul_mem a b ha.1 hb.1, T.mul_mem a b ha.2 hb.2⟩

/-! ### §2. Гомоморфизмы и подмоноиды -/

/-- Образ подмоноида под гомоморфизмом. -/
def image {M N : Type u} [Monoid M] [Monoid N] (f : UAM_Morphism.MonoidMorphism M N)
    (S : Submonoid M) : Submonoid N where
  carrier := f.toFun '' S.carrier
  one_mem := ⟨1, S.one_mem, f.map_one⟩
  mul_mem := fun a b ha hb => by
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x * y, S.mul_mem x y hx hy, f.map_mul x y⟩

/-- Прообраз подмоноида под гомоморфизмом. -/
def preimage {M N : Type u} [Monoid M] [Monoid N] (f : UAM_Morphism.MonoidMorphism M N)
    (T : Submonoid N) : Submonoid M where
  carrier := f.toFun ⁻¹' T.carrier
  one_mem := by
    show f.toFun 1 ∈ T.carrier
    rw [f.map_one]
    exact T.one_mem
  mul_mem := fun a b ha hb => by
    show f.toFun (a * b) ∈ T.carrier
    rw [f.map_mul]
    exact T.mul_mem (f.toFun a) (f.toFun b) ha hb

/-! ### §3. UAM: подмоноид и достижимость -/

/-- Правые кратные `a`, лежащие в подмоноиде, содержатся в `reach a`. -/
theorem reach_submonoid_subset {M : Type u} [Monoid M] (S : Submonoid M) (a : M) :
    {b | b ∈ S.carrier ∧ ∃ c ∈ S.carrier, a * c = b} ⊆ reach a := by
  rintro b ⟨_, c, _, hc⟩
  exact ⟨c, hc⟩

/-- Если `e` идемпотент и `a` H-эквивалентно `e`, то `a` лежит в правом
    локальном моноиде `eMe`. -/
theorem H_subset_eMe {M : Type u} [Monoid M] {e a : M} (he : e * e = e) (h : H_eq e a) :
    a ∈ {x : M | ∃ y : M, e * y * e = x} := by
  obtain ⟨hR, hL⟩ := h
  -- Из R_eq: a ∈ reach e = reach a, поэтому ∃ c, e * c = a, откуда e * a = a
  have haR : a ∈ reach a := ⟨1, mul_one a⟩
  rw [← hR] at haR
  obtain ⟨c, hc⟩ := haR
  have hea : e * a = a := by
    rw [← hc, ← mul_assoc, he]
  -- Из L_eq: a ∈ reachLeft e, поэтому ∃ d, d * e = a, откуда a * e = a
  have haL : a ∈ reachLeft a := ⟨1, one_mul a⟩
  rw [← hL] at haL
  obtain ⟨d, hd⟩ := haL
  have hae : a * e = a := by
    rw [← hd, mul_assoc, he]
  exact ⟨a, by rw [hea, hae]⟩

/-! ### §4. Правый локальный моноид

  ЗАМЕЧАНИЕ О ФОРМАЛИЗАЦИИ.  Правый локальный моноид `eMe = e·M·e` для
  идемпотента `e` является моноидом с единицей `e`, а НЕ с глобальной
  единицей `1` объемлющего моноида `M`.  В общем случае `1 ∉ e·M·e`
  (это потребовало бы `∃ y, e·y·e = 1`).  Поэтому `eMe` НЕ является
  подмоноидом `M` в смысле структуры `Submonoid` выше (которая требует
  `1 ∈ carrier`).  Исходная спецификация задачи (`eMe … : Submonoid M`)
  в этом месте математически нереализуема, и мы формализуем `eMe`
  честно — как множество `Set M`, снабжённое доказательствами замкнутости
  относительно умножения и того, что `e` — его двусторонняя единица. -/

/-- Правый локальный моноид `eMe = e·M·e` для идемпотента `e`
    (как множество; его единицей является `e`, а не `1`). -/
def eMe {M : Type u} [Monoid M] (e : M) : Set M := {x | ∃ y, e * y * e = x}

/-- `e` принадлежит `eMe e` (при идемпотентности `e`). -/
theorem e_mem_eMe {M : Type u} [Monoid M] {e : M} (he : e * e = e) : e ∈ eMe e :=
  ⟨e, by rw [he, he]⟩

/-- `eMe e` замкнуто относительно умножения. -/
theorem eMe_mul_mem {M : Type u} [Monoid M] {e : M}
    {a b : M} (ha : a ∈ eMe e) (hb : b ∈ eMe e) : a * b ∈ eMe e := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x * e * e * y, ?_⟩
  rw [← hx, ← hy]
  simp only [mul_assoc]

/-- В `eMe` элемент `e` является двусторонней единицей. -/
theorem eMe_identity {M : Type u} [Monoid M] {e : M} (he : e * e = e)
    {a : M} (ha : a ∈ eMe e) : e * a = a ∧ a * e = a := by
  obtain ⟨y, hy⟩ := ha
  constructor
  · rw [← hy, ← mul_assoc, ← mul_assoc, he]
  · rw [← hy, mul_assoc, mul_assoc, he, ← mul_assoc]

end UAM_Submonoid
