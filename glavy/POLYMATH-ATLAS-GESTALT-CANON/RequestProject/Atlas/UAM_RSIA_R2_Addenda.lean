import Mathlib.Tactic
import RequestProject.Atlas.UAM_RSIA_CompressionDynamics
import RequestProject.Atlas.UAM_RSIA_BehavioralMetric
import RequestProject.Atlas.UAM_RSIA_PairedMetric

set_option autoImplicit false

/-!
# R2 Addenda: доказанные версии рекомендаций второго раунда обзора

Архивная версия этого модуля состояла из формулировок-заглушек (`sorry`).
Здесь те же пункты доведены до доказательств, а одна из предложенных
формулировок опровергнута контрпримером.

* §1 — равномерно убывающее сжатие. Исходная формулировка (условие на длину
  только для слов длиннее порога `N`) **неверна**: она допускает
  Nerode-сохраняющее сжатие языка с несколькими классами
  (`uniformlyRateDecreasing_nerodePreserving_exists`). Верной оказывается
  глобальная версия, без порога
  (`globalRate_compression_incompatibility`).
* §2 — `k`-ограниченное сохранение Nerode-классов и приближённая
  неувеличивающая оценка поведенческого расстояния
  (`behavioralDistance_k_nonexpansive`).
* §3 — класс `WordMetric` со всеми доказанными аксиомами для грубой метрики
  и общая теорема о разрыве формы и значения.
* §4 — коалгебраическая формулировка: функтор `Bool × (A → ·)`,
  коалгебры и их морфизмы; Nerode-сохраняющее отображение сохраняет
  наблюдение.
-/

namespace UAM_RSIA

open Classical

universe u

variable {α : Type u}

/-! ## §1 Равномерно убывающее сжатие -/

/-- Отображение равномерно убывает по длине, если найдутся `c < 1` и порог `N`
такие, что все слова длиннее `N` укорачиваются хотя бы в `c` раз. -/
def IsUniformlyRateDecreasing
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) : Prop :=
  ∃ (c : ℝ) (N : Nat), c < 1 ∧
    ∀ w, w.length ≥ N → ((f w).length : ℤ) ≤ ⌊c * (w.length : ℝ)⌋

/-- Глобальная (беспороговая) версия: оценка выполняется для всех слов. -/
def IsGloballyRateDecreasing
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∀ w, ((f w).length : ℤ) ≤ ⌊c * (w.length : ℝ)⌋

/-- Глобально убывающее по длине отображение строго антиэнтропийно. -/
theorem isStrictlyAntiEntropic_of_globallyRateDecreasing
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hf : IsGloballyRateDecreasing f) : IsStrictlyAntiEntropic f := by
  obtain ⟨c, hc, hbound⟩ := hf
  intro w hw
  have hpos : 0 < w.length := List.length_pos_iff.mpr hw
  have hlt : c * (w.length : ℝ) < (w.length : ℝ) := by
    have : (0 : ℝ) < (w.length : ℝ) := by exact_mod_cast hpos
    nlinarith
  have hfloor : ⌊c * (w.length : ℝ)⌋ < (w.length : ℤ) := by
    refine Int.floor_lt.mpr ?_
    push_cast
    linarith
  have := hbound w
  omega

/-- Глобально равномерное сжатие несовместимо с сохранением Nerode-классов
для языка, у которого этих классов больше одного. -/
theorem globalRate_compression_incompatibility
    (L : Set (UAM_Free.FreeMonoid α))
    (hclasses : HasMultipleNerodeClasses L) :
    ¬ ∃ f, NerodePreserving L f ∧ IsGloballyRateDecreasing f := by
  rintro ⟨f, hnerode, hrate⟩
  exact strict_fifth_barrier L hclasses
    ⟨f, hnerode, isStrictlyAntiEntropic_of_globallyRateDecreasing f hrate⟩

/-! ### Контрпример к пороговой формулировке -/

/-- Язык слов над `Bool`, начинающихся с `true`. -/
def headTrueLanguage : Set (UAM_Free.FreeMonoid Bool) :=
  {w | w.head? = some true}

/-- Сжатие «оставить первую букву». -/
def takeOne (w : UAM_Free.FreeMonoid Bool) : UAM_Free.FreeMonoid Bool := w.take 1

theorem takeOne_nerodePreserving : NerodePreserving headTrueLanguage takeOne := by
  intro w v
  cases w with
  | nil => rfl
  | cons a t => simp [takeOne, headTrueLanguage]

theorem headTrueLanguage_hasMultipleNerodeClasses :
    HasMultipleNerodeClasses headTrueLanguage := by
  refine ⟨[true], ?_⟩
  intro h
  have := h []
  simp [headTrueLanguage] at this

theorem takeOne_isUniformlyRateDecreasing : IsUniformlyRateDecreasing takeOne := by
  refine ⟨1 / 2, 2, by norm_num, ?_⟩
  intro w hw
  have hlen : (takeOne w).length ≤ 1 := by
    simp [takeOne]
  have h1 : (1 : ℤ) ≤ ⌊(1 / 2 : ℝ) * (w.length : ℝ)⌋ := by
    refine Int.le_floor.mpr ?_
    have : (2 : ℝ) ≤ (w.length : ℝ) := by exact_mod_cast hw
    push_cast
    linarith
  have : ((takeOne w).length : ℤ) ≤ 1 := by exact_mod_cast hlen
  omega

/-- Пороговая формулировка «равномерного барьера» **неверна**: существует язык
с несколькими Nerode-классами и Nerode-сохраняющее отображение, равномерно
убывающее по длине для всех достаточно длинных слов. -/
theorem uniformlyRateDecreasing_nerodePreserving_exists :
    ∃ (L : Set (UAM_Free.FreeMonoid Bool))
      (f : UAM_Free.FreeMonoid Bool → UAM_Free.FreeMonoid Bool),
      HasMultipleNerodeClasses L ∧ NerodePreserving L f ∧
        IsUniformlyRateDecreasing f :=
  ⟨headTrueLanguage, takeOne, headTrueLanguage_hasMultipleNerodeClasses,
    takeOne_nerodePreserving, takeOne_isUniformlyRateDecreasing⟩

/-- Отсюда: рекомендованное усиление пятого барьера в пороговой форме ложно. -/
theorem not_uniform_rate_compression_incompatibility :
    ¬ ∀ (L : Set (UAM_Free.FreeMonoid Bool)),
        HasMultipleNerodeClasses L →
          ¬ ∃ f, NerodePreserving L f ∧ IsUniformlyRateDecreasing f := by
  intro h
  obtain ⟨L, f, hclasses, hnerode, hrate⟩ :=
    uniformlyRateDecreasing_nerodePreserving_exists
  exact h L hclasses ⟨f, hnerode, hrate⟩

/-! ## §2 `k`-ограниченное сохранение Nerode-классов -/

/-- Отображение `k`-сохраняет Nerode-классы, если остаточные языки совпадают
на всех суффиксах длины не больше `k`. -/
def IsKNerodePreserving
    (L : Set (UAM_Free.FreeMonoid α))
    (k : Nat)
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α) : Prop :=
  ∀ w v, v.length ≤ k → ((w ++ v ∈ L) ↔ (f w ++ v ∈ L))

/-- На суффиксах длины не больше `k` различимость слов и их образов совпадает. -/
theorem distinguishedAt_iff_of_kNerodePreserving
    {L : Set (UAM_Free.FreeMonoid α)} {k : Nat}
    {f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α}
    (hf : IsKNerodePreserving L k f)
    (w₁ w₂ : UAM_Free.FreeMonoid α) {n : Nat} (hn : n ≤ k) :
    DistinguishedAt L w₁ w₂ n ↔ DistinguishedAt L (f w₁) (f w₂) n := by
  constructor
  · rintro ⟨v, hv, hne⟩
    refine ⟨v, hv, ?_⟩
    rw [← propext (hf w₁ v (hv ▸ hn)), ← propext (hf w₂ v (hv ▸ hn))]
    exact hne
  · rintro ⟨v, hv, hne⟩
    refine ⟨v, hv, ?_⟩
    rw [propext (hf w₁ v (hv ▸ hn)), propext (hf w₂ v (hv ▸ hn))]
    exact hne

/-- Если различающих суффиксов длины `≤ k` нет, поведенческое расстояние не
превосходит `2⁻⁽ᵏ⁺¹⁾`. -/
theorem behavioralDistance_le_of_no_short_distinguisher
    (L : Set (UAM_Free.FreeMonoid α)) (k : Nat)
    (w₁ w₂ : UAM_Free.FreeMonoid α)
    (h : ∀ n ≤ k, ¬ DistinguishedAt L w₁ w₂ n) :
    behavioralDistance L w₁ w₂ ≤ (2 : ℝ)⁻¹ ^ (k + 1) := by
  unfold behavioralDistance distinguishingSuffixLength
  split_ifs with hex
  · have hgt : k < Nat.find hex := by
      by_contra hcon
      push_neg at hcon
      exact h _ hcon (Nat.find_spec hex)
    have : (2 : ℝ)⁻¹ ^ (Nat.find hex) ≤ (2 : ℝ)⁻¹ ^ (k + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hgt
    simp only []
    exact this
  · simp

/-- Если различающий суффикс длины `≤ k` существует, то расстояния совпадают. -/
theorem behavioralDistance_eq_of_short_distinguisher
    {L : Set (UAM_Free.FreeMonoid α)} {k : Nat}
    {f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α}
    (hf : IsKNerodePreserving L k f)
    (w₁ w₂ : UAM_Free.FreeMonoid α)
    (hshort : ∃ n ≤ k, DistinguishedAt L w₁ w₂ n) :
    behavioralDistance L (f w₁) (f w₂) = behavioralDistance L w₁ w₂ := by
  obtain ⟨n₀, hn₀k, hn₀⟩ := hshort
  have hex : ∃ n, DistinguishedAt L w₁ w₂ n := ⟨n₀, hn₀⟩
  have hex' : ∃ n, DistinguishedAt L (f w₁) (f w₂) n :=
    ⟨n₀, (distinguishedAt_iff_of_kNerodePreserving hf w₁ w₂ hn₀k).mp hn₀⟩
  have hfind_le : Nat.find hex ≤ n₀ := Nat.find_min' hex hn₀
  have hfind_le' : Nat.find hex' ≤ n₀ :=
    Nat.find_min' hex' ((distinguishedAt_iff_of_kNerodePreserving hf w₁ w₂ hn₀k).mp hn₀)
  have h1 : Nat.find hex' ≤ Nat.find hex :=
    Nat.find_min' hex'
      ((distinguishedAt_iff_of_kNerodePreserving hf w₁ w₂
        (le_trans hfind_le hn₀k)).mp (Nat.find_spec hex))
  have h2 : Nat.find hex ≤ Nat.find hex' :=
    Nat.find_min' hex
      ((distinguishedAt_iff_of_kNerodePreserving hf w₁ w₂
        (le_trans hfind_le' hn₀k)).mpr (Nat.find_spec hex'))
  have heq : Nat.find hex' = Nat.find hex := le_antisymm h1 h2
  unfold behavioralDistance distinguishingSuffixLength
  rw [dif_pos hex, dif_pos hex']
  simp [heq]

/-- `k`-сохраняющее отображение почти не меняет поведенческое расстояние:
отклонение не превосходит `2⁻ᵏ`. -/
theorem behavioralDistance_k_nonexpansive
    (L : Set (UAM_Free.FreeMonoid α))
    (k : Nat)
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hf : IsKNerodePreserving L k f)
    (w₁ w₂ : UAM_Free.FreeMonoid α) :
    |behavioralDistance L (f w₁) (f w₂) -
      behavioralDistance L w₁ w₂| ≤ (2 : ℝ)⁻¹ ^ k := by
  by_cases hshort : ∃ n ≤ k, DistinguishedAt L w₁ w₂ n
  · rw [behavioralDistance_eq_of_short_distinguisher hf w₁ w₂ hshort]
    simp
  · push_neg at hshort
    have hno : ∀ n ≤ k, ¬ DistinguishedAt L w₁ w₂ n := fun n hn => hshort n hn
    have hno' : ∀ n ≤ k, ¬ DistinguishedAt L (f w₁) (f w₂) n := by
      intro n hn hd
      exact hno n hn ((distinguishedAt_iff_of_kNerodePreserving hf w₁ w₂ hn).mpr hd)
    have hb₁ := behavioralDistance_le_of_no_short_distinguisher L k w₁ w₂ hno
    have hb₂ := behavioralDistance_le_of_no_short_distinguisher L k (f w₁) (f w₂) hno'
    have hp₁ := behavioralDistance_nonneg L w₁ w₂
    have hp₂ := behavioralDistance_nonneg L (f w₁) (f w₂)
    have hhalf : (2 : ℝ)⁻¹ ^ (k + 1) ≤ (2 : ℝ)⁻¹ ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
    rw [abs_le]
    constructor <;> linarith

/-! ## §3 Класс метрик на словах -/

/-- Метрика на словах: невырожденная, симметричная, с неравенством
треугольника. -/
class WordMetric (α : Type u) where
  dist : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α → ℕ
  nondeg : ∀ w₁ w₂, dist w₁ w₂ = 0 ↔ w₁ = w₂
  symm : ∀ w₁ w₂, dist w₁ w₂ = dist w₂ w₁
  triangle : ∀ w₁ w₂ w₃, dist w₁ w₃ ≤ dist w₁ w₂ + dist w₂ w₃

/-- Грубое расстояние: `0` для равных слов, `1` для слов разной длины и `2`
для различных слов одинаковой длины. -/
noncomputable def coarseDist (w₁ w₂ : UAM_Free.FreeMonoid α) : ℕ :=
  if w₁ = w₂ then 0 else if w₁.length = w₂.length then 2 else 1

/-- Грубое расстояние — метрика на словах. -/
noncomputable instance coarseWordMetric : WordMetric α where
  dist := coarseDist
  nondeg := by
    intro w₁ w₂
    unfold coarseDist
    split_ifs <;> simp_all
  symm := by
    intro w₁ w₂
    unfold coarseDist
    by_cases h : w₁ = w₂
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
      by_cases hl : w₁.length = w₂.length
      · rw [if_pos hl, if_pos hl.symm]
      · rw [if_neg hl, if_neg (fun hh => hl hh.symm)]
  triangle := by
    intro w₁ w₂ w₃
    unfold coarseDist
    split_ifs <;> simp_all

/-- Разрыв формы и значения для любой метрики на словах: различные слова
находятся на положительном структурном расстоянии, даже если они
Nerode-эквивалентны (то есть семантически неразличимы). -/
theorem form_meaning_gap_generic
    {α : Type u} [wm : WordMetric α]
    (w₁ w₂ : UAM_Free.FreeMonoid α)
    (hne : w₁ ≠ w₂) :
    0 < wm.dist w₁ w₂ :=
  Nat.pos_of_ne_zero fun h => hne ((wm.nondeg w₁ w₂).mp h)

/-! ## §4 Коалгебраическая формулировка -/

/-- Функтор детерминированных автоматов Раттена: `F X = Bool × (A → X)`. -/
def RSIA_Functor (A : Type u) (X : Type u) : Type u := Bool × (A → X)

/-- Коалгебра этого функтора — автомат с булевым наблюдением. -/
structure RSIA_Coalgebra (A : Type u) where
  carrier : Type u
  observe : carrier → Bool
  predict : carrier → A → carrier

/-- Морфизм коалгебр. -/
structure RSIA_CoalgebraMorphism {A : Type u} (C₁ C₂ : RSIA_Coalgebra A) where
  map : C₁.carrier → C₂.carrier
  observe_compat : ∀ x, C₂.observe (map x) = C₁.observe x
  predict_compat : ∀ x a, C₂.predict (map x) a = map (C₁.predict x a)

/-- Тождественный морфизм коалгебр. -/
def RSIA_CoalgebraMorphism.id {A : Type u} (C : RSIA_Coalgebra A) :
    RSIA_CoalgebraMorphism C C where
  map := _root_.id
  observe_compat := fun _ => rfl
  predict_compat := fun _ _ => rfl

/-- Композиция морфизмов коалгебр. -/
def RSIA_CoalgebraMorphism.comp {A : Type u} {C₁ C₂ C₃ : RSIA_Coalgebra A}
    (g : RSIA_CoalgebraMorphism C₂ C₃) (f : RSIA_CoalgebraMorphism C₁ C₂) :
    RSIA_CoalgebraMorphism C₁ C₃ where
  map := g.map ∘ f.map
  observe_compat := fun x => by
    simp [Function.comp, g.observe_compat, f.observe_compat]
  predict_compat := fun x a => by
    simp [Function.comp, g.predict_compat, f.predict_compat]

/-- Коалгебра слов языка `L`: наблюдение — принадлежность языку,
переход — дописывание буквы справа. -/
noncomputable def wordCoalgebra (L : Set (UAM_Free.FreeMonoid α)) :
    RSIA_Coalgebra α where
  carrier := UAM_Free.FreeMonoid α
  observe := fun w => decide (w ∈ L)
  predict := fun w a => w ++ [a]

/-- Nerode-сохраняющее отображение сохраняет наблюдение коалгебры слов. -/
theorem nerodePreserving_observe
    (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hf : NerodePreserving L f) (w : UAM_Free.FreeMonoid α) :
    (wordCoalgebra L).observe (f w) = (wordCoalgebra L).observe w := by
  have h := hf w []
  simp only [List.append_nil] at h
  simp [wordCoalgebra, h]

/-- Если Nerode-сохраняющее отображение коммутирует с дописыванием буквы, оно
является эндоморфизмом коалгебры слов. -/
def nerodePreserving_toCoalgebraEndomorphism
    (L : Set (UAM_Free.FreeMonoid α))
    (f : UAM_Free.FreeMonoid α → UAM_Free.FreeMonoid α)
    (hf : NerodePreserving L f)
    (hcomm : ∀ w a, f (w ++ [a]) = f w ++ [a]) :
    RSIA_CoalgebraMorphism (wordCoalgebra L) (wordCoalgebra L) where
  map := f
  observe_compat := nerodePreserving_observe L f hf
  predict_compat := fun w a => (hcomm w a).symm

end UAM_RSIA
