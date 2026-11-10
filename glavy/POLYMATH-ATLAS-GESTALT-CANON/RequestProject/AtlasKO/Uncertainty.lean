/-
# STEP-005: информация уменьшает неопределённость

Формализация математического слоя кластера STEP-005:

* CONCEPT-010 «Неопределённость конфигурации» — энтропия Шеннона над
  пространством допустимых топологий;
* CONCEPT-011 «Релевантность данных» — доля полезной информации `R = I_rel/I`;
* MECHANISM-005 «Редукция неопределённости» — `U₁ = U₀ - min(Γ, R·I)`;
* INVARIANT-005 «Информационное снижение неопределённости» —
  `ΔU ≤ -α·R·I` и нижняя граница, задаваемая шумом канала.

Ключевые доказанные утверждения: неопределённость никогда не растёт от
поступления информации, снижение ограничено пропускной способностью канала,
шумовой порог непреодолим, и при ненулевом релевантном потоке порог
достигается за конечное число шагов.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.AtlasKO

/-! ## CONCEPT-010: неопределённость конфигурации -/

/-- Неопределённость конфигурации: энтропия Шеннона распределения `p`
над пространством допустимых топологий, `U = -Σ pᵢ log pᵢ`. -/
noncomputable def configEntropy {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- Энтропия неотрицательна для любого распределения вероятностей. -/
theorem configEntropy_nonneg {n : ℕ} {p : Fin n → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) : 0 ≤ configEntropy p :=
  Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (h0 i) (h1 i)

/-- Детерминированная конфигурация (вся вероятность на одном варианте)
имеет нулевую неопределённость. -/
theorem configEntropy_point_mass {n : ℕ} (j : Fin n) :
    configEntropy (fun i => if i = j then (1 : ℝ) else 0) = 0 := by
  unfold configEntropy
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : i = j <;> simp [h, Real.negMulLog]

/-! ## CONCEPT-011: релевантность данных -/

/-- Релевантность `R = I_rel / I` — доля информации, реально снижающей
неопределённость. -/
noncomputable def relevance (iRel iTotal : ℝ) : ℝ := iRel / iTotal

/-- Релевантность лежит в отрезке `[0,1]`. -/
theorem relevance_mem_unitInterval {iRel iTotal : ℝ} (h0 : 0 ≤ iRel)
    (hle : iRel ≤ iTotal) (hpos : 0 < iTotal) :
    0 ≤ relevance iRel iTotal ∧ relevance iRel iTotal ≤ 1 := by
  refine ⟨div_nonneg h0 hpos.le, (div_le_one hpos).2 hle⟩

/-- Нулевая релевантность означает полностью бесполезный поток. -/
theorem relevance_zero {iTotal : ℝ} : relevance 0 iTotal = 0 := by
  simp [relevance]

/-! ## MECHANISM-005: редукция неопределённости -/

/-- `U₁ = U₀ - min(Γ, R·I)`: снижение неопределённости ограничено
пропускной способностью канала `Γ`. -/
noncomputable def reduce (u0 gamma rel info : ℝ) : ℝ :=
  u0 - min gamma (rel * info)

/-- Информация не увеличивает неопределённость. -/
theorem reduce_le {u0 gamma rel info : ℝ} (hg : 0 ≤ gamma) (hr : 0 ≤ rel)
    (hi : 0 ≤ info) : reduce u0 gamma rel info ≤ u0 := by
  unfold reduce
  have : 0 ≤ min gamma (rel * info) := le_min hg (mul_nonneg hr hi)
  linarith

/-- **Пропускная способность канала — потолок редукции.**  Как бы ни был велик
объём данных, за один шаг неопределённость не может снизиться больше, чем на
`Γ`. -/
theorem reduce_bounded_by_channel (u0 gamma rel info : ℝ) :
    u0 - reduce u0 gamma rel info ≤ gamma := by
  unfold reduce
  have : min gamma (rel * info) ≤ gamma := min_le_left _ _
  linarith

/-- Нерелевантный поток не снижает неопределённость. -/
theorem reduce_of_relevance_zero {u0 gamma info : ℝ} (hg : 0 ≤ gamma) :
    reduce u0 gamma 0 info = u0 := by
  unfold reduce
  rw [zero_mul, min_eq_right hg]
  ring

/-- Больший объём релевантных данных снижает неопределённость не слабее. -/
theorem reduce_antitone_in_info {u0 gamma rel i₁ i₂ : ℝ} (hr : 0 ≤ rel) (h : i₁ ≤ i₂) :
    reduce u0 gamma rel i₂ ≤ reduce u0 gamma rel i₁ := by
  unfold reduce
  have : min gamma (rel * i₁) ≤ min gamma (rel * i₂) :=
    le_min (min_le_left _ _) (le_trans (min_le_right _ _) (by nlinarith))
  linarith

/-! ## INVARIANT-005: информационное снижение неопределённости -/

/-- Линейная форма инварианта: при `α·R·I ≤ Γ` снижение не меньше `α·R·I`,
то есть `ΔU ≤ -α·R·I`. -/
theorem invariant005_linear {u0 gamma rel info alpha : ℝ}
    (halpha1 : alpha ≤ 1) (hr : 0 ≤ rel) (hi : 0 ≤ info)
    (hcap : alpha * (rel * info) ≤ gamma) :
    reduce u0 gamma rel info - u0 ≤ -(alpha * (rel * info)) := by
  unfold reduce
  have hle : alpha * (rel * info) ≤ rel * info := by nlinarith [mul_nonneg hr hi]
  have : alpha * (rel * info) ≤ min gamma (rel * info) := le_min hcap hle
  linarith

/-- Последовательность неопределённостей с шумовым порогом `floor`:
каждый шаг снижает `U` на `min(Γ, R·I)`, но не ниже порога. -/
noncomputable def uSeq (floor u0 step : ℝ) : ℕ → ℝ
  | 0 => u0
  | n + 1 => max floor (uSeq floor u0 step n - step)

/-- **Шумовой порог непреодолим.**  Неопределённость никогда не опускается
ниже уровня, задаваемого шумом канала: `lim U > 0` при `floor > 0`. -/
theorem uSeq_ge_floor {floor u0 step : ℝ} (h0 : floor ≤ u0) (n : ℕ) :
    floor ≤ uSeq floor u0 step n := by
  induction n with
  | zero => simpa [uSeq] using h0
  | succ n _ => exact le_max_left _ _

/-- Неопределённость не растёт. -/
theorem uSeq_antitone {floor u0 step : ℝ} (h0 : floor ≤ u0) (hs : 0 ≤ step) :
    Antitone (uSeq floor u0 step) := by
  apply antitone_nat_of_succ_le
  intro n
  have hfl : floor ≤ uSeq floor u0 step n := uSeq_ge_floor h0 n
  show max floor (uSeq floor u0 step n - step) ≤ uSeq floor u0 step n
  exact max_le hfl (by linarith)

/-- Явная нижняя оценка скорости сходимости. -/
theorem uSeq_le {floor u0 step : ℝ} (hs : 0 ≤ step) (n : ℕ) :
    uSeq floor u0 step n ≤ max floor (u0 - n * step) := by
  induction n with
  | zero => simp [uSeq]
  | succ n ih =>
    show max floor (uSeq floor u0 step n - step) ≤ _
    have h1 : uSeq floor u0 step n - step ≤ max floor (u0 - n * step) - step := by linarith
    refine max_le (le_max_left _ _) (le_trans h1 ?_)
    rcases max_cases floor (u0 - n * step) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      exact le_trans (by linarith) (le_max_left _ _)
    · rw [he]
      have : u0 - (n : ℝ) * step - step = u0 - ((n : ℕ) + 1 : ℕ) * step := by push_cast; ring
      rw [this]
      exact le_max_right _ _

/-- **Порог достигается за конечное число шагов.**  При ненулевом релевантном
потоке неопределённость доходит до шумового порога и дальше не меняется. -/
theorem uSeq_reaches_floor {floor u0 step : ℝ} (h0 : floor ≤ u0) (hs : 0 < step) :
    ∃ n : ℕ, uSeq floor u0 step n = floor := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((u0 - floor) / step)
  refine ⟨n, le_antisymm ?_ ?_⟩
  · have hb := uSeq_le (floor := floor) (u0 := u0) (step := step) hs.le n
    have hlt : u0 - n * step ≤ floor := by
      rw [div_lt_iff₀ hs] at hn
      nlinarith
    calc uSeq floor u0 step n ≤ max floor (u0 - n * step) := hb
      _ = floor := max_eq_left hlt
  · exact uSeq_ge_floor h0 n

end Polymath.AtlasKO
