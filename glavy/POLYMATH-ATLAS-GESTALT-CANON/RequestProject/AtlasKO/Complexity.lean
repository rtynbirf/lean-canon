/-
# STEP-006: редукция неопределённости порождает уровни сложности

Формализация математического слоя кластера STEP-006:

* CONCEPT-013 «Высвобожденный ресурс» — `R_free = C(U₀) - C(U₁) ≥ 0`;
* CONCEPT-012 «Уровень системной сложности» — условие появления уровня
  `L_{k+1}`;
* MECHANISM-006 «Формирование уровней сложности» — `R_free ≥ R_min` и
  `U₁ ≤ U_crit`, с последующим приростом вторичной неопределённости;
* INVARIANT-006 «Порождение сложности через редукцию неопределённости» —
  `ΔL = κ·R_free`, `0 ≤ κ ≤ 1`.

Ключевые доказанные утверждения: высвобожденный ресурс неотрицателен и
монотонен по снижению неопределённости; жёсткая (непластичная) система
не порождает уровней; каскад «снижение → новый уровень → вторичная
неопределённость» прогрессирует тогда и только тогда, когда вторичная
неопределённость меньше снижения.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.AtlasKO

/-! ## CONCEPT-013: высвобожденный ресурс -/

/-- Стоимость преодоления неопределённости `C` монотонна: чем выше
неопределённость, тем дороже с ней работать. -/
structure CostModel where
  /-- Функция стоимости `C(U)`. -/
  cost : ℝ → ℝ
  /-- Монотонность: большей неопределённости соответствует большая стоимость. -/
  mono : Monotone cost

/-- Высвобожденный ресурс `R_free = C(U₀) - C(U₁)`. -/
def CostModel.rFree (C : CostModel) (u0 u1 : ℝ) : ℝ := C.cost u0 - C.cost u1

/-- Высвобожденный ресурс неотрицателен при снижении неопределённости. -/
theorem CostModel.rFree_nonneg (C : CostModel) {u0 u1 : ℝ} (h : u1 ≤ u0) :
    0 ≤ C.rFree u0 u1 := by
  have := C.mono h
  simp [CostModel.rFree]
  linarith

/-- Без снижения неопределённости ресурс не высвобождается. -/
theorem CostModel.rFree_self (C : CostModel) (u : ℝ) : C.rFree u u = 0 := by
  simp [CostModel.rFree]

/-- Чем сильнее снижение неопределённости, тем больше высвобожденный ресурс. -/
theorem CostModel.rFree_mono (C : CostModel) {u0 u1 u2 : ℝ} (h : u2 ≤ u1) :
    C.rFree u0 u1 ≤ C.rFree u0 u2 := by
  have := C.mono h
  simp only [CostModel.rFree]
  linarith

/-! ## INVARIANT-006: прирост сложности -/

/-- Прирост сложности `ΔL = κ·R_free`, где `κ ∈ [0,1]` — пластичность системы. -/
def deltaL (kappa rFree : ℝ) : ℝ := kappa * rFree

/-- Прирост сложности не превосходит высвобожденного ресурса. -/
theorem deltaL_le_rFree {kappa rFree : ℝ} (h1 : kappa ≤ 1) (hr : 0 ≤ rFree) :
    deltaL kappa rFree ≤ rFree := by
  unfold deltaL
  nlinarith

/-- Прирост сложности неотрицателен. -/
theorem deltaL_nonneg {kappa rFree : ℝ} (hk : 0 ≤ kappa) (hr : 0 ≤ rFree) :
    0 ≤ deltaL kappa rFree := mul_nonneg hk hr

/-- **Граничное условие инварианта: жёсткая система.**  При нулевой
пластичности снижение неопределённости не порождает сложности. -/
theorem deltaL_rigid (rFree : ℝ) : deltaL 0 rFree = 0 := by simp [deltaL]

/-- **Граничное условие инварианта: `ΔU = 0`.**  Без снижения
неопределённости прироста сложности нет. -/
theorem deltaL_of_no_reduction (C : CostModel) (kappa u : ℝ) :
    deltaL kappa (C.rFree u u) = 0 := by
  rw [C.rFree_self]
  simp [deltaL]

/-! ## MECHANISM-006 / CONCEPT-012: условие появления уровня -/

/-- Уровень `L_{k+1}` может сформироваться, если высвобожденного ресурса
хватает и остаточная неопределённость ниже критического порога. -/
def canFormLevel (rFree rMin u1 uCrit : ℝ) : Prop := rMin ≤ rFree ∧ u1 ≤ uCrit

/-- Условие монотонно по высвобожденному ресурсу. -/
theorem canFormLevel_mono {r₁ r₂ rMin u1 uCrit : ℝ} (h : r₁ ≤ r₂)
    (hc : canFormLevel r₁ rMin u1 uCrit) : canFormLevel r₂ rMin u1 uCrit :=
  ⟨le_trans hc.1 h, hc.2⟩

/-- **Полное устранение неопределённости не требуется**: достаточно опуститься
ниже критического порога. -/
theorem canFormLevel_of_below_crit {rFree rMin u1 uCrit : ℝ}
    (hr : rMin ≤ rFree) (hu : u1 ≤ uCrit) : canFormLevel rFree rMin u1 uCrit :=
  ⟨hr, hu⟩

/-- Если ресурса не хватает, уровень не формируется. -/
theorem not_canFormLevel_of_insufficient {rFree rMin u1 uCrit : ℝ} (h : rFree < rMin) :
    ¬ canFormLevel rFree rMin u1 uCrit := by
  rintro ⟨h1, -⟩
  exact absurd h1 (not_le.2 h)

/-! ## Каскад «редукция → уровень → вторичная неопределённость» -/

/-- Неопределённость после `n` циклов: каждый цикл снижает её на `du`
и добавляет вторичную неопределённость `ddu` нового уровня. -/
def cascadeU (u0 du ddu : ℝ) : ℕ → ℝ
  | 0 => u0
  | n + 1 => cascadeU u0 du ddu n - du + ddu

/-- Замкнутая форма каскада. -/
theorem cascadeU_closed (u0 du ddu : ℝ) (n : ℕ) :
    cascadeU u0 du ddu n = u0 - n * (du - ddu) := by
  induction n with
  | zero => simp [cascadeU]
  | succ n ih =>
    simp only [cascadeU, ih]
    push_cast
    ring

/-- **Каскад прогрессирует.**  Если вторичная неопределённость меньше
снижения, неопределённость строго убывает от цикла к циклу. -/
theorem cascadeU_strictAnti {u0 du ddu : ℝ} (h : ddu < du) :
    StrictAnti (cascadeU u0 du ddu) := by
  intro a b hab
  rw [cascadeU_closed, cascadeU_closed]
  have hlt : (a : ℝ) < b := by exact_mod_cast hab
  nlinarith

/-- **Каскад достигает любого порога.**  При `δU < ΔU` неопределённость
рано или поздно опускается ниже критического порога. -/
theorem cascadeU_below_crit {u0 du ddu : ℝ} (h : ddu < du) (uCrit : ℝ) :
    ∃ n : ℕ, cascadeU u0 du ddu n ≤ uCrit := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((u0 - uCrit) / (du - ddu))
  refine ⟨n, ?_⟩
  rw [cascadeU_closed]
  have hpos : 0 < du - ddu := by linarith
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- **Каскад глохнет.**  Если вторичная неопределённость нового уровня не
меньше достигнутого снижения, неопределённость никогда не падает ниже
исходной — новых уровней не будет. -/
theorem cascadeU_stalls {u0 du ddu : ℝ} (h : du ≤ ddu) (n : ℕ) :
    u0 ≤ cascadeU u0 du ddu n := by
  rw [cascadeU_closed]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- Число уровней, построенных за `n` циклов прогрессирующего каскада. -/
def levels (n : ℕ) : ℕ := n

/-- Сложность растёт вместе с числом успешных циклов. -/
theorem levels_strictMono : StrictMono levels := fun _ _ h => h

/-- **Связка инварианта и каскада.**  На каждом цикле прогрессирующего каскада
высвобождается строго положительный ресурс, если стоимость строго монотонна. -/
theorem cascade_rFree_pos (C : CostModel) (hstrict : StrictMono C.cost)
    {u0 du ddu : ℝ} (h : ddu < du) (n : ℕ) :
    0 < C.rFree (cascadeU u0 du ddu n) (cascadeU u0 du ddu (n + 1)) := by
  have hlt : cascadeU u0 du ddu (n + 1) < cascadeU u0 du ddu n :=
    cascadeU_strictAnti h (Nat.lt_succ_self n)
  have := hstrict hlt
  simp only [CostModel.rFree]
  linarith

end Polymath.AtlasKO
