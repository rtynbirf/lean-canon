/-
# STEP-001: системы, метрики, ресурсы, рост

Формализация содержательного (математического) слоя документов кластера
STEP-001:

* CONCEPT-001 «System» — система как пара «элементы + взаимодействия»
  с границей;
* CONCEPT-002 «Metric» — вектор метрик и его норма;
* CONCEPT-003 «Resource» — входящий/исходящий потоки, нетто-поток и запас;
* MECHANISM-001 «Accumulation» — уравнение материального баланса;
* MECHANISM-002 «Reproduction and cooperation» — экспоненциальный рост
  популяции и выигрыш кооперации;
* INVARIANT-001 «Growth invariant» — рост метрики требует положительного
  нетто-потока ресурса.

**Найденная неточность источника.**  INVARIANT-001 записан как
эквивалентность «метрика растёт ⟺ существует ресурс с положительным
нетто-потоком».  Здесь доказано, что верна лишь одна импликация
(`growth_implies_some_positive_net`), а обратная неверна
(`some_positive_net_not_implies_growth`: один ресурс прибывает, другой
убывает сильнее); эквивалентность восстанавливается при дополнительном
условии неотрицательности всех нетто-потоков (`growth_iff_of_nonneg`).
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.AtlasKO

/-! ## CONCEPT-001: система -/

/-- Система: конечное множество элементов, отношение взаимодействия между ними
и граница — подмножество элементов, взаимодействующих с внешней средой. -/
structure Sys (α : Type) [DecidableEq α] where
  /-- Множество элементов `E`. -/
  elems : Finset α
  /-- Взаимодействия `R ⊆ E × E`. -/
  inter : Finset (α × α)
  /-- Элементы границы `B ⊆ E`. -/
  bnd : Finset α
  /-- Взаимодействия соединяют элементы системы. -/
  inter_sub : ∀ p ∈ inter, p.1 ∈ elems ∧ p.2 ∈ elems
  /-- Граница состоит из элементов системы. -/
  bnd_sub : bnd ⊆ elems

namespace Sys

variable {α : Type} [DecidableEq α] (S : Sys α)

/-- Число взаимодействий не превосходит числа упорядоченных пар элементов. -/
theorem inter_card_le : S.inter.card ≤ S.elems.card ^ 2 := by
  have hsub : S.inter ⊆ S.elems ×ˢ S.elems := by
    intro p hp
    have := S.inter_sub p hp
    simp [Finset.mem_product, this.1, this.2]
  calc S.inter.card ≤ (S.elems ×ˢ S.elems).card := Finset.card_le_card hsub
    _ = S.elems.card ^ 2 := by rw [Finset.card_product, sq]

/-- Плотность связности `ρ = |R| / |E|²` — доля реализованных взаимодействий. -/
noncomputable def density : ℝ :=
  if S.elems.card = 0 then 0 else (S.inter.card : ℝ) / (S.elems.card : ℝ) ^ 2

/-- Плотность связности лежит в отрезке `[0,1]`. -/
theorem density_mem_unitInterval : 0 ≤ S.density ∧ S.density ≤ 1 := by
  unfold density
  split
  · exact ⟨le_refl 0, by norm_num⟩
  · rename_i hne
    have hpos : (0 : ℝ) < (S.elems.card : ℝ) ^ 2 := by
      have : (0 : ℝ) < (S.elems.card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hne
      positivity
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hpos]
    exact_mod_cast S.inter_card_le

/-- Система замкнута, если её граница пуста. -/
def IsClosed : Prop := S.bnd = ∅

end Sys

/-! ## CONCEPT-002: вектор метрик -/

/-- Норма вектора метрик `‖M‖ = √(Σ mᵢ²)`. -/
noncomputable def metricNorm {n : ℕ} (M : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (M i) ^ 2)

/-- Норма вектора метрик неотрицательна. -/
theorem metricNorm_nonneg {n : ℕ} (M : Fin n → ℝ) : 0 ≤ metricNorm M :=
  Real.sqrt_nonneg _

/-- Норма равна нулю в точности тогда, когда все метрики нулевые. -/
theorem metricNorm_eq_zero_iff {n : ℕ} (M : Fin n → ℝ) :
    metricNorm M = 0 ↔ ∀ i, M i = 0 := by
  unfold metricNorm
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  constructor
  · intro h i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (M j))).1 h i
      (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  · intro h
    exact Finset.sum_eq_zero fun i _ => by rw [h i]; ring

/-- Покомпонентный рост неотрицательных метрик не уменьшает норму. -/
theorem metricNorm_mono {n : ℕ} {M N : Fin n → ℝ} (hM : ∀ i, 0 ≤ M i)
    (h : ∀ i, M i ≤ N i) : metricNorm M ≤ metricNorm N := by
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum fun i _ => by
    have := hM i
    nlinarith [h i, hM i]

/-! ## CONCEPT-003: ресурсы -/

/-- Потоки ресурсов: `k` видов ресурса, для каждого — входящий и исходящий поток. -/
structure Flows (k : ℕ) where
  /-- Входящий поток `R_in`. -/
  inflow : Fin k → ℝ
  /-- Исходящий поток `R_out`. -/
  outflow : Fin k → ℝ

/-- Нетто-поток `R_net = R_in - R_out` по каждому ресурсу. -/
def Flows.net {k : ℕ} (F : Flows k) (i : Fin k) : ℝ := F.inflow i - F.outflow i

/-- Запас ресурса: `R_stock(t+Δt) = R_stock(t) + R_net·Δt`. -/
def stock (s0 c dt : ℝ) : ℕ → ℝ
  | 0 => s0
  | n + 1 => stock s0 c dt n + c * dt

/-- Замкнутая форма запаса. -/
theorem stock_closed (s0 c dt : ℝ) (n : ℕ) : stock s0 c dt n = s0 + n * (c * dt) := by
  induction n with
  | zero => simp [stock]
  | succ n ih => simp [stock, ih]; ring

/-- При неотрицательном нетто-потоке запас не убывает. -/
theorem stock_monotone {s0 c dt : ℝ} (h : 0 ≤ c * dt) : Monotone (stock s0 c dt) := by
  intro a b hab
  rw [stock_closed, stock_closed]
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  nlinarith

/-- **Истощение запаса.**  При отрицательном нетто-потоке запас за конечное
число шагов уходит в минус: рост «за счёт запасов» не может длиться вечно. -/
theorem stock_exhausts {s0 c dt : ℝ} (h : c * dt < 0) : ∃ n : ℕ, stock s0 c dt n < 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (s0 / (-(c * dt)))
  refine ⟨n, ?_⟩
  rw [stock_closed]
  have hpos : 0 < -(c * dt) := by linarith
  have : s0 < n * (-(c * dt)) := by
    rw [div_lt_iff₀ hpos] at hn
    linarith
  nlinarith

/-! ## MECHANISM-001: накопление -/

/-- Дискретное уравнение материального баланса
`m(t+Δt) = m(t) + (R_in - R_out - R_dissipation)·Δt`. -/
def mass (m0 rIn rOut rDis dt : ℝ) : ℕ → ℝ :=
  stock m0 (rIn - rOut - rDis) dt

/-- Замкнутая форма баланса массы. -/
theorem mass_closed (m0 rIn rOut rDis dt : ℝ) (n : ℕ) :
    mass m0 rIn rOut rDis dt n = m0 + n * ((rIn - rOut - rDis) * dt) :=
  stock_closed _ _ _ n

/-- **Критерий роста.**  Масса строго растёт тогда и только тогда, когда
входящий поток превосходит сумму исходящего потока и потерь. -/
theorem mass_strictMono_iff {m0 rIn rOut rDis dt : ℝ} (hdt : 0 < dt) :
    StrictMono (mass m0 rIn rOut rDis dt) ↔ rOut + rDis < rIn := by
  constructor
  · intro h
    have h01 := h (Nat.lt_succ_self 0)
    rw [mass_closed, mass_closed] at h01
    simp at h01
    nlinarith
  · intro h a b hab
    rw [mass_closed, mass_closed]
    have hlt : (a : ℝ) < b := by exact_mod_cast hab
    have hc : 0 < (rIn - rOut - rDis) * dt := by nlinarith
    have := mul_lt_mul_of_pos_right hlt hc
    linarith

/-- В замкнутой системе без потоков масса постоянна. -/
theorem mass_const_of_no_flow (m0 dt : ℝ) (n : ℕ) : mass m0 0 0 0 dt n = m0 := by
  rw [mass_closed]; ring

/-! ## MECHANISM-002: воспроизводство и кооперация -/

/-- Экспоненциальная модель популяции `N(t) = N₀·exp((r_birth - r_death)·t)`. -/
noncomputable def pop (N0 rBirth rDeath t : ℝ) : ℝ :=
  N0 * Real.exp ((rBirth - rDeath) * t)

theorem pop_zero (N0 rBirth rDeath : ℝ) : pop N0 rBirth rDeath 0 = N0 := by
  simp [pop]

/-- Популяция растёт, если рождаемость превосходит смертность. -/
theorem pop_strictMono {N0 rBirth rDeath : ℝ} (hN : 0 < N0) (h : rDeath < rBirth) :
    StrictMono (pop N0 rBirth rDeath) := by
  intro a b hab
  have hr : 0 < rBirth - rDeath := by linarith
  have : (rBirth - rDeath) * a < (rBirth - rDeath) * b := by
    exact mul_lt_mul_of_pos_left hab hr
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 this) hN

/-- Популяция вымирает, если смертность превосходит рождаемость. -/
theorem pop_strictAnti {N0 rBirth rDeath : ℝ} (hN : 0 < N0) (h : rBirth < rDeath) :
    StrictAnti (pop N0 rBirth rDeath) := by
  intro a b hab
  have hr : rBirth - rDeath < 0 := by linarith
  have : (rBirth - rDeath) * b < (rBirth - rDeath) * a :=
    mul_lt_mul_of_neg_left hab hr
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 this) hN

/-- При равных рождаемости и смертности популяция постоянна. -/
theorem pop_const {N0 r : ℝ} (t : ℝ) : pop N0 r r t = N0 := by
  simp [pop]

/-- Совокупная производительность `n` агентов при эффективности кооперации `η`. -/
def coopOutput (n P eta : ℝ) : ℝ := n * P * eta

/-- Кооперация с эффективностью `η > 1` строго выгоднее независимой работы. -/
theorem coopOutput_gt {n P eta : ℝ} (hn : 0 < n) (hP : 0 < P) (heta : 1 < eta) :
    n * P < coopOutput n P eta := by
  unfold coopOutput
  have hnp : 0 < n * P := mul_pos hn hP
  nlinarith

/-- Предельное число агентов `n_max = R_in / (R_per_capita·(1 - overhead))`. -/
noncomputable def nMax (rIn rPerCapita overhead : ℝ) : ℝ :=
  rIn / (rPerCapita * (1 - overhead))

/-- **Найденная неточность источника.**  В напечатанной формуле множитель
`(1 - overhead)` стоит в знаменателе, поэтому предельное число агентов
*растёт* вместе с накладными расходами на координацию — что противоречит
смыслу самого механизма. -/
theorem nMax_increases_with_overhead {rIn rPerCapita o₁ o₂ : ℝ}
    (hIn : 0 < rIn) (hPc : 0 < rPerCapita) (h₂ : o₂ < 1) (h : o₁ < o₂) :
    nMax rIn rPerCapita o₁ < nMax rIn rPerCapita o₂ := by
  unfold nMax
  have hd₂ : 0 < rPerCapita * (1 - o₂) := by nlinarith
  have hd₁ : 0 < rPerCapita * (1 - o₁) := by nlinarith
  rw [div_lt_div_iff₀ hd₁ hd₂]
  nlinarith [mul_pos hIn hPc]

/-- Исправленная формула: доля `overhead` уходит на координацию, поэтому на
содержание агентов остаётся `R_in·(1 - overhead)`. -/
noncomputable def nMaxCorrected (rIn rPerCapita overhead : ℝ) : ℝ :=
  rIn * (1 - overhead) / rPerCapita

/-- **Издержки координации сокращают масштаб.**  В исправленной формуле чем
выше доля ресурсов, уходящих на координацию, тем меньше агентов может
содержать система. -/
theorem nMaxCorrected_antitone_in_overhead {rIn rPerCapita o₁ o₂ : ℝ}
    (hIn : 0 < rIn) (hPc : 0 < rPerCapita) (h : o₁ < o₂) :
    nMaxCorrected rIn rPerCapita o₂ < nMaxCorrected rIn rPerCapita o₁ := by
  unfold nMaxCorrected
  rw [div_lt_div_iff_of_pos_right hPc]
  nlinarith

/-! ## INVARIANT-001: инвариант роста -/

/-- **Рост требует ресурса.**  Если суммарный нетто-поток положителен, то
хотя бы по одному ресурсу вход строго превосходит выход. -/
theorem growth_implies_some_positive_net {k : ℕ} (F : Flows k)
    (h : 0 < ∑ i, F.net i) : ∃ i, 0 < F.net i := by
  by_contra hc
  push_neg at hc
  have : ∑ i, F.net i ≤ 0 :=
    Finset.sum_nonpos fun i _ => hc i
  linarith

/-- **Обратная импликация источника неверна.**  Положительный нетто-поток по
одному ресурсу не гарантирует роста: другой ресурс может убывать сильнее. -/
theorem some_positive_net_not_implies_growth :
    ∃ F : Flows 2, (∃ i, 0 < F.net i) ∧ ¬ (0 < ∑ i, F.net i) := by
  refine ⟨⟨fun i => if i = 0 then 1 else 0, fun i => if i = 0 then 0 else 2⟩, ⟨0, ?_⟩, ?_⟩
  · norm_num [Flows.net]
  · simp [Flows.net, Fin.sum_univ_two]

/-- **Исправленная формулировка INVARIANT-001.**  Если ни один ресурс не
убывает, эквивалентность источника восстанавливается. -/
theorem growth_iff_of_nonneg {k : ℕ} (F : Flows k) (hnn : ∀ i, 0 ≤ F.net i) :
    0 < ∑ i, F.net i ↔ ∃ i, 0 < F.net i := by
  constructor
  · exact growth_implies_some_positive_net F
  · rintro ⟨i, hi⟩
    exact Finset.sum_pos' (fun j _ => hnn j) ⟨i, Finset.mem_univ i, hi⟩

/-- **Нет вечного роста без притока.**  Если нетто-поток неположителен, запас
никогда не превосходит начального: долгосрочный рост требует `R_in > R_out`. -/
theorem no_perpetual_growth_without_inflow {s0 c dt : ℝ} (hdt : 0 ≤ dt) (hc : c ≤ 0)
    (n : ℕ) : stock s0 c dt n ≤ s0 := by
  rw [stock_closed]
  have : c * dt ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hdt
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end Polymath.AtlasKO
