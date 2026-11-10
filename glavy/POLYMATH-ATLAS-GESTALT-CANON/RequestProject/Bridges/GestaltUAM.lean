/-
# Мост 5: Gestalt (UCC, T1–T5) ↔ UAM (конечные автоматы)

Когнитивный цикл UCC и автоматная часть UAM описывают одну и ту же
математическую структуру — детерминированную динамику на множестве состояний.
Мост делает соответствие явным и доказанным:

* `dfaSystem` — из детерминированного автомата и входного символа строится
  когнитивная система UCC (среда = переход автомата, наивный прогноз «ничего
  не изменится», скорость обучения = индикатор ошибки прогноза);
* `trajectory_eq_evalFrom` — траектория UCC совпадает с работой автомата на
  слове `aⁿ`;
* `dfa_revisits` — T5 (принудительное самостолкновение) для автомата:
  за `|Q| + 1` шагов состояние обязано повториться;
* `acceptChannel` и `no_distinction_language_trivial` — T1 для автомата:
  канал, не проводящий различия, соответствует тривиальному языку
  (пустому или всему множеству слов); и обратно
  (`drawsDistinction_of_nontrivial_language`);
* `returnLanguage_contextFree` — язык возвращений (слова, приводящие систему в
  исходное состояние — формальная запись «уробороса» T5) регулярен и, через
  мост `RegularContextFree`, контекстно-свободен.
-/
import Mathlib
import RequestProject.Gestalt.UCC
import RequestProject.Bridges.RegularContextFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PolymathAtlas.Bridges.GestaltUAM

open PolymathAtlas.Gestalt.UCC
open Classical

universe u

variable {α σ : Type u}

/-! ## Автомат как когнитивная система -/

/-- Когнитивная система, порождённая автоматом и фиксированным входным
символом: среда — переход автомата, прогноз — «состояние не изменится»,
скорость обучения — индикатор ошибки прогноза. -/
noncomputable def dfaSystem (M : DFA α σ) (a : α) : CognitiveSystem σ where
  env q := M.step q a
  predict q := q
  step q := M.step q a
  learningRate q := if M.step q a = q then 0 else 1
  learningRate_nonneg q := by
    by_cases h : M.step q a = q <;> simp [h]
  learningRate_eq_zero_iff q := by
    by_cases h : M.step q a = q
    · simp [h]
    · simp only [h, if_false]
      constructor
      · intro hzero; exact absurd hzero one_ne_zero
      · intro hq; exact absurd hq.symm h

/-- Траектория когнитивной системы автомата — это работа автомата на слове
`aⁿ`. -/
theorem trajectory_eq_evalFrom (M : DFA α σ) (a : α) (q : σ) :
    ∀ n : ℕ, (dfaSystem M a).trajectory q n = M.evalFrom q (List.replicate n a) := by
  intro n
  induction n generalizing q with
  | zero => simp [CognitiveSystem.trajectory, DFA.evalFrom]
  | succ n ih =>
      rw [CognitiveSystem.trajectory, Function.iterate_succ_apply,
        List.replicate_succ, DFA.evalFrom_cons]
      exact ih (M.step q a)

/-- **T5 для автомата.**  На однобуквенном входе состояние конечного автомата
обязано повториться за `|Q| + 1` шагов: «принудительное самостолкновение»
Gestalt — это принцип Дирихле на конечном множестве состояний. -/
theorem dfa_revisits [Fintype σ] (M : DFA α σ) (a : α) (q : σ) :
    ∃ i j, i < j ∧ j ≤ Fintype.card σ + 1 ∧
      M.evalFrom q (List.replicate i a) = M.evalFrom q (List.replicate j a) := by
  obtain ⟨i, j, hij, hjn, heq⟩ := t5_system_revisits (dfaSystem M a) q
  refine ⟨i, j, hij, by simpa [t5Bound] using hjn, ?_⟩
  rw [← trajectory_eq_evalFrom, ← trajectory_eq_evalFrom]
  exact heq

/-! ## T1 для автомата: различие и нетривиальность языка -/

/-- Канал приёмки: единственное различие, которое автомат проводит между
состояниями. -/
def acceptChannel (M : DFA α σ) : Channel σ Prop := fun q => q ∈ M.accept

/-- **T1 для автомата.**  Канал, не проводящий различия, не несёт информации:
язык автомата либо пуст, либо содержит все слова. -/
theorem no_distinction_language_trivial (M : DFA α σ)
    (h : ¬ DrawsDistinction (acceptChannel M)) :
    M.accepts = (∅ : Set (List α)) ∨ M.accepts = (Set.univ : Set (List α)) := by
  have hall : ∀ q p : σ, (q ∈ M.accept) = (p ∈ M.accept) := by
    intro q p
    by_contra hne
    exact h ⟨q, p, hne⟩
  by_cases hstart : M.start ∈ M.accept
  · refine Or.inr (Set.eq_univ_of_forall ?_)
    intro w
    show M.evalFrom M.start w ∈ M.accept
    rw [hall (M.evalFrom M.start w) M.start]
    exact hstart
  · refine Or.inl (Set.eq_empty_iff_forall_notMem.mpr ?_)
    intro w hw
    exact hstart (by rw [hall M.start (M.evalFrom M.start w)]; exact hw)

/-- Обратное направление T1: нетривиальный язык заставляет канал приёмки
проводить различие. -/
theorem drawsDistinction_of_nontrivial_language (M : DFA α σ)
    {x y : List α} (hx : x ∈ M.accepts) (hy : y ∉ M.accepts) :
    DrawsDistinction (acceptChannel M) := by
  refine ⟨M.evalFrom M.start x, M.evalFrom M.start y, ?_⟩
  intro hcontra
  simp only [acceptChannel, eq_iff_iff] at hcontra
  exact hy (hcontra.mp hx)

/-! ## Язык возвращений: уроборос как регулярный (и КС) язык -/

/-- Автомат возвращений: те же переходы, допускающее состояние одно — исходное. -/
def returnDFA (M : DFA α σ) (q : σ) : DFA α σ where
  step := M.step
  start := q
  accept := {q}

/-- Слово принимается автоматом возвращений ровно тогда, когда оно возвращает
систему в исходное состояние. -/
theorem mem_returnDFA_accepts (M : DFA α σ) (q : σ) (w : List α) :
    w ∈ (returnDFA M q).accepts ↔ M.evalFrom q w = q := by
  constructor
  · intro h
    have : (returnDFA M q).evalFrom q w = q := by simpa [returnDFA] using h
    simpa [returnDFA, DFA.evalFrom] using this
  · intro h
    show (returnDFA M q).evalFrom (returnDFA M q).start w ∈ (returnDFA M q).accept
    simpa [returnDFA, DFA.evalFrom] using h

/-- **Язык возвращений контекстно-свободен.**  Множество слов, возвращающих
систему в исходное состояние (формальная запись «замыкания уробороса» T5),
регулярно, а значит — по мосту `regular_subset_contextFree` — контекстно-свободно. -/
theorem returnLanguage_contextFree (M : DFA α σ) (q : σ) :
    ∃ (N : Type u) (g : UAM.ContextFree.Grammar N α),
      g.language = {w : List α | M.evalFrom q w = q} := by
  refine UAM.ContextFree.regular_subset_contextFree _ ⟨σ, returnDFA M q, ?_⟩
  ext w
  exact mem_returnDFA_accepts M q w

end PolymathAtlas.Bridges.GestaltUAM
