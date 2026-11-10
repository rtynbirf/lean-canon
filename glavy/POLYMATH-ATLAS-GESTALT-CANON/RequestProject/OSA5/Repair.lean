/-
# OSA-5.0 — многошаговый ремонт: поиск, корректность, полнота, минимальность

Находка аудита OSA-4.1 (критический вопрос 4): вердикт `REPAIR` **не**
гарантирует одношаговой починки — критерий `repairFor` не проверяет
предусловия самого оператора ремонта, а усиленный критерий `repairForSound`
на сценарии `MODEL` из пустого состояния даёт `false`, хотя двухшаговая
починка `MEASURE → CHECK_SUFFICIENCY` существует
(`Polymath.OSA4.repair_not_one_step_complete`).

Этот модуль закрывает пункт «OSA-5.x: верификация многошаговых сценариев
ремонта»:

* `chainPred` — предикат ядра, доказанность которого **равносильна**
  исполнимости всей цепочки и достижению цели (`chainPred_true_iff`); тем
  самым «починить цепочку» сводится к «сделать один предикат доказанным»;
* `searchRepair` — поиск последовательности исполнимых операторов реестра,
  тотальный по построению (структурная рекурсия по топливу), поэтому
  **зацикливание невозможно**;
* корректность (`searchRepair_sound`): найденный план исполним шаг за шагом,
  состоит из операторов реестра, не длиннее топлива и доказанно достигает цели;
* полнота (`searchRepair_complete`): если починка длины ≤ n существует, поиск
  с топливом n её находит; отсюда точный критерий `searchRepair_isSome_iff`;
* минимальность (`minRepair_length_le`): итеративное углубление возвращает
  план минимальной длины;
* **repair completeness** (`repaired_chain_compiles_pass`): после вставки
  найденного плана компилятор выдаёт `PASS`;
* тесты T21–T25 — вычисленные, а не объявленные вердикты.
-/
import RequestProject.OSA4.Criteria
import RequestProject.OSA4.TortureSet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Polymath.OSA5

open Polymath.OSA4

/-! ## Условие исполнимости цепочки как предикат ядра -/

/-- Требование авторизации оператора, записанное как предикат ядра. -/
def authPred (o : Op) : Pred :=
  if o.requiresAuth then .factExists (authFact o) else .ctrue

theorem eval_authPred_iff (s : KState) (o : Op) :
    eval s (authPred o) = .TRUE_KNOWN ↔ authStatus s o = .TRUE_KNOWN := by
  unfold authPred authStatus
  by_cases h : o.requiresAuth
  · simp [h, eval]
  · simp [h, eval]

/-- Предикат «цепочка исполнима и цель достигается», выраженный в языке ядра
через обратный трансформер предикатов. -/
def chainPred : List Op → Pred → Pred
  | [], goal => goal
  | o :: t, goal =>
      .pand (conj o.requires) (.pand (authPred o) (wp o (chainPred t goal)))

/-- **Точная характеризация.**  Предикат `chainPred ops goal` доказан в
состоянии `s` тогда и только тогда, когда цепочка `ops` исполнима из `s`
шаг за шагом и в конечном состоянии цель доказана. -/
theorem chainPred_true_iff :
    ∀ (ops : List Op) (s : KState) (goal : Pred),
      eval s (chainPred ops goal) = .TRUE_KNOWN ↔
        chainEnabled ops s ∧ eval (execChain ops s) goal = .TRUE_KNOWN := by
  intro ops
  induction ops with
  | nil => intro s goal; simp [chainPred, chainEnabled, execChain]
  | cons o t ih =>
      intro s goal
      have hstep : eval s (chainPred (o :: t) goal) = .TRUE_KNOWN ↔
          (eval s (conj o.requires) = .TRUE_KNOWN ∧ eval s (authPred o) = .TRUE_KNOWN ∧
            eval (o.exec s) (chainPred t goal) = .TRUE_KNOWN) := by
        rw [chainPred, eval, PT.and_eq_true_iff, eval, PT.and_eq_true_iff,
          ← eval_exec_eq_eval_wp]
      rw [hstep, ih (o.exec s) goal, eval_authPred_iff]
      simp only [chainEnabled, execChain_cons, execAllowed, Op.enabled]
      tauto

/-! ## Поиск многошаговой починки -/

/-- Перебор кандидатов первого шага: берётся первый исполнимый оператор
реестра, для которого продолжение `rec` находит план. -/
def searchList (rec : KState → Option (List Op)) (s : KState) :
    List Op → Option (List Op)
  | [] => none
  | r :: t =>
      if execAllowed s r then
        match rec (r.exec s) with
        | some p => some (r :: p)
        | none => searchList rec s t
      else searchList rec s t

/-- Поиск плана ремонта с ограниченным числом шагов (топливом).  Функция
тотальна: рекурсия структурна по топливу, поэтому последовательность
попыток **не может зациклиться**. -/
def searchRepair (reg : List Op) (goal : Pred) : ℕ → KState → Option (List Op)
  | 0, s => if eval s goal = .TRUE_KNOWN then some [] else none
  | n + 1, s =>
      if eval s goal = .TRUE_KNOWN then some []
      else searchList (fun s' => searchRepair reg goal n s') s reg

/-! ### Корректность -/

theorem searchList_sound (rec : KState → Option (List Op)) (s : KState) :
    ∀ (l : List Op) (p : List Op), searchList rec s l = some p →
      ∃ r ∈ l, ∃ q, execAllowed s r ∧ rec (r.exec s) = some q ∧ p = r :: q := by
  intro l
  induction l with
  | nil => intro p h; exact absurd h (by simp [searchList])
  | cons r t ih =>
      intro p h
      rw [searchList] at h
      by_cases hr : execAllowed s r
      · rw [if_pos hr] at h
        cases hrec : rec (r.exec s) with
        | none =>
            rw [hrec] at h
            obtain ⟨r', hr', q, h₁, h₂, h₃⟩ := ih p h
            exact ⟨r', List.mem_cons_of_mem _ hr', q, h₁, h₂, h₃⟩
        | some q =>
            rw [hrec] at h
            exact ⟨r, List.mem_cons_self, q, hr, hrec, by simpa using h.symm⟩
      · rw [if_neg hr] at h
        obtain ⟨r', hr', q, h₁, h₂, h₃⟩ := ih p h
        exact ⟨r', List.mem_cons_of_mem _ hr', q, h₁, h₂, h₃⟩

/-- **Корректность поиска.**  Найденный план исполним из `s` шаг за шагом,
состоит из операторов реестра, достигает цели и не длиннее топлива. -/
theorem searchRepair_sound (reg : List Op) (goal : Pred) :
    ∀ (n : ℕ) (s : KState) (p : List Op), searchRepair reg goal n s = some p →
      chainEnabled p s ∧ eval (execChain p s) goal = .TRUE_KNOWN ∧
        (∀ o ∈ p, o ∈ reg) ∧ p.length ≤ n := by
  intro n
  induction n with
  | zero =>
      intro s p h
      rw [searchRepair] at h
      by_cases hg : eval s goal = .TRUE_KNOWN
      · rw [if_pos hg] at h
        have hp : p = [] := by simpa using h.symm
        subst hp
        exact ⟨trivial, hg, by simp, by simp⟩
      · rw [if_neg hg] at h; exact absurd h (by simp)
  | succ n ih =>
      intro s p h
      rw [searchRepair] at h
      by_cases hg : eval s goal = .TRUE_KNOWN
      · rw [if_pos hg] at h
        have hp : p = [] := by simpa using h.symm
        subst hp
        exact ⟨trivial, hg, by simp, by simp⟩
      · rw [if_neg hg] at h
        obtain ⟨r, hr, q, hallow, hrec, rfl⟩ := searchList_sound _ s reg p h
        obtain ⟨h₁, h₂, h₃, h₄⟩ := ih (r.exec s) q hrec
        refine ⟨⟨hallow, h₁⟩, by simpa using h₂, ?_, by simpa using h₄⟩
        intro o ho
        rcases List.mem_cons.mp ho with rfl | ho'
        · exact hr
        · exact h₃ o ho'

/-! ### Полнота -/

theorem searchList_isSome_of_witness (rec : KState → Option (List Op)) (s : KState) :
    ∀ (l : List Op), (∃ r ∈ l, execAllowed s r ∧ (rec (r.exec s)).isSome) →
      (searchList rec s l).isSome := by
  intro l
  induction l with
  | nil => rintro ⟨r, hr, -⟩; exact absurd hr (by simp)
  | cons r t ih =>
      rintro ⟨r', hr', hallow', hsome'⟩
      rw [searchList]
      by_cases hr : execAllowed s r
      · rw [if_pos hr]
        cases hrec : rec (r.exec s) with
        | some q => simp
        | none =>
            refine ih ⟨r', ?_, hallow', hsome'⟩
            rcases List.mem_cons.mp hr' with rfl | h
            · rw [hrec] at hsome'; simp at hsome'
            · exact h
      · rw [if_neg hr]
        refine ih ⟨r', ?_, hallow', hsome'⟩
        rcases List.mem_cons.mp hr' with rfl | h
        · exact absurd hallow' hr
        · exact h

/-- **Полнота поиска.**  Если починка длины не более `n` существует в
реестре, поиск с топливом `n` её находит. -/
theorem searchRepair_complete (reg : List Op) (goal : Pred) :
    ∀ (n : ℕ) (s : KState) (p : List Op), chainEnabled p s →
      eval (execChain p s) goal = .TRUE_KNOWN → (∀ o ∈ p, o ∈ reg) →
      p.length ≤ n → (searchRepair reg goal n s).isSome := by
  intro n
  induction n with
  | zero =>
      intro s p hchain hgoal _ hlen
      have hp : p = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      subst hp
      rw [searchRepair, if_pos (by simpa [execChain] using hgoal)]
      simp
  | succ n ih =>
      intro s p hchain hgoal hmem hlen
      rw [searchRepair]
      by_cases hg : eval s goal = .TRUE_KNOWN
      · rw [if_pos hg]; simp
      · rw [if_neg hg]
        cases p with
        | nil => exact absurd (by simpa [execChain] using hgoal) hg
        | cons r q =>
            obtain ⟨hallow, hq⟩ := hchain
            refine searchList_isSome_of_witness _ s reg
              ⟨r, hmem r List.mem_cons_self, hallow, ?_⟩
            exact ih (r.exec s) q hq (by simpa using hgoal)
              (fun o ho => hmem o (List.mem_cons_of_mem _ ho))
              (by simpa using Nat.succ_le_succ_iff.mp hlen)

/-- **Точный критерий.**  Поиск с топливом `n` успешен тогда и только тогда,
когда существует исполнимая починка длины не более `n`. -/
theorem searchRepair_isSome_iff (reg : List Op) (goal : Pred) (n : ℕ) (s : KState) :
    (searchRepair reg goal n s).isSome ↔
      ∃ p : List Op, chainEnabled p s ∧ eval (execChain p s) goal = .TRUE_KNOWN ∧
        (∀ o ∈ p, o ∈ reg) ∧ p.length ≤ n := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := searchRepair_sound reg goal n s p hp
    exact ⟨p, h₁, h₂, h₃, h₄⟩
  · rintro ⟨p, h₁, h₂, h₃, h₄⟩
    exact searchRepair_complete reg goal n s p h₁ h₂ h₃ h₄

/-- **Монотонность по топливу.**  Увеличение бюджета не может потерять
найденную починку. -/
theorem searchRepair_mono (reg : List Op) (goal : Pred) {n m : ℕ} (h : n ≤ m)
    (s : KState) (hn : (searchRepair reg goal n s).isSome) :
    (searchRepair reg goal m s).isSome := by
  obtain ⟨p, h₁, h₂, h₃, h₄⟩ := (searchRepair_isSome_iff reg goal n s).mp hn
  exact (searchRepair_isSome_iff reg goal m s).mpr ⟨p, h₁, h₂, h₃, le_trans h₄ h⟩

/-! ### Минимальность: итеративное углубление -/

/-- Итеративное углубление: попытки с топливом `k`, `k+1`, …, `k+b`. -/
def deepen (reg : List Op) (goal : Pred) (s : KState) (k : ℕ) :
    ℕ → Option (List Op)
  | 0 => searchRepair reg goal k s
  | b + 1 =>
      match searchRepair reg goal k s with
      | some p => some p
      | none => deepen reg goal s (k + 1) b

/-- Поиск минимальной починки с бюджетом `n`. -/
def minRepair (reg : List Op) (goal : Pred) (n : ℕ) (s : KState) : Option (List Op) :=
  deepen reg goal s 0 n

theorem deepen_spec (reg : List Op) (goal : Pred) (s : KState) :
    ∀ (b k : ℕ) (p : List Op), deepen reg goal s k b = some p →
      ∃ j, k ≤ j ∧ searchRepair reg goal j s = some p ∧
        ∀ i, k ≤ i → i < j → searchRepair reg goal i s = none := by
  intro b
  induction b with
  | zero =>
      intro k p h
      exact ⟨k, le_refl k, h, by intro i h₁ h₂; omega⟩
  | succ b ih =>
      intro k p h
      rw [deepen] at h
      cases hk : searchRepair reg goal k s with
      | some q =>
          rw [hk] at h
          refine ⟨k, le_refl k, ?_, by intro i h₁ h₂; omega⟩
          rw [hk]
          exact h
      | none =>
          rw [hk] at h
          obtain ⟨j, hj, hsome, hmin⟩ := ih (k + 1) p h
          refine ⟨j, by omega, hsome, ?_⟩
          intro i h₁ h₂
          rcases Nat.eq_or_lt_of_le h₁ with rfl | h₃
          · exact hk
          · exact hmin i (by omega) h₂

theorem deepen_isSome (reg : List Op) (goal : Pred) (s : KState) :
    ∀ (b k j : ℕ), k ≤ j → j ≤ k + b → (searchRepair reg goal j s).isSome →
      (deepen reg goal s k b).isSome := by
  intro b
  induction b with
  | zero =>
      intro k j h₁ h₂ h₃
      have : j = k := by omega
      subst this
      exact h₃
  | succ b ih =>
      intro k j h₁ h₂ h₃
      rw [deepen]
      cases hk : searchRepair reg goal k s with
      | some q => simp
      | none =>
          have hjk : k ≠ j := by
            intro h; subst h; rw [hk] at h₃; simp at h₃
          exact ih (k + 1) j (by omega) (by omega) h₃

/-- **Минимальность.**  Если исполнимая починка длины не более `n`
существует, итеративное углубление её находит, и найденный план не длиннее
любой другой починки, укладывающейся в бюджет. -/
theorem minRepair_length_le (reg : List Op) (goal : Pred) (n : ℕ) (s : KState)
    {p q : List Op} (hp : minRepair reg goal n s = some p)
    (h₁ : chainEnabled q s) (h₂ : eval (execChain q s) goal = .TRUE_KNOWN)
    (h₃ : ∀ o ∈ q, o ∈ reg) :
    p.length ≤ q.length := by
  obtain ⟨j, -, hj, hmin⟩ := deepen_spec reg goal s n 0 p hp
  have hq : (searchRepair reg goal q.length s).isSome :=
    searchRepair_complete reg goal q.length s q h₁ h₂ h₃ (le_refl _)
  have hjq : j ≤ q.length := by
    by_contra hcon
    have hnone := hmin q.length (Nat.zero_le _) (by omega)
    rw [hnone] at hq
    simp at hq
  have := (searchRepair_sound reg goal j s p hj).2.2.2
  omega

/-- Если починка в бюджете существует, минимальный поиск её выдаёт. -/
theorem minRepair_isSome (reg : List Op) (goal : Pred) (n : ℕ) (s : KState)
    {q : List Op} (h₁ : chainEnabled q s)
    (h₂ : eval (execChain q s) goal = .TRUE_KNOWN)
    (h₃ : ∀ o ∈ q, o ∈ reg) (h₄ : q.length ≤ n) :
    (minRepair reg goal n s).isSome :=
  deepen_isSome reg goal s n 0 q.length (Nat.zero_le _) (by simpa using h₄)
    (searchRepair_complete reg goal q.length s q h₁ h₂ h₃ (le_refl _))

/-! ## Repair completeness: после починки компилятор выдаёт PASS -/

theorem chainEnabled_append :
    ∀ (p t : List Op) (s : KState),
      chainEnabled (p ++ t) s ↔ chainEnabled p s ∧ chainEnabled t (execChain p s) := by
  intro p
  induction p with
  | nil => intro t s; simp [chainEnabled, execChain]
  | cons o p ih =>
      intro t s
      simp only [List.cons_append, chainEnabled, execChain_cons, ih]
      tauto

theorem execChain_append (p t : List Op) (s : KState) :
    execChain (p ++ t) s = execChain t (execChain p s) := by
  simp [execChain, List.foldl_append]

/-- Обратная к `epiPass_pass_sound`: исполнимая цепочка, достигающая цели,
проходит эпистемический проход. -/
theorem epiPass_pass_of_chainEnabled (reg : List Op) :
    ∀ (ops : List Op) (s : KState) (goal : Pred), chainEnabled ops s →
      eval (execChain ops s) goal = .TRUE_KNOWN →
      epiPass reg ops s goal = ⟨.PASS, none, none⟩ := by
  intro ops
  induction ops with
  | nil =>
      intro s goal _ hgoal
      rw [epiPass]
      simp only [execChain_nil] at hgoal
      rw [hgoal]
  | cons o t ih =>
      intro s goal hchain hgoal
      obtain ⟨⟨hreq, hauth⟩, hrest⟩ := hchain
      rw [epiPass]
      rw [show eval s (conj o.requires) = PT.TRUE_KNOWN from hreq]
      rw [hauth]
      exact ih (o.exec s) goal hrest (by simpa using hgoal)

/-- Исполнимая цепочка, достигающая цели и проходящая структурные проверки,
компилируется в `PASS`. -/
theorem compile_pass_of_chainEnabled (sc : Scenario)
    (hu : unknownOperator sc.registry sc.chain = none)
    (hd : doubleConsume [] sc.chain = none)
    (hl : livenessViolation sc.goal sc.chain = none)
    (hchain : chainEnabled sc.chain sc.init)
    (hgoal : eval (execChain sc.chain sc.init) sc.goal = .TRUE_KNOWN) :
    compile sc = ⟨.PASS, none, none⟩ := by
  rw [compile, hu, hd, hl]
  exact epiPass_pass_of_chainEnabled sc.registry sc.chain sc.init sc.goal hchain hgoal

/-- **Repair completeness.**  Если многошаговый поиск нашёл план `p` для
условия исполнимости цепочки `chain`, то составная цепочка `p ++ chain`
исполнима и — при пройденных структурных проверках — компилируется в `PASS`.
Это ровно то, чего не даёт одношаговый критерий `repairFor`. -/
theorem repaired_chain_compiles_pass (reg : List Op) (s : KState)
    (chain : List Op) (goal : Pred) (n : ℕ) (p : List Op)
    (hp : searchRepair reg (chainPred chain goal) n s = some p)
    (hu : unknownOperator reg (p ++ chain) = none)
    (hd : doubleConsume [] (p ++ chain) = none)
    (hl : livenessViolation goal (p ++ chain) = none) :
    compile ⟨reg, s, p ++ chain, goal⟩ = ⟨.PASS, none, none⟩ := by
  obtain ⟨hchain, hgoal, -, -⟩ := searchRepair_sound reg (chainPred chain goal) n s p hp
  obtain ⟨hce, hgl⟩ := (chainPred_true_iff chain (execChain p s) goal).mp hgoal
  refine compile_pass_of_chainEnabled ⟨reg, s, p ++ chain, goal⟩ hu hd hl ?_ ?_
  · exact (chainEnabled_append p chain s).mpr ⟨hchain, hce⟩
  · rw [execChain_append]; exact hgl

/-! ## Тесты T21–T25 (многошаговый ремонт) -/

/-- Цель сценария T01/T14: цепочка `[MODEL]` должна исполниться и доказать
`Model`. -/
def modelGoal : Pred := chainPred (MODEL :: []) (.factExists "Model")

/-- **T21.**  Одношаговой починки не существует: поиск с топливом 1 из
пустого состояния терпит неудачу. -/
theorem T21_no_one_step_repair :
    searchRepair registry modelGoal 1 s0 = none := by
  rfl

/-- **T22.**  Двухшаговая починка существует и найдена: план
`MEASURE → CHECK_SUFFICIENCY`. -/
theorem T22_two_step_repair :
    searchRepair registry modelGoal 2 s0 = some [MEASURE, CHECK_SUFFICIENCY] := by
  rfl

/-- **T23.**  Найденный план, вставленный перед цепочкой, доводит сценарий до
`PASS` — вычислением компилятора. -/
theorem T23_repaired_pass :
    compile ⟨registry, s0, [MEASURE, CHECK_SUFFICIENCY] ++ (MODEL :: []),
      .factExists "Model"⟩ = ⟨.PASS, none, none⟩ := by
  decide

/-- **T24.**  Итеративное углубление выдаёт план минимальной длины: с
бюджетом 4 возвращается тот же двухшаговый план. -/
theorem T24_minimal_plan :
    minRepair registry modelGoal 4 s0 = some [MEASURE, CHECK_SUFFICIENCY] := by
  rfl

/-- **T25.**  Недостижимая цель: починки нет ни при каком бюджете в пределах
проверки — поиск честно возвращает `none`, а не выдумывает план. -/
theorem T25_no_repair_for_unreachable :
    searchRepair registry (.factExists "Teleported") 3 s0 = none := by
  rfl

/-- Итог слоя OSA-5: многошаговый ремонт корректен, полон, минимален и
доводит сценарий до `PASS`; тесты T21–T25 пройдены. -/
theorem osa5_multistep_repair_report :
    (∀ (reg : List Op) (goal : Pred) (n : ℕ) (s : KState) (p : List Op),
        searchRepair reg goal n s = some p →
        chainEnabled p s ∧ eval (execChain p s) goal = .TRUE_KNOWN ∧
          (∀ o ∈ p, o ∈ reg) ∧ p.length ≤ n) ∧
    (∀ (reg : List Op) (goal : Pred) (n : ℕ) (s : KState),
        (searchRepair reg goal n s).isSome ↔
          ∃ p : List Op, chainEnabled p s ∧ eval (execChain p s) goal = .TRUE_KNOWN ∧
            (∀ o ∈ p, o ∈ reg) ∧ p.length ≤ n) ∧
    searchRepair registry modelGoal 1 s0 = none ∧
    searchRepair registry modelGoal 2 s0 = some [MEASURE, CHECK_SUFFICIENCY] ∧
    compile ⟨registry, s0, [MEASURE, CHECK_SUFFICIENCY] ++ (MODEL :: []),
      .factExists "Model"⟩ = ⟨.PASS, none, none⟩ ∧
    minRepair registry modelGoal 4 s0 = some [MEASURE, CHECK_SUFFICIENCY] ∧
    searchRepair registry (.factExists "Teleported") 3 s0 = none :=
  ⟨fun reg goal n s p h => searchRepair_sound reg goal n s p h,
   fun reg goal n s => searchRepair_isSome_iff reg goal n s,
   T21_no_one_step_repair, T22_two_step_repair, T23_repaired_pass,
   T24_minimal_plan, T25_no_repair_for_unreachable⟩

end Polymath.OSA5
