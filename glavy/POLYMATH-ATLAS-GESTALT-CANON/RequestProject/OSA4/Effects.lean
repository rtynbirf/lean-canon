/-
# OSA-4.0 — эффекты, авторизация и эпистемическая честность

Формализация законов LAW-008 (Effect Monotonicity / Effect Monoid),
LAW-009 (Epistemic Non-Overclaim) и LAW-011 (Effect Authorization Soundness)
кодекса OSA-4.0.

Ключевая ремарка кодекса: агрегация эффектов и авторизация — **разные**
вещи; поэтому агрегация здесь чисто алгебраическая (коммутативный
идемпотентный моноид уровней эффекта), а авторизация — отдельное условие
исполнения с трёхзначным вердиктом (`FALSE_KNOWN → REJECT`,
`UNKNOWN → UNDECIDABLE`).
-/
import RequestProject.OSA4.Kernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-! ## LAW-008 — алгебра агрегации эффектов -/

namespace EffectLevel

/-- Агрегация двух уровней эффекта: уровень с наибольшим рангом
(`EffectLevel.rank`). -/
def join (a b : EffectLevel) : EffectLevel := if a.rank ≤ b.rank then b else a

theorem join_comm (a b : EffectLevel) : join a b = join b a := by
  revert a b; decide

theorem join_assoc (a b c : EffectLevel) : join (join a b) c = join a (join b c) := by
  revert a b c; decide

theorem join_idem (a : EffectLevel) : join a a = a := by cases a <;> rfl

@[simp] theorem join_E0 (a : EffectLevel) : join a .E0 = a := by cases a <;> rfl

@[simp] theorem E0_join (a : EffectLevel) : join .E0 a = a := by cases a <;> rfl

/-- Суммарный эффект списка операторов. -/
def aggregate (l : List EffectLevel) : EffectLevel := l.foldl join .E0

@[simp] theorem aggregate_nil : aggregate [] = .E0 := rfl

private theorem foldl_join_start (l : List EffectLevel) :
    ∀ x : EffectLevel, l.foldl join x = join x (l.foldl join .E0) := by
  induction l with
  | nil => intro x; simp
  | cons a t ih =>
      intro x
      simp only [List.foldl_cons]
      rw [ih (join x a), ih (join .E0 a), E0_join, join_assoc]

theorem aggregate_cons (a : EffectLevel) (l : List EffectLevel) :
    aggregate (a :: l) = join a (aggregate l) := by
  simpa [aggregate, List.foldl_cons] using foldl_join_start l (join .E0 a)

/-- **LAW-008 (Effect Monoid Associativity).**  Суммарный эффект графа не
зависит от того, как операторы сгруппированы. -/
theorem aggregate_append (l₁ l₂ : List EffectLevel) :
    aggregate (l₁ ++ l₂) = join (aggregate l₁) (aggregate l₂) := by
  induction l₁ with
  | nil => simp [aggregate]
  | cons a t ih => rw [List.cons_append, aggregate_cons, ih, aggregate_cons, join_assoc]

/-- Суммарный эффект не зависит и от порядка операторов. -/
theorem aggregate_perm {l₁ l₂ : List EffectLevel} (h : l₁.Perm l₂) :
    aggregate l₁ = aggregate l₂ := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [aggregate_cons, aggregate_cons, ih]
  | swap a b l => rw [aggregate_cons, aggregate_cons, aggregate_cons, aggregate_cons,
      ← join_assoc, ← join_assoc, join_comm a b]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- Уровень эффекта не превосходит агрегата с любым другим уровнем. -/
theorem rank_le_join (a b : EffectLevel) : a.rank ≤ (join a b).rank := by
  revert a b; decide

/-- Агрегация монотонна: ранг агрегата не меньше ранга каждого слагаемого. -/
theorem le_aggregate_cons (a : EffectLevel) (l : List EffectLevel) :
    a.rank ≤ (aggregate (a :: l)).rank := by
  rw [aggregate_cons]; exact rank_le_join a _

end EffectLevel

/-- Политика эффектов: максимально допустимый уровень. -/
structure EffectPolicy where
  /-- Верхняя граница уровня эффекта. -/
  maxLevel : EffectLevel
  deriving DecidableEq, Repr, Inhabited

/-- Композиция соответствует политике эффектов. -/
def EffectPolicy.allows (p : EffectPolicy) (l : List EffectLevel) : Bool :=
  (EffectLevel.aggregate l).rank ≤ p.maxLevel.rank

/-- Проверка политики не зависит от группировки операторов (следствие
LAW-008). -/
theorem EffectPolicy.allows_append_comm (p : EffectPolicy) (l₁ l₂ : List EffectLevel) :
    p.allows (l₁ ++ l₂) = p.allows (l₂ ++ l₁) := by
  simp only [allows, EffectLevel.aggregate_append, EffectLevel.join_comm]

/-! ## LAW-011 — авторизация эффекта -/

/-- Факт-токен авторизации для оператора. -/
def authFact (o : Op) : FactId := "AUTH::" ++ o.name

/-- Эпистемический статус авторизации оператора в состоянии. -/
def authStatus (s : KState) (o : Op) : PT :=
  if o.requiresAuth then s.factStatus (authFact o) else .TRUE_KNOWN

/-- Вердикт компилятора. -/
inductive Verdict
  /-- Композиция корректна. -/
  | PASS
  /-- Композиция отвергается. -/
  | REJECT
  /-- Композиция чинится вставкой оператора. -/
  | REPAIR
  /-- Данных недостаточно для решения. -/
  | UNDECIDABLE
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Вердикт по авторизации: доказано отсутствие прав — REJECT, нет данных —
UNDECIDABLE (правило LAW-011 кодекса). -/
def authVerdict (s : KState) (o : Op) : Verdict :=
  match authStatus s o with
  | .TRUE_KNOWN => .PASS
  | .FALSE_KNOWN => .REJECT
  | .UNKNOWN => .UNDECIDABLE
  | .CONFLICT => .REJECT

/-- Исполнение оператора разрешено: предусловия доказаны и авторизация
получена. -/
def execAllowed (s : KState) (o : Op) : Prop :=
  o.enabled s ∧ authStatus s o = .TRUE_KNOWN

instance (s : KState) (o : Op) : Decidable (execAllowed s o) := by
  unfold execAllowed; infer_instance

/-- **LAW-011 (Effect Authorization Soundness).**  `Exec(Op,S) ⇒ Authorized(S,Op)`:
исполнение возможно только при доказанной авторизации. -/
theorem law011_exec_implies_authorized {s : KState} {o : Op} (h : execAllowed s o) :
    authStatus s o = .TRUE_KNOWN := h.2

/-- Оператору, не требующему авторизации, она и не нужна. -/
theorem authStatus_of_not_requiresAuth {s : KState} {o : Op} (h : o.requiresAuth = false) :
    authStatus s o = .TRUE_KNOWN := by simp [authStatus, h]

/-- Доказанное отсутствие прав даёт REJECT. -/
theorem law011_reject {s : KState} {o : Op} (h : authStatus s o = .FALSE_KNOWN) :
    authVerdict s o = .REJECT := by simp [authVerdict, h]

/-- Отсутствие данных об авторизации даёт UNDECIDABLE, а не REJECT. -/
theorem law011_undecidable {s : KState} {o : Op} (h : authStatus s o = .UNKNOWN) :
    authVerdict s o = .UNDECIDABLE := by simp [authVerdict, h]

/-- Оператор с эффектом, требующим авторизации, не исполняется в состоянии,
где токен неизвестен. -/
theorem no_exec_without_token {s : KState} {o : Op} (hreq : o.requiresAuth = true)
    (h : s.factStatus (authFact o) = .UNKNOWN) : ¬ execAllowed s o := by
  rintro ⟨-, hauth⟩
  rw [authStatus, if_pos hreq, h] at hauth
  exact PT.noConfusion hauth

/-- Вставка оператора авторизации чинит композицию: после исполнения
оператора, производящего токен, исполнение становится разрешённым. -/
theorem authorize_repairs {s : KState} {a o : Op}
    (hprod : authFact o ∈ a.produces) (henab : o.enabled (a.exec s)) :
    execAllowed (a.exec s) o := by
  refine ⟨henab, ?_⟩
  by_cases hreq : o.requiresAuth
  · rw [authStatus, if_pos hreq, factStatus_exec_produces a s hprod]
  · simp [authStatus, hreq]

/-! ## LAW-009 — запрет эпистемического самоповышения -/

/-- Шаг переноса неопределённости: вход, выход и наличие явно порождённого
свидетельства (`GEN(Evidence)` / validation).  Неопределённость выражена в
сотых долях. -/
structure UStep where
  /-- Неопределённость на входе. -/
  uIn : ℕ
  /-- Неопределённость на выходе. -/
  uOut : ℕ
  /-- Оператор явно породил свидетельство/валидацию. -/
  evidence : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Контракт шага: без явного свидетельства неопределённость не уменьшается. -/
def UStep.honest (s : UStep) : Prop := s.evidence = false → s.uIn ≤ s.uOut

instance (s : UStep) : Decidable s.honest := by unfold UStep.honest; infer_instance

/-- Цепочка шагов согласована, если выход каждого шага — вход следующего. -/
def UChain : List UStep → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => a.uOut = b.uIn ∧ UChain (b :: t)

/-- **LAW-009 (Epistemic Non-Overclaim).**  Если ни один шаг цепочки не
порождает свидетельства и все шаги честны, итоговая неопределённость не
меньше исходной: уверенность нельзя «отмыть» композицией. -/
theorem law009_no_overclaim :
    ∀ (l : List UStep) (a : UStep), UChain (a :: l) →
      (∀ s ∈ a :: l, s.honest) → (∀ s ∈ a :: l, s.evidence = false) →
      a.uIn ≤ (List.getLast (a :: l) (by simp)).uOut := by
  intro l
  induction l with
  | nil => intro a _ hh he; simpa using hh a (by simp) (he a (by simp))
  | cons b t ih =>
      intro a hchain hh he
      obtain ⟨hlink, hrest⟩ := hchain
      have h₁ : a.uIn ≤ a.uOut := hh a (by simp) (he a (by simp))
      have h₂ : b.uIn ≤ (List.getLast (b :: t) (by simp)).uOut :=
        ih b hrest (fun s hs => hh s (by simp [hs])) (fun s hs => he s (by simp [hs]))
      have hlast : List.getLast (a :: b :: t) (by simp) = List.getLast (b :: t) (by simp) :=
        List.getLast_cons (by simp)
      rw [hlast]
      omega

/-- Уменьшить неопределённость без свидетельства нельзя: такой шаг нечестен. -/
theorem uncertainty_drop_needs_evidence {s : UStep} (h : s.uOut < s.uIn)
    (hh : s.honest) : s.evidence = true := by
  by_contra hc
  have := hh (by simpa using hc)
  omega

end Polymath.OSA4
