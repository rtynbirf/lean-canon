/-
# OSA-4.0 — формальные критерии вместо оценочных характеристик

Модуль заменяет оценочную лексику исходного кодекса («сильный эффект»,
«хороший ремонт», «слабое предусловие», «оператор не трогает инвариант»)
на определения и доказанные утверждения:

| неформальная оценка | формальный критерий |
|---------------------|---------------------|
| «условие сильнее»   | `Entails` / `StrictlyStronger` (предпорядок на `Pred`) |
| «эффект сильнее»    | `EffectLevel.Severer` (строгий порядок по рангу) |
| «неопределённость снизилась» | `UStep.Reduces` + `uncertainty_drop_needs_evidence` |
| «оператор применим» | `Op.WellFormedIn` (разрешимый предикат) |
| «оператор не трогает инвариант» | `Untouched` + `wp_eq_self_of_untouched` |
| «ремонт лучше»      | `RVec.Better` (лексикографический порядок, `safety` доминирует) |

Здесь же доказана семантическая корректность вердикта `PASS`
(`pass_chain_executable`): вердикт не является декларацией — он влечёт
исполнимость цепочки и достижение цели.
-/
import RequestProject.OSA4.Invariants
import RequestProject.OSA4.Repair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-! ## Пространство предикатов P: порядок по силе -/

/-- **Определение.**  Предикат `p` влечёт предикат `q`, если во всяком
состоянии доказанность `p` влечёт доказанность `q`. -/
def Entails (p q : Pred) : Prop :=
  ∀ s : KState, eval s p = .TRUE_KNOWN → eval s q = .TRUE_KNOWN

@[refl] theorem entails_refl (p : Pred) : Entails p p := fun _ h => h

theorem entails_trans {p q r : Pred} (hpq : Entails p q) (hqr : Entails q r) : Entails p r :=
  fun s h => hqr s (hpq s h)

/-- **Определение.**  `p` строго сильнее `q`. -/
def StrictlyStronger (p q : Pred) : Prop := Entails p q ∧ ¬ Entails q p

theorem strictlyStronger_irrefl (p : Pred) : ¬ StrictlyStronger p p :=
  fun h => h.2 (entails_refl p)

theorem strictlyStronger_trans {p q r : Pred}
    (h₁ : StrictlyStronger p q) (h₂ : StrictlyStronger q r) : StrictlyStronger p r :=
  ⟨entails_trans h₁.1 h₂.1, fun hrp => h₁.2 (entails_trans h₂.1 hrp)⟩

/-- Константа «доказано истинно» — наибольший элемент предпорядка. -/
theorem entails_ctrue (p : Pred) : Entails p .ctrue := fun _ _ => rfl

/-- Константа «доказано ложно» — наименьший элемент предпорядка. -/
theorem cfalse_entails (p : Pred) : Entails .cfalse p := by
  intro s h; exact absurd h (by simp [eval])

/-- Отсутствие информации не доказывает ничего. -/
theorem cunknown_entails (p : Pred) : Entails .cunknown p := by
  intro s h; exact absurd h (by simp [eval])

/-- Предпорядок нетривиален: `cfalse` строго сильнее `ctrue`. -/
theorem strictlyStronger_cfalse_ctrue : StrictlyStronger .cfalse .ctrue := by
  refine ⟨cfalse_entails _, fun h => ?_⟩
  have := h ⟨[], []⟩ rfl
  simp [eval] at this

/-- **Монотонность WP по силе предиката.**  Обратный трансформер предикатов
сохраняет порядок «сильнее». -/
theorem wp_monotone (o : Op) {p q : Pred} (h : Entails p q) : Entails (wp o p) (wp o q) := by
  intro s hs
  rw [← eval_exec_eq_eval_wp] at hs ⊢
  exact h _ hs

/-- Конъюнкция сильнее каждого конъюнкта. -/
theorem entails_pand_left (p q : Pred) : Entails (.pand p q) p := by
  intro s h
  exact ((PT.and_eq_true_iff _ _).1 h).1

/-- Конъюнкция сильнее каждого конъюнкта. -/
theorem entails_pand_right (p q : Pred) : Entails (.pand p q) q := by
  intro s h
  exact ((PT.and_eq_true_iff _ _).1 h).2

/-! ## Пространство эффектов E: порядок по строгости -/

namespace EffectLevel

/-- **Определение.**  Эффект `a` строже эффекта `b`, если его ранг больше. -/
def Severer (a b : EffectLevel) : Prop := b.rank < a.rank

instance : DecidableRel Severer := fun a b => by unfold Severer; infer_instance

theorem severer_irrefl (a : EffectLevel) : ¬ Severer a a := by
  unfold Severer; omega

theorem severer_trans {a b c : EffectLevel} (h₁ : Severer a b) (h₂ : Severer b c) : Severer a c := by
  unfold Severer at *; omega

/-- Агрегация двух эффектов — это максимум рангов. -/
theorem rank_join (a b : EffectLevel) : (join a b).rank = max a.rank b.rank := by
  revert a b; decide

/-- Ранг агрегата списка не меньше ранга любого его элемента. -/
theorem rank_le_aggregate : ∀ (l : List EffectLevel) (a : EffectLevel),
    a ∈ l → a.rank ≤ (aggregate l).rank := by
  intro l
  induction l with
  | nil => intro a ha; simp at ha
  | cons b t ih =>
      intro a ha
      rw [aggregate_cons, rank_join]
      rcases List.mem_cons.1 ha with rfl | hmem
      · exact le_max_left _ _
      · exact le_trans (ih a hmem) (le_max_right _ _)

end EffectLevel

/-! ## Пространство неопределённости U -/

/-- **Определение.**  Шаг снижает неопределённость. -/
def UStep.Reduces (s : UStep) : Prop := s.uOut < s.uIn

instance (s : UStep) : Decidable s.Reduces := by unfold UStep.Reduces; infer_instance

/-- **Определение.**  Значение неопределённости укладывается в порог. -/
def UWithin (thr u : ℕ) : Prop := u ≤ thr

instance (thr u : ℕ) : Decidable (UWithin thr u) := by unfold UWithin; infer_instance

theorem uWithin_mono {thr thr' u : ℕ} (h : thr ≤ thr') (hu : UWithin thr u) : UWithin thr' u :=
  le_trans hu h

/-- **Определение.**  Уверенность как дополнение неопределённости
(неопределённость выражена в сотых долях). -/
def UStep.confidence (s : UStep) : ℕ := 100 - s.uOut

/-- Уверенность антимонотонна по неопределённости. -/
theorem confidence_antitone {a b : UStep} (h : a.uOut ≤ b.uOut) :
    b.confidence ≤ a.confidence := by
  unfold UStep.confidence; omega

/-- Снижение неопределённости честным шагом возможно только при явном
свидетельстве (формальный критерий вместо оценки «шаг обоснован»). -/
theorem reduces_needs_evidence {s : UStep} (h : s.Reduces) (hh : s.honest) :
    s.evidence = true :=
  uncertainty_drop_needs_evidence h hh

/-! ## Пространство операторов O: применимость -/

/-- **Определение.**  Оператор корректно применим в состоянии: предусловия
доказаны и авторизация получена. -/
def Op.WellFormedIn (o : Op) (s : KState) : Prop := execAllowed s o

instance (o : Op) (s : KState) : Decidable (o.WellFormedIn s) := by
  unfold Op.WellFormedIn; infer_instance

theorem wellFormed_enabled {o : Op} {s : KState} (h : o.WellFormedIn s) : o.enabled s := h.1

theorem wellFormed_authorized {o : Op} {s : KState} (h : o.WellFormedIn s) :
    authStatus s o = .TRUE_KNOWN := h.2

/-! ## Синтаксический критерий сохранения инварианта -/

/-- Имена переменных состояния, встречающиеся в предикате. -/
def Pred.varNames : Pred → List VarName
  | .factExists _ => []
  | .pnot p => p.varNames
  | .pand p q => p.varNames ++ q.varNames
  | .por p q => p.varNames ++ q.varNames
  | .pimp p q => p.varNames ++ q.varNames
  | .gte v _ => [v]
  | .peq v _ => [v]
  | .ctrue => []
  | .cfalse => []
  | .cunknown => []

/-- **Определение.**  Оператор не затрагивает предикат: ни один упомянутый
факт не производится и не уничтожается, ни одна упомянутая переменная не
изменяется. -/
def Untouched (o : Op) (q : Pred) : Prop :=
  (∀ f ∈ q.factIds, f ∉ o.produces ∧ f ∉ o.kill) ∧ (∀ v ∈ q.varNames, v ∉ o.modifies)

/-- Если оператор не затрагивает предикат, WP-образ предиката совпадает с
ним самим. -/
theorem wp_eq_self_of_untouched (o : Op) : ∀ q : Pred, Untouched o q → wp o q = q := by
  intro q
  induction q with
  | factExists f =>
      intro h
      have hf := h.1 f (by simp [Pred.factIds])
      simp [wp, hf.1, hf.2]
  | pnot p ih =>
      intro h
      simp [wp, ih ⟨h.1, h.2⟩]
  | pand p q ihp ihq =>
      intro h
      obtain ⟨hf, hv⟩ := h
      simp only [Pred.factIds, Pred.varNames, List.mem_append] at hf hv
      simp [wp, ihp ⟨fun f hfm => hf f (Or.inl hfm), fun v hvm => hv v (Or.inl hvm)⟩,
        ihq ⟨fun f hfm => hf f (Or.inr hfm), fun v hvm => hv v (Or.inr hvm)⟩]
  | por p q ihp ihq =>
      intro h
      obtain ⟨hf, hv⟩ := h
      simp only [Pred.factIds, Pred.varNames, List.mem_append] at hf hv
      simp [wp, ihp ⟨fun f hfm => hf f (Or.inl hfm), fun v hvm => hv v (Or.inl hvm)⟩,
        ihq ⟨fun f hfm => hf f (Or.inr hfm), fun v hvm => hv v (Or.inr hvm)⟩]
  | pimp p q ihp ihq =>
      intro h
      obtain ⟨hf, hv⟩ := h
      simp only [Pred.factIds, Pred.varNames, List.mem_append] at hf hv
      simp [wp, ihp ⟨fun f hfm => hf f (Or.inl hfm), fun v hvm => hv v (Or.inl hvm)⟩,
        ihq ⟨fun f hfm => hf f (Or.inr hfm), fun v hvm => hv v (Or.inr hvm)⟩]
  | gte v n =>
      intro h
      have hv := h.2 v (by simp [Pred.varNames])
      simp [wp, hv]
  | peq v n =>
      intro h
      have hv := h.2 v (by simp [Pred.varNames])
      simp [wp, hv]
  | ctrue => intro _; rfl
  | cfalse => intro _; rfl
  | cunknown => intro _; rfl

/-- **Достаточный синтаксический критерий сохранения инварианта.** -/
theorem preserves_of_untouched {o : Op} {I : Invariant} (h : Untouched o I.cond) :
    o.preserves I :=
  preserves_of_wp_eq o I (wp_eq_self_of_untouched o I.cond h)

/-- Критерий достаточен, но не необходим: оператор, производящий факт
инварианта, сохраняет инвариант, хотя и затрагивает его. -/
theorem untouched_not_necessary :
    ∃ (o : Op) (I : Invariant), o.preserves I ∧ ¬ Untouched o I.cond := by
  refine ⟨⟨"PRODUCE_F", [], ["F"], [], [], [], .E0, false⟩, ⟨"I_F", .factExists "F"⟩, ?_, ?_⟩
  · intro s _
    show eval (Op.exec _ s) (.factExists "F") = .TRUE_KNOWN
    exact factStatus_exec_produces _ s (by simp)
  · intro h
    have := (h.1 "F" (by simp [Pred.factIds])).1
    simp at this

/-! ## Пространство планов ремонта: формальный критерий качества -/

namespace RVec

/-- **Определение.**  План строго лучше другого в лексикографическом
порядке `safety > obligations > policy > uncertainty > cost`. -/
def Better (a b : RVec) : Prop := lt a b

instance : DecidableRel Better := fun a b => by unfold Better; infer_instance

theorem better_irrefl (a : RVec) : ¬ Better a a := lt_irrefl a

theorem better_trans {a b c : RVec} (h₁ : Better a b) (h₂ : Better b c) : Better a c :=
  lt_trans h₁ h₂

/-- Формальный смысл приоритета безопасности: меньшее число нарушений
безопасности делает план лучше независимо от остальных компонент. -/
theorem better_of_safety {a b : RVec} (h : a.safety < b.safety) : Better a b :=
  safety_dominates h

end RVec

/-! ## Семантическая корректность вердикта PASS -/

/-- Вердикт `PASS` эпистемического прохода влечёт исполнимость цепочки и
доказанность цели в конечном состоянии. -/
theorem epiPass_pass_sound (reg : List Op) :
    ∀ (ops : List Op) (s : KState) (goal : Pred),
      (epiPass reg ops s goal).verdict = .PASS →
        chainEnabled ops s ∧ eval (execChain ops s) goal = .TRUE_KNOWN := by
  intro ops
  induction ops with
  | nil =>
      intro s goal h
      refine ⟨trivial, ?_⟩
      rw [epiPass] at h
      split at h
      all_goals rename_i hg
      all_goals first
        | exact Verdict.noConfusion h
        | simpa using hg
  | cons o t ih =>
      intro s goal h
      rw [epiPass] at h
      split at h
      all_goals rename_i hreq
      all_goals first
        | exact Verdict.noConfusion h
        | (split at h <;> exact Verdict.noConfusion h)
        | (split at h
           all_goals rename_i hauth
           all_goals first
             | exact Verdict.noConfusion h
             | (split at h <;> exact Verdict.noConfusion h)
             | (obtain ⟨hchain, hgoal⟩ := ih (o.exec s) goal h
                exact ⟨⟨⟨hreq, hauth⟩, hchain⟩, hgoal⟩))

/-- **Вердикт `PASS` компилятора семантически обоснован.**  Цепочка
исполнима шаг за шагом (все предусловия и авторизации доказаны) и цель
доказанно достигается. -/
theorem pass_chain_executable (sc : Scenario) (h : (compile sc).verdict = .PASS) :
    chainEnabled sc.chain sc.init ∧
      eval (execChain sc.chain sc.init) sc.goal = .TRUE_KNOWN := by
  have hu := pass_no_unknown_operator sc h
  have hd := pass_no_double_consume sc h
  have hl := pass_no_liveness_violation sc h
  rw [compile, hu, hd, hl] at h
  exact epiPass_pass_sound sc.registry sc.chain sc.init sc.goal h

end Polymath.OSA4
