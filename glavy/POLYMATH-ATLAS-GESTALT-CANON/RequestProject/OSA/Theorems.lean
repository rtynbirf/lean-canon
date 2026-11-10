/-
# OSA-3.2 — доказанные свойства компилятора

Здесь доказаны ключевые свойства компилятора из `RequestProject.OSA.Spec`:

* вердикт `PASS` выдаётся **тогда и только тогда**, когда пройдены все четыре
  уровня L1–L4 (§1);
* `PASS` влечёт покомпонентные гарантии: типовую совместимость каждого стыка,
  отсутствие межуровневых прыжков (§7 RULE 6), установленность всех
  прекондиций гарантированными постусловиями (§7 RULE 2/2B), сохранность
  требуемых инвариантов (§7 RULE 3), отсутствие утечки эффектов и наличие
  авторизации перед каждым E4-оператором (§7 RULE 4), а также
  соблюдение порога неопределённости (§7 RULE 5);
* соответствие «код ошибки ↔ статус» из реестра §8.
-/
import RequestProject.OSA.Spec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

variable (reg : List Operator) (c : Composition)

/-! ## Вердикт и четыре уровня -/

/-- Статус `PASS` не является образом никакой тяжести нарушения. -/
theorem Severity.toStatus_ne_pass (s : Severity) : s.toStatus ≠ Status.PASS := by
  cases s <;> simp [Severity.toStatus]

/-- Ни при какой политике починки нарушение не превращается в `PASS`:
эскалация может только ужесточить вердикт. -/
theorem escalate_ne_pass (p : RepairPolicy) (s : Severity) :
    Status.escalate p s.toStatus ≠ Status.PASS := by
  cases p <;> cases s <;> simp [Severity.toStatus, Status.escalate]

/-- Нарушение отсутствует ровно тогда, когда пройдены все четыре уровня. -/
theorem firstFailure_eq_none_iff :
    firstFailure reg c = none ↔
      diagL1 reg c = none ∧ diagL2 reg c = none ∧
      diagL3 reg c = none ∧ diagL4 reg c = none := by
  unfold firstFailure
  cases h1 : diagL1 reg c <;> cases h2 : diagL2 reg c <;>
    cases h3 : diagL3 reg c <;> cases h4 : diagL4 reg c <;>
    simp [Option.orElse]

/-- **Основное свойство §1**: композиция получает вердикт `PASS` тогда и только
тогда, когда пройдены все четыре уровня проверки. -/
theorem compile_status_pass_iff :
    (compile reg c).status = Status.PASS ↔
      ((compile reg c).l1 = true ∧ (compile reg c).l2 = true ∧
       (compile reg c).l3 = true ∧ (compile reg c).l4 = true) := by
  have hff := firstFailure_eq_none_iff reg c
  constructor
  · intro h
    have hnone : firstFailure reg c = none := by
      unfold compile at h
      simp only at h
      cases hf : firstFailure reg c with
      | none => rfl
      | some f =>
          rw [hf] at h
          exact absurd h (escalate_ne_pass c.repairPolicy f.sev)
    obtain ⟨g1, g2, g3, g4⟩ := hff.mp hnone
    simp [compile, g1, g2, g3, g4]
  · rintro ⟨g1, g2, g3, g4⟩
    simp only [compile] at g1 g2 g3 g4 ⊢
    have h1 : diagL1 reg c = none := Option.isNone_iff_eq_none.mp g1
    have h2 : diagL2 reg c = none := Option.isNone_iff_eq_none.mp g2
    have h3 : diagL3 reg c = none := Option.isNone_iff_eq_none.mp g3
    have h4 : diagL4 reg c = none := Option.isNone_iff_eq_none.mp g4
    rw [hff.mpr ⟨h1, h2, h3, h4⟩]

/-- Вердикт `PASS` означает отсутствие каких-либо нарушений. -/
theorem compile_pass_iff_no_failure :
    (compile reg c).status = Status.PASS ↔ firstFailure reg c = none := by
  constructor
  · intro h
    cases hf : firstFailure reg c with
    | none => rfl
    | some f =>
        rw [compile, hf] at h
        exact absurd h (escalate_ne_pass c.repairPolicy f.sev)
  · intro h
    simp [compile, h]

/-! ## L1: типовая корректность (§7 RULE 1, RULE 6) -/

/-- Тип, поступающий на вход после выполнения списка операторов. -/
def outAfter (t : OSAType) : List Operator → OSAType
  | [] => t
  | o :: rest => outAfter o.outputType rest

@[simp] theorem outAfter_append (t : OSAType) (xs ys : List Operator) :
    outAfter t (xs ++ ys) = outAfter (outAfter t xs) ys := by
  induction xs generalizing t with
  | nil => rfl
  | cons a l ih => simpa [outAfter] using ih a.outputType

/-- Если проверка типов прошла, то каждый оператор цепочки принимает тип,
приходящий на его вход. -/
theorem typeDiag_none_at (pre : List Operator) (o : Operator) (suf : List Operator) :
    ∀ t : OSAType, typeDiag reg t (pre ++ o :: suf) = none →
      typeCompatible (outAfter t pre) o.inputType = true := by
  induction pre with
  | nil =>
      intro t h
      rw [List.nil_append, typeDiag] at h
      split_ifs at h with c1 c2
      · simpa [outAfter] using c1
      · cases hfind : reg.find? (fun x => typeCompatible t x.inputType &&
            typeCompatible x.outputType o.inputType) with
        | none =>
            rw [hfind] at h
            cases hp : findPath2 reg t o.inputType with
            | none => rw [hp] at h; simp at h
            | some pr => obtain ⟨x1, x2⟩ := pr; rw [hp] at h; simp at h
        | some x => rw [hfind] at h; simp at h
  | cons a l ih =>
      intro t h
      rw [List.cons_append, typeDiag] at h
      split_ifs at h with c1 c2
      · simpa [outAfter] using ih a.outputType h
      · cases hfind : reg.find? (fun x => typeCompatible t x.inputType &&
            typeCompatible x.outputType a.inputType) with
        | none =>
            rw [hfind] at h
            cases hp : findPath2 reg t a.inputType with
            | none => rw [hp] at h; simp at h
            | some pr => obtain ⟨x1, x2⟩ := pr; rw [hp] at h; simp at h
        | some x => rw [hfind] at h; simp at h

/-- Совместимость типов никогда не меняет уровень иерархии §3: объявленные
подтипы и конверсии живут внутри одного уровня. -/
theorem typeCompatible_level (a b : OSAType) (h : typeCompatible a b = true) :
    a.level = b.level := by
  revert h; revert a b; decide

/-- **Отсутствие межуровневых прыжков (§7 RULE 6).**  Если композиция получила
`PASS`, то на каждом стыке уровень типа не меняется (никаких скачков через
уровни без оператора конверсии). -/
theorem pass_implies_no_level_jump
    (h : (compile reg c).status = Status.PASS)
    (pre : List Operator) (o : Operator) (suf : List Operator)
    (hops : c.ops = pre ++ o :: suf) :
    levelGap (outAfter c.initialType pre) o.inputType = 0 := by
  have hnone : diagL1 reg c = none :=
    ((firstFailure_eq_none_iff reg c).mp ((compile_pass_iff_no_failure reg c).mp h)).1
  rw [diagL1, hops] at hnone
  have := typeCompatible_level _ _ (typeDiag_none_at reg pre o suf _ hnone)
  simp [levelGap, this, Nat.dist_self]

/-- **Локальная типовая совместимость каждого стыка (§7 RULE 1).** -/
theorem pass_implies_adjacent_compatible
    (h : (compile reg c).status = Status.PASS)
    (pre : List Operator) (a b : Operator) (suf : List Operator)
    (hops : c.ops = pre ++ a :: b :: suf) :
    typeCompatible a.outputType b.inputType = true := by
  have hnone : diagL1 reg c = none :=
    ((firstFailure_eq_none_iff reg c).mp ((compile_pass_iff_no_failure reg c).mp h)).1
  rw [diagL1, hops] at hnone
  have hops' : pre ++ a :: b :: suf = (pre ++ [a]) ++ b :: suf := by simp
  rw [hops'] at hnone
  have := typeDiag_none_at reg (pre ++ [a]) b suf c.initialType hnone
  simpa [outAfter] using this

/-! ## L2: контрактная корректность (§7 RULE 2, RULE 2B) -/

/-- Гарантированные факты, накопленные после выполнения списка операторов. -/
def factsAfter (g : List Fact) : List Operator → List Fact
  | [] => g
  | o :: rest => factsAfter (g ++ o.post) rest

/-- Если контрактная проверка прошла, то прекондиции каждого оператора
покрыты **гарантированными** постусловиями предшественников (а не побочными
эффектами — это и есть отсутствие `E_CONTRACT_LEAKAGE`). -/
theorem contractDiag_none_at (pre : List Operator) (o : Operator) (suf : List Operator) :
    ∀ (g s : List Fact) (prev : List String),
      contractDiag reg g s prev (pre ++ o :: suf) = none →
      subsetOf o.pre (factsAfter g pre) = true := by
  induction pre with
  | nil =>
      intro g s prev h
      rw [List.nil_append, contractDiag] at h
      split_ifs at h with c1 c2 c3 c4
      · simpa [factsAfter] using c1
      · cases hfind : reg.find? (fun x =>
            (o.pre.filter (fun f => !g.contains f)).all (fun f => x.post.contains f)) with
        | none => rw [hfind] at h; simp at h
        | some x => rw [hfind] at h; simp at h
  | cons a l ih =>
      intro g s prev h
      rw [List.cons_append, contractDiag] at h
      split_ifs at h with c1 c2 c3 c4
      · simpa [factsAfter] using ih (g ++ a.post) (s ++ a.sideFacts) (prev ++ [a.id]) h
      · cases hfind : reg.find? (fun x =>
            (a.pre.filter (fun f => !g.contains f)).all (fun f => x.post.contains f)) with
        | none => rw [hfind] at h; simp at h
        | some x => rw [hfind] at h; simp at h

/-- **Контрактная корректность (§7 RULE 2 и 2B).**  При вердикте `PASS`
прекондиции каждого оператора следуют из гарантированных постусловий
предшественников. -/
theorem pass_implies_preconditions_guaranteed
    (h : (compile reg c).status = Status.PASS)
    (pre : List Operator) (o : Operator) (suf : List Operator)
    (hops : c.ops = pre ++ o :: suf) :
    subsetOf o.pre (factsAfter c.initialFacts pre) = true := by
  have hnone : diagL2 reg c = none :=
    ((firstFailure_eq_none_iff reg c).mp ((compile_pass_iff_no_failure reg c).mp h)).2.1
  rw [diagL2, hops] at hnone
  exact contractDiag_none_at reg pre o suf _ _ _ hnone

/-! ## L3: инварианты и политика эффектов (§7 RULE 3, RULE 4) -/

/-- Инварианты, действующие после выполнения списка операторов. -/
def invAfter (inv : List Invariant) : List Operator → List Invariant
  | [] => inv
  | o :: rest => invAfter (inv.filter (fun i => !o.destroys.contains i)) rest

theorem mem_invAfter (inv : List Invariant) (ops : List Operator) (i : Invariant) :
    i ∈ invAfter inv ops ↔ i ∈ inv ∧ ∀ o ∈ ops, o.destroys.contains i = false := by
  induction ops generalizing inv with
  | nil => simp [invAfter]
  | cons a l ih =>
      simp only [invAfter, ih, List.mem_filter, List.mem_cons]
      constructor
      · rintro ⟨⟨hi, ha⟩, hrest⟩
        refine ⟨hi, ?_⟩
        rintro o (rfl | ho)
        · simpa using ha
        · exact hrest o ho
      · rintro ⟨hi, hall⟩
        exact ⟨⟨hi, by simpa using hall a (Or.inl rfl)⟩,
               fun o ho => hall o (Or.inr ho)⟩

/-- Ключевое следствие успешной проверки уровня L3 для отдельного оператора
цепочки: эффекты в пределах контракта, требуемые инварианты живы, а
E4-оператор снабжён токеном авторизации (E3-оператор — подтверждением). -/
theorem effectDiag_none_at (pre : List Operator) (o : Operator) (suf : List Operator) :
    ∀ (inv : List Invariant) (tok htok apr : Bool),
      effectDiag reg inv tok htok apr (pre ++ o :: suf) = none →
      subsetOf o.producedEffects o.allowedEffects = true ∧
      subsetOf o.requiresInv (invAfter inv pre) = true ∧
      (o.effectLevel = EffectLevel.E4 → o.requiresAuthorization = true →
        (tok || pre.any (fun x => x.isAuthorizer)) = true) ∧
      (o.effectLevel = EffectLevel.E3 →
        (apr || pre.any (fun x => x.isApprover)) = true) := by
  induction pre with
  | nil =>
      intro inv tok htok apr h
      rw [List.nil_append, effectDiag] at h
      split_ifs at h with c1 c2 c3 c4 c5 c6
      · cases hfind : reg.find? (fun x => o.authorizes x) with
        | none => rw [hfind] at h; simp at h
        | some x => rw [hfind] at h; simp at h
      · cases hfind : reg.find? (fun x => x.isApprover) with
        | none => rw [hfind] at h; simp at h
        | some x => rw [hfind] at h; simp at h
      · refine ⟨by simpa using c1, by simpa [invAfter] using c3, ?_, ?_⟩
        · intro he ha
          cases htok' : tok with
          | true => simp
          | false =>
              exfalso
              apply c4
              simp [he, ha, htok']
        · intro he
          cases hapr : apr with
          | true => simp
          | false =>
              exfalso
              apply c5
              simp [he, hapr]
  | cons a l ih =>
      intro inv tok htok apr h
      rw [List.cons_append, effectDiag] at h
      split_ifs at h with c1 c2 c3 c4 c5 c6
      · cases hfind : reg.find? (fun x => a.authorizes x) with
        | none => rw [hfind] at h; simp at h
        | some x => rw [hfind] at h; simp at h
      · cases hfind : reg.find? (fun x => x.isApprover) with
        | none => rw [hfind] at h; simp at h
        | some x => rw [hfind] at h; simp at h
      · obtain ⟨k1, k2, k3, k4⟩ := ih _ _ _ _ h
        refine ⟨k1, by simpa [invAfter] using k2, ?_, ?_⟩
        · intro he ha
          have hk := k3 he ha
          simp only [List.any_cons]
          rcases Bool.or_eq_true_iff.mp hk with hh | hh
          · rcases Bool.or_eq_true_iff.mp hh with hh' | hh' <;> simp [hh']
          · simp [hh]
        · intro he
          have hk := k4 he
          simp only [List.any_cons]
          rcases Bool.or_eq_true_iff.mp hk with hh | hh
          · rcases Bool.or_eq_true_iff.mp hh with hh' | hh' <;> simp [hh']
          · simp [hh]

private theorem diagL3_none (h : (compile reg c).status = Status.PASS) :
    effectDiag reg c.initialInvariants false false false c.ops = none := by
  have hnone : diagL3 reg c = none :=
    ((firstFailure_eq_none_iff reg c).mp ((compile_pass_iff_no_failure reg c).mp h)).2.2.1
  rw [diagL3] at hnone
  cases he : effectDiag reg c.initialInvariants false false false c.ops with
  | none => rfl
  | some f => rw [he] at hnone; simp at hnone

/-- **Отсутствие утечки эффектов (§7 RULE 4C).** -/
theorem pass_implies_no_effect_leakage
    (h : (compile reg c).status = Status.PASS)
    (pre : List Operator) (o : Operator) (suf : List Operator)
    (hops : c.ops = pre ++ o :: suf) :
    subsetOf o.producedEffects o.allowedEffects = true := by
  have hnone := diagL3_none reg c h
  rw [hops] at hnone
  exact (effectDiag_none_at reg pre o suf _ _ _ _ hnone).1

/-- **Инвариантная безопасность (§7 RULE 3).**  Ни один предшественник не
уничтожает инвариант, необходимый последующему оператору. -/
theorem pass_implies_invariant_safety
    (h : (compile reg c).status = Status.PASS)
    (pre : List Operator) (o : Operator) (suf : List Operator)
    (hops : c.ops = pre ++ o :: suf)
    (i : Invariant) (hi : i ∈ o.requiresInv) :
    i ∈ c.initialInvariants ∧ ∀ p ∈ pre, p.destroys.contains i = false := by
  have hnone := diagL3_none reg c h
  rw [hops] at hnone
  have hsub := (effectDiag_none_at reg pre o suf _ _ _ _ hnone).2.1
  have hmem : (invAfter c.initialInvariants pre).contains i = true := by
    unfold subsetOf at hsub
    exact List.all_eq_true.mp hsub i hi
  exact (mem_invAfter c.initialInvariants pre i).mp (List.mem_of_elem_eq_true hmem)

/-- **Политика авторизации (§7 RULE 4A).**  Перед каждым оператором уровня E4,
требующим авторизации, в цепочке присутствует оператор, выдающий
`AuthorizationToken`. -/
theorem pass_implies_authorization
    (h : (compile reg c).status = Status.PASS)
    (pre : List Operator) (o : Operator) (suf : List Operator)
    (hops : c.ops = pre ++ o :: suf)
    (he : o.effectLevel = EffectLevel.E4)
    (ha : o.requiresAuthorization = true) :
    pre.any (fun x => x.isAuthorizer) = true := by
  have hnone := diagL3_none reg c h
  rw [hops] at hnone
  have := (effectDiag_none_at reg pre o suf _ _ _ _ hnone).2.2.1 he ha
  simpa using this

/-- **Политика подтверждения (§7 RULE 4B).**  Перед каждым оператором уровня E3
в цепочке присутствует оператор, порождающий подтверждение. -/
theorem pass_implies_approval
    (h : (compile reg c).status = Status.PASS)
    (pre : List Operator) (o : Operator) (suf : List Operator)
    (hops : c.ops = pre ++ o :: suf)
    (he : o.effectLevel = EffectLevel.E3) :
    pre.any (fun x => x.isApprover) = true := by
  have hnone := diagL3_none reg c h
  rw [hops] at hnone
  have := (effectDiag_none_at reg pre o suf _ _ _ _ hnone).2.2.2 he
  simpa using this

/-- **Глобальная проверка инвариантов (§11.D).**  Композиция, получившая
`PASS`, сохраняет все инварианты, объявленные обязательными для её результата. -/
theorem pass_implies_global_invariants
    (h : (compile reg c).status = Status.PASS) :
    subsetOf c.requiredFinalInvariants (finalInvariants c.initialInvariants c.ops) = true := by
  have hnone : diagL3 reg c = none :=
    ((firstFailure_eq_none_iff reg c).mp ((compile_pass_iff_no_failure reg c).mp h)).2.2.1
  rw [diagL3] at hnone
  cases he : effectDiag reg c.initialInvariants false false false c.ops with
  | some f => rw [he] at hnone; simp at hnone
  | none =>
      rw [he] at hnone
      simp only [Option.orElse_none] at hnone
      unfold globalInvariantDiag at hnone
      by_cases hs : subsetOf c.requiredFinalInvariants
          (finalInvariants c.initialInvariants c.ops)
      · exact hs
      · exfalso
        simp only [hs, if_false, Bool.false_eq_true] at hnone
        exact Option.some_ne_none _ hnone

/-! ## L4: эпистемическая обоснованность (§7 RULE 5) -/

/-- **Эпистемическая обоснованность.**  Если непустая композиция получила
`PASS`, то для неё задано правило агрегации, для целевого уровня определён
порог, и накопленная неопределённость не превышает его — ни покомпонентно,
ни суммарно. -/
theorem pass_implies_uncertainty_within_threshold
    (h : (compile reg c).status = Status.PASS)
    (last : Operator) (hlast : c.ops.getLast? = some last) :
    ∃ r thr, c.agg = some r ∧
      c.declaredThreshold.orElse
        (fun _ => thresholdFor last.outputType last.reversibility) = some thr ∧
      (aggregate r Uncert.zero c.ops).peak ≤ thr ∧
      (aggregate r Uncert.zero c.ops).total ≤ thr := by
  have hnone : diagL4 reg c = none :=
    ((firstFailure_eq_none_iff reg c).mp ((compile_pass_iff_no_failure reg c).mp h)).2.2.2
  rw [diagL4, uncertaintyDiag, hlast] at hnone
  cases hr : c.agg with
  | none => rw [hr] at hnone; simp at hnone
  | some r =>
      rw [hr] at hnone
      simp only at hnone
      cases hthr : c.declaredThreshold.orElse
          (fun _ => thresholdFor last.outputType last.reversibility) with
      | none => rw [hthr] at hnone; simp at hnone
      | some thr =>
          rw [hthr] at hnone
          simp only at hnone
          by_cases hb : (aggregate r Uncert.zero c.ops).peak ≤ thr ∧
              (aggregate r Uncert.zero c.ops).total ≤ thr
          · exact ⟨r, thr, rfl, rfl, hb.1, hb.2⟩
          · exfalso
            have hfalse : (decide ((aggregate r Uncert.zero c.ops).peak ≤ thr) &&
                decide ((aggregate r Uncert.zero c.ops).total ≤ thr)) = false := by
              simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
              rcases not_and_or.mp hb with hh | hh
              · exact Or.inl hh
              · exact Or.inr hh
            rw [hfalse] at hnone
            simp only [if_false, Bool.false_eq_true] at hnone
            cases hfind : reg.find? (fun x => x.reduces &&
                decide (((aggregate r Uncert.zero c.ops).sub x.reduction).peak ≤ thr) &&
                decide (((aggregate r Uncert.zero c.ops).sub x.reduction).total ≤ thr)) with
            | none => rw [hfind] at hnone; simp at hnone
            | some x => rw [hfind] at hnone; simp at hnone

/-! ## §8: соответствие кода ошибки и статуса -/

/-- Классификация кодов §8 по статусу.  Для `E_EFFECT_POLICY_VIOLATION` и
`E_EPISTEMIC_INSUFFICIENT` реестр §8 допускает и REJECT, и REPAIR (в
зависимости от возможности починки), поэтому они не классифицируются жёстко. -/
def codeClass : ErrCode → Option Severity
  | .E_TYPE_MISMATCH | .E_INVARIANT_VIOLATION | .E_CONTRACT_LEAKAGE
  | .E_LEVEL_JUMP | .E_EFFECT_LEAKAGE | .E_UNSATISFIABLE_CONTRACT => some .REJECT
  | .E_MISSING_CONVERSION | .E_NOT_YET_SATISFIED | .E_INVARIANT_LOSS => some .REPAIR
  | .UNCERTAINTY_RULE_NOT_DEFINED | .SPEC_GAP_UNDEFINED_THRESHOLD => some .SPEC_GAP
  | _ => none

/-- Нарушение согласовано с реестром §8: его код не пуст, а тяжесть совпадает
с той, которую реестр фиксирует для этого кода. -/
def Failure.wellFormed (f : Failure) : Prop :=
  f.code ≠ ErrCode.NONE ∧ ∀ s, codeClass f.code = some s → f.sev = s

private theorem wf_mk (sev : Severity) (code : ErrCode) (d sg : String)
    (h1 : code ≠ ErrCode.NONE) (h2 : ∀ x, codeClass code = some x → sev = x) :
    (Failure.mk sev code d sg).wellFormed := ⟨h1, h2⟩

theorem typeDiag_wellFormed :
    ∀ (t : OSAType) (ops : List Operator) (f : Failure),
      typeDiag reg t ops = some f → f.wellFormed := by
  intro t ops
  induction ops generalizing t with
  | nil => intro f h; simp [typeDiag] at h
  | cons a l ih =>
      intro f h
      rw [typeDiag] at h
      split_ifs at h with c1 c2
      · exact ih _ _ h
      · injection h with h'; subst h'
        exact wf_mk _ _ _ _ (by decide) (by decide)
      · cases hfind : reg.find? (fun x => typeCompatible t x.inputType &&
            typeCompatible x.outputType a.inputType) with
        | none =>
            rw [hfind] at h
            cases hp : findPath2 reg t a.inputType with
            | none =>
                rw [hp] at h; injection h with h'; subst h'
                exact wf_mk _ _ _ _ (by decide) (by decide)
            | some pr =>
                obtain ⟨x1, x2⟩ := pr
                rw [hp] at h; injection h with h'; subst h'
                exact wf_mk _ _ _ _ (by decide) (by decide)
        | some x =>
            rw [hfind] at h; injection h with h'; subst h'
            exact wf_mk _ _ _ _ (by decide) (by decide)

theorem contractDiag_wellFormed :
    ∀ (ops : List Operator) (g s : List Fact) (prev : List String) (f : Failure),
      contractDiag reg g s prev ops = some f → f.wellFormed := by
  intro ops
  induction ops with
  | nil => intro g s prev f h; simp [contractDiag] at h
  | cons a l ih =>
      intro g s prev f h
      rw [contractDiag] at h
      split_ifs at h with c1 c2 c3 c4
      · injection h with h'; subst h'
        exact wf_mk _ _ _ _ (by decide) (by decide)
      · injection h with h'; subst h'
        exact wf_mk _ _ _ _ (by decide) (by decide)
      · exact ih _ _ _ _ h
      · injection h with h'; subst h'
        exact wf_mk _ _ _ _ (by decide) (by decide)
      · cases hfind : reg.find? (fun x =>
            (a.pre.filter (fun z => !g.contains z)).all (fun z => x.post.contains z)) with
        | none =>
            rw [hfind] at h; injection h with h'; subst h'
            exact wf_mk _ _ _ _ (by decide) (by decide)
        | some x =>
            rw [hfind] at h; injection h with h'; subst h'
            exact wf_mk _ _ _ _ (by decide) (by decide)

theorem effectDiag_wellFormed :
    ∀ (ops : List Operator) (inv : List Invariant) (tok htok apr : Bool) (f : Failure),
      effectDiag reg inv tok htok apr ops = some f → f.wellFormed := by
  intro ops
  induction ops with
  | nil => intro inv tok htok apr f h; simp [effectDiag] at h
  | cons a l ih =>
      intro inv tok htok apr f h
      rw [effectDiag] at h
      split_ifs at h with c1 c2 c3 c4 c5 c6
      · injection h with h'; subst h'
        exact wf_mk _ _ _ _ (by decide) (by decide)
      · injection h with h'; subst h'
        exact wf_mk _ _ _ _ (by decide) (by decide)
      · injection h with h'; subst h'
        exact wf_mk _ _ _ _ (by decide) (by decide)
      · cases hfind : reg.find? (fun x => a.authorizes x) with
        | none =>
            rw [hfind] at h; injection h with h'; subst h'
            exact wf_mk _ _ _ _ (by decide) (by decide)
        | some x =>
            rw [hfind] at h; injection h with h'; subst h'
            exact wf_mk _ _ _ _ (by decide) (by decide)
      · cases hfind : reg.find? (fun x => x.isApprover) with
        | none =>
            rw [hfind] at h; injection h with h'; subst h'
            exact wf_mk _ _ _ _ (by decide) (by decide)
        | some x =>
            rw [hfind] at h; injection h with h'; subst h'
            exact wf_mk _ _ _ _ (by decide) (by decide)
      · injection h with h'; subst h'
        exact wf_mk _ _ _ _ (by decide) (by decide)
      · exact ih _ _ _ _ _ h

theorem firstFailure_wellFormed (f : Failure) (h : firstFailure reg c = some f) :
    f.wellFormed := by
  unfold firstFailure diagL1 diagL2 diagL3 diagL4 at h
  cases h1 : typeDiag reg c.initialType c.ops with
  | some f1 =>
      rw [h1] at h; simp at h; subst h
      exact typeDiag_wellFormed reg _ _ _ h1
  | none =>
    rw [h1] at h
    simp only [Option.orElse_none] at h
    cases h2 : contractDiag reg c.initialFacts [] [] c.ops with
    | some f2 =>
        rw [h2] at h; simp at h; subst h
        exact contractDiag_wellFormed reg _ _ _ _ _ h2
    | none =>
      rw [h2] at h
      simp only [Option.orElse_none] at h
      cases h3 : effectDiag reg c.initialInvariants false false false c.ops with
      | some f3 =>
          rw [h3] at h; simp at h; subst h
          exact effectDiag_wellFormed reg _ _ _ _ _ _ h3
      | none =>
        rw [h3] at h
        simp only [Option.orElse_none] at h
        cases h4 : globalInvariantDiag c with
        | some f4 =>
            rw [h4] at h; simp at h; subst h
            unfold globalInvariantDiag at h4
            by_cases hs : subsetOf c.requiredFinalInvariants
                (finalInvariants c.initialInvariants c.ops)
            · simp only [hs, if_true] at h4; exact absurd h4 (by simp)
            · simp only [hs, if_false, Bool.false_eq_true] at h4
              injection h4 with h4'; subst h4'
              exact wf_mk _ _ _ _ (by decide) (by decide)
        | none =>
          rw [h4] at h
          simp only [Option.orElse_none] at h
          unfold uncertaintyDiag at h
          cases hlast : c.ops.getLast? with
          | none => rw [hlast] at h; simp at h
          | some last =>
            rw [hlast] at h
            simp only at h
            cases hagg : c.agg with
            | none =>
                rw [hagg] at h; simp only [Option.some.injEq] at h
                subst h
                exact wf_mk _ _ _ _ (by decide) (by decide)
            | some r =>
              rw [hagg] at h
              simp only at h
              cases hthr : c.declaredThreshold.orElse
                  (fun _ => thresholdFor last.outputType last.reversibility) with
              | none =>
                  rw [hthr] at h; simp only [Option.some.injEq] at h
                  subst h
                  exact wf_mk _ _ _ _ (by decide) (by decide)
              | some thr =>
                rw [hthr] at h
                simp only at h
                split_ifs at h with hb
                cases hfind : reg.find? (fun x => x.reduces &&
                    decide (((aggregate r Uncert.zero c.ops).sub x.reduction).peak ≤ thr) &&
                    decide (((aggregate r Uncert.zero c.ops).sub x.reduction).total ≤ thr)) with
                  | none =>
                      rw [hfind] at h; injection h with h'; subst h'
                      exact wf_mk _ _ _ _ (by decide) (by decide)
                  | some x =>
                      rw [hfind] at h; injection h with h'; subst h'
                      exact wf_mk _ _ _ _ (by decide) (by decide)

/-- При вердикте `PASS` код ошибки равен `NONE`, и наоборот. -/
theorem compile_code_none_iff_pass :
    (compile reg c).code = ErrCode.NONE ↔ (compile reg c).status = Status.PASS := by
  cases hf : firstFailure reg c with
  | none => simp [compile, hf]
  | some f =>
      have hcode : (compile reg c).code = f.code := by rw [compile]; simp [hf]
      have hstat : (compile reg c).status = Status.escalate c.repairPolicy f.sev.toStatus := by
        rw [compile]; simp [hf]
      constructor
      · intro h
        exact absurd (hcode ▸ h) (firstFailure_wellFormed reg c f hf).1
      · intro h
        exact absurd (hstat ▸ h) (escalate_ne_pass c.repairPolicy f.sev)

/-- **Согласованность реестра §8**: код ошибки однозначно определяет статус
для всех кодов, для которых спецификация фиксирует его однозначно (с точностью
до эскалации политикой починки). -/
theorem compile_code_determines_status (s : Severity)
    (h : codeClass (compile reg c).code = some s) :
    (compile reg c).status = Status.escalate c.repairPolicy s.toStatus := by
  cases hf : firstFailure reg c with
  | none =>
      exfalso
      rw [compile] at h
      simp only [hf] at h
      simp [codeClass] at h
  | some f =>
      have hcode : (compile reg c).code = f.code := by rw [compile]; simp [hf]
      have hstat : (compile reg c).status = Status.escalate c.repairPolicy f.sev.toStatus := by
        rw [compile]; simp [hf]
      rw [hcode] at h
      rw [hstat, (firstFailure_wellFormed reg c f hf).2 s h]

/-- При разрешённой починке код ошибки определяет статус точно. -/
theorem compile_code_determines_status_of_allow (s : Severity)
    (hp : c.repairPolicy = RepairPolicy.allow)
    (h : codeClass (compile reg c).code = some s) :
    (compile reg c).status = s.toStatus := by
  rw [compile_code_determines_status reg c s h, hp, Status.escalate]

end Polymath.OSA
