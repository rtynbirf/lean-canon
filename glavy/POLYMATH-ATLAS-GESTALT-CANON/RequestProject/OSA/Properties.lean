/-
# OSA-3.2 — свойства компилятора (§19, property-based testing)

§19 перечисляет четыре свойства, которые компилятор обязан удовлетворять
на *любом* входе, а не только на кейсах Gold Dataset:

1. `PASS` ⇒ первый оператор совместим с входным типом композиции;
2. `REPAIR` ⇒ предложение починки непусто;
3. `PASS` и `REJECT` несовместимы;
4. любая `PASS`-композиция проходит все четыре уровня корректности.

Здесь все четыре доказаны для произвольных реестра и композиции (никаких
`decide` по конечному набору кейсов).  Дополнительно доказано, что при
запрещённой политике починки вердикт `REPAIR` невозможен.
-/
import RequestProject.OSA.Theorems

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA

variable (reg : List Operator) (c : Composition)

/-! ## Свойство 1: PASS ⇒ вход принят первым оператором -/

/-- **§19.1.**  Если композиция получила `PASS`, её первый оператор
принимает начальный тип. -/
theorem pass_implies_head_compatible
    (h : (compile reg c).status = Status.PASS)
    (o : Operator) (rest : List Operator) (hops : c.ops = o :: rest) :
    typeCompatible c.initialType o.inputType = true := by
  have hops' : c.ops = [] ++ o :: rest := by simpa using hops
  have hnone : diagL1 reg c = none :=
    ((firstFailure_eq_none_iff reg c).mp ((compile_pass_iff_no_failure reg c).mp h)).1
  rw [diagL1, hops'] at hnone
  simpa [outAfter] using typeDiag_none_at reg [] o rest c.initialType hnone

/-! ## Свойство 2: REPAIR ⇒ непустое предложение починки -/

/-- Нарушение уровня REPAIR обязано нести непустое предложение починки. -/
def Failure.repairInformative (f : Failure) : Prop :=
  f.sev = Severity.REPAIR → 0 < f.suggestion.length

private theorem ri_mk (sev : Severity) (code : ErrCode) (d sg : String)
    (h : sev = Severity.REPAIR → 0 < sg.length) :
    (Failure.mk sev code d sg).repairInformative := h

private theorem ri_reject (code : ErrCode) (d : String) :
    (Failure.mk Severity.REJECT code d "").repairInformative := by
  intro hh; exact absurd hh (by simp)

private theorem ri_specGap (code : ErrCode) (d sg : String) :
    (Failure.mk Severity.SPEC_GAP code d sg).repairInformative := by
  intro hh; exact absurd hh (by simp)

private theorem len_insert (a b : String) : 0 < ("insert " ++ a ++ b).length := by
  simp only [String.length_append]
  have h : 0 < "insert ".length := by decide
  omega

theorem typeDiag_repairInformative :
    ∀ (t : OSAType) (ops : List Operator) (f : Failure),
      typeDiag reg t ops = some f → f.repairInformative := by
  intro t ops
  induction ops generalizing t with
  | nil => intro f h; simp [typeDiag] at h
  | cons a l ih =>
      intro f h
      rw [typeDiag] at h
      split_ifs at h with c1 c2
      · exact ih _ _ h
      · injection h with h'; subst h'; exact ri_reject _ _
      · cases hfind : reg.find? (fun x => typeCompatible t x.inputType &&
            typeCompatible x.outputType a.inputType) with
        | none =>
            rw [hfind] at h
            cases hp : findPath2 reg t a.inputType with
            | none =>
                rw [hp] at h; injection h with h'; subst h'
                exact ri_reject _ _
            | some pr =>
                obtain ⟨x1, x2⟩ := pr
                rw [hp] at h; injection h with h'; subst h'
                exact ri_mk _ _ _ _ (fun _ => by
                  simpa [String.append_assoc] using
                    len_insert x1.id (" and " ++ x2.id ++ " before " ++ a.id))
        | some x =>
            rw [hfind] at h; injection h with h'; subst h'
            exact ri_mk _ _ _ _ (fun _ => by
              simpa [String.append_assoc] using
                len_insert x.id (" before " ++ a.id))

theorem contractDiag_repairInformative :
    ∀ (ops : List Operator) (g s : List Fact) (prev : List String) (f : Failure),
      contractDiag reg g s prev ops = some f → f.repairInformative := by
  intro ops
  induction ops with
  | nil => intro g s prev f h; simp [contractDiag] at h
  | cons a l ih =>
      intro g s prev f h
      rw [contractDiag] at h
      split_ifs at h with c1 c2 c3 c4
      · injection h with h'; subst h'
        exact ri_mk _ _ _ _ (fun _ => by
          simp only [String.length_append]
          have hx : 0 < "insert the required pre-operators of ".length := by decide
          omega)
      · injection h with h'; subst h'; exact ri_reject _ _
      · exact ih _ _ _ _ h
      · injection h with h'; subst h'; exact ri_reject _ _
      · cases hfind : reg.find? (fun x =>
            (a.pre.filter (fun z => !g.contains z)).all (fun z => x.post.contains z)) with
        | none =>
            rw [hfind] at h; injection h with h'; subst h'
            exact ri_reject _ _
        | some x =>
            rw [hfind] at h; injection h with h'; subst h'
            exact ri_mk _ _ _ _ (fun _ => by
              simpa [String.append_assoc] using
                len_insert x.id (" before " ++ a.id))

theorem effectDiag_repairInformative :
    ∀ (ops : List Operator) (inv : List Invariant) (tok htok apr : Bool) (f : Failure),
      effectDiag reg inv tok htok apr ops = some f → f.repairInformative := by
  intro ops
  induction ops with
  | nil => intro inv tok htok apr f h; simp [effectDiag] at h
  | cons a l ih =>
      intro inv tok htok apr f h
      rw [effectDiag] at h
      split_ifs at h with c1 c2 c3 c4 c5 c6
      · injection h with h'; subst h'; exact ri_reject _ _
      · injection h with h'; subst h'; exact ri_reject _ _
      · injection h with h'; subst h'; exact ri_reject _ _
      · cases hfind : reg.find? (fun x => a.authorizes x) with
        | none =>
            rw [hfind] at h; injection h with h'; subst h'
            exact ri_reject _ _
        | some x =>
            rw [hfind] at h; injection h with h'; subst h'
            exact ri_mk _ _ _ _ (fun _ => by
              simpa [String.append_assoc] using
                len_insert x.id (" before " ++ a.id))
      · cases hfind : reg.find? (fun x => x.isApprover) with
        | none =>
            rw [hfind] at h; injection h with h'; subst h'
            exact ri_reject _ _
        | some x =>
            rw [hfind] at h; injection h with h'; subst h'
            exact ri_mk _ _ _ _ (fun _ => by
              simpa [String.append_assoc] using
                len_insert x.id (" before " ++ a.id))
      · injection h with h'; subst h'
        exact ri_mk _ _ _ _ (fun _ => by
          simp only [String.length_append]
          have hx : 0 < "declare the invariant in preserves of ".length := by decide
          omega)
      · exact ih _ _ _ _ _ h

theorem globalInvariantDiag_repairInformative (f : Failure)
    (h : globalInvariantDiag c = some f) : f.repairInformative := by
  have hsev : f.sev = Severity.REJECT := by
    unfold globalInvariantDiag at h
    split at h
    · exact absurd h (by simp)
    · injection h with h'; subst h'; rfl
  intro hh
  rw [hsev] at hh
  exact absurd hh (by simp)

theorem uncertaintyDiag_repairInformative (f : Failure)
    (h : uncertaintyDiag reg c = some f) : f.repairInformative := by
  unfold uncertaintyDiag at h
  cases hlast : c.ops.getLast? with
  | none => rw [hlast] at h; simp at h
  | some last =>
    rw [hlast] at h
    simp only at h
    cases hagg : c.agg with
    | none =>
        rw [hagg] at h; injection h with h'; subst h'
        exact ri_specGap _ _ _
    | some r =>
      rw [hagg] at h
      simp only at h
      cases hthr : c.declaredThreshold.orElse
          (fun _ => thresholdFor last.outputType last.reversibility) with
      | none =>
          rw [hthr] at h; injection h with h'; subst h'
          exact ri_specGap _ _ _
      | some thr =>
        rw [hthr] at h
        simp only at h
        split_ifs at h with hb
        cases hfind : reg.find? (fun x => x.reduces &&
            decide (((aggregate r Uncert.zero c.ops).sub x.reduction).peak ≤ thr) &&
            decide (((aggregate r Uncert.zero c.ops).sub x.reduction).total ≤ thr)) with
        | none =>
            rw [hfind] at h; injection h with h'; subst h'
            exact ri_reject _ _
        | some x =>
            rw [hfind] at h; injection h with h'; subst h'
            exact ri_mk _ _ _ _ (fun _ => by
              simpa [String.append_assoc] using
                len_insert x.id " to reduce uncertainty")

theorem firstFailure_repairInformative (f : Failure)
    (h : firstFailure reg c = some f) : f.repairInformative := by
  unfold firstFailure diagL1 diagL2 diagL3 diagL4 at h
  cases h1 : typeDiag reg c.initialType c.ops with
  | some f1 =>
      rw [h1] at h; simp at h; subst h
      exact typeDiag_repairInformative reg _ _ _ h1
  | none =>
    rw [h1] at h
    simp only [Option.orElse_none] at h
    cases h2 : contractDiag reg c.initialFacts [] [] c.ops with
    | some f2 =>
        rw [h2] at h; simp at h; subst h
        exact contractDiag_repairInformative reg _ _ _ _ _ h2
    | none =>
      rw [h2] at h
      simp only [Option.orElse_none] at h
      cases h3 : effectDiag reg c.initialInvariants false false false c.ops with
      | some f3 =>
          rw [h3] at h; simp at h; subst h
          exact effectDiag_repairInformative reg _ _ _ _ _ _ h3
      | none =>
        rw [h3] at h
        simp only [Option.orElse_none] at h
        cases h4 : globalInvariantDiag c with
        | some f4 =>
            rw [h4] at h; simp at h; subst h
            exact globalInvariantDiag_repairInformative c _ h4
        | none =>
            rw [h4] at h
            simp only [Option.orElse_none] at h
            exact uncertaintyDiag_repairInformative reg c f h

/-- **§19.2.**  Вердикт `REPAIR` всегда сопровождается непустым предложением
починки. -/
theorem repair_implies_suggestion
    (h : (compile reg c).status = Status.REPAIR) :
    0 < (compile reg c).suggestion.length := by
  cases hf : firstFailure reg c with
  | none =>
      exfalso
      rw [compile, hf] at h
      simp at h
  | some f =>
      have hsug : (compile reg c).suggestion = f.suggestion := by
        rw [compile]; simp [hf]
      have hstat : (compile reg c).status =
          Status.escalate c.repairPolicy f.sev.toStatus := by
        rw [compile]; simp [hf]
      have hsev : f.sev = Severity.REPAIR := by
        rw [hstat] at h
        cases hp : c.repairPolicy <;> cases hs : f.sev <;>
          simp [hp, hs, Severity.toStatus, Status.escalate] at h ⊢
      rw [hsug]
      exact firstFailure_repairInformative reg c f hf hsev

/-! ## Свойство 3: PASS и REJECT несовместимы -/

/-- **§19.3.**  Вердикт единственен: `PASS` исключает `REJECT` (и наоборот). -/
theorem pass_excludes_reject :
    ¬((compile reg c).status = Status.PASS ∧ (compile reg c).status = Status.REJECT) := by
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- Вердикт всегда принадлежит реестру §9 и ровно один. -/
theorem status_total :
    (compile reg c).status = Status.PASS ∨ (compile reg c).status = Status.REPAIR ∨
    (compile reg c).status = Status.REJECT ∨ (compile reg c).status = Status.SPEC_GAP := by
  cases h : (compile reg c).status <;> simp

/-! ## Свойство 4: PASS ⇒ все четыре уровня корректности -/

/-- **§19.4.**  Композиция с вердиктом `PASS` проходит все четыре уровня
§9 — и это не формальная отметка: для каждого стыка выполняются типовая
совместимость и отсутствие межуровневого прыжка, прекондиции покрыты
гарантированными постусловиями, инварианты живы, эффекты в рамках
контракта, а неопределённость — под порогом. -/
theorem pass_implies_four_levels :
    (compile reg c).status = Status.PASS →
      ((compile reg c).l1 = true ∧ (compile reg c).l2 = true ∧
       (compile reg c).l3 = true ∧ (compile reg c).l4 = true) :=
  (compile_status_pass_iff reg c).mp

/-- Полный семантический смысл вердикта `PASS`, собранный в одно
утверждение. -/
theorem pass_semantics
    (h : (compile reg c).status = Status.PASS) :
    (∀ pre o suf, c.ops = pre ++ o :: suf →
        typeCompatible (outAfter c.initialType pre) o.inputType = true) ∧
    (∀ pre o suf, c.ops = pre ++ o :: suf →
        levelGap (outAfter c.initialType pre) o.inputType = 0) ∧
    (∀ pre o suf, c.ops = pre ++ o :: suf →
        subsetOf o.pre (factsAfter c.initialFacts pre) = true) ∧
    (∀ pre o suf, c.ops = pre ++ o :: suf →
        subsetOf o.producedEffects o.allowedEffects = true) ∧
    subsetOf c.requiredFinalInvariants
      (finalInvariants c.initialInvariants c.ops) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro pre o suf hops
    have hnone : diagL1 reg c = none :=
      ((firstFailure_eq_none_iff reg c).mp ((compile_pass_iff_no_failure reg c).mp h)).1
    rw [diagL1, hops] at hnone
    exact typeDiag_none_at reg pre o suf c.initialType hnone
  · intro pre o suf hops
    exact pass_implies_no_level_jump reg c h pre o suf hops
  · intro pre o suf hops
    exact pass_implies_preconditions_guaranteed reg c h pre o suf hops
  · intro pre o suf hops
    exact pass_implies_no_effect_leakage reg c h pre o suf hops
  · exact pass_implies_global_invariants reg c h

/-! ## Политика починки -/

/-- При запрещённой автоматической починке вердикт `REPAIR` невозможен:
компилятор либо принимает композицию, либо отвергает её (§11). -/
theorem forbid_policy_never_repairs (hp : c.repairPolicy = RepairPolicy.forbid) :
    (compile reg c).status ≠ Status.REPAIR := by
  cases hf : firstFailure reg c with
  | none => rw [compile, hf]; simp
  | some f =>
      rw [compile, hf]
      simp only
      cases f.sev <;> simp [hp, Severity.toStatus, Status.escalate]

end Polymath.OSA
