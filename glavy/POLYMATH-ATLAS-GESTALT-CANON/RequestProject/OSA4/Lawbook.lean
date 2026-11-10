/-
# OSA-4.0 — LAWBOOK: 18 законов ядра

Формализация §9/§12 «LAWBOOK — АЛГЕБРАИЧЕСКИЕ ЗАКОНЫ» кодекса OSA-4.0.
Кодекс перечисляет законы как «17 аксиом, готовых к трансляции в Lean 4 /
Coq» (в полной версии — 18, с LAW-018 Repair Soundness).  Здесь они
**не аксиомы**: каждый закон записан как утверждение о формальном ядре и
доказан (`lawbook_holds`).  Никаких новых аксиом проект не вводит.

Единственная поправка, зафиксированная аудитом: LAW-014 (ассоциативность
слияния) **не выполняется** для напечатанной пятизначной таблицы
(`joinSpec_not_assoc` в `Epistemic.lean`).  Поэтому законы слияния
(LAW-013 – LAW-015) сформулированы для исправленной алгебры свидетельств
`Belief`, которая сохраняет вердикты Torture Set; расхождение с
напечатанной таблицей локализовано и доказано (`spec_disagreement_eq`).
-/
import RequestProject.OSA4.TortureSet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Polymath.OSA4

/-- Идентификаторы законов ядра OSA-4.0. -/
inductive LawId
  | LAW_001 | LAW_002 | LAW_003 | LAW_004 | LAW_005 | LAW_006
  | LAW_007 | LAW_008 | LAW_009 | LAW_010 | LAW_011 | LAW_012
  | LAW_013 | LAW_014 | LAW_015 | LAW_016 | LAW_017 | LAW_018
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace LawId

/-- Название закона по кодексу. -/
def title : LawId → String
  | .LAW_001 => "Type Reflexivity"
  | .LAW_002 => "Type Transitivity"
  | .LAW_003 => "State Conservation"
  | .LAW_004 => "No Resurrection"
  | .LAW_005 => "Consume Safety"
  | .LAW_006 => "Destroy / Predicate Liveness Safety"
  | .LAW_007 => "Liveness Soundness"
  | .LAW_008 => "Effect Monotonicity / Effect Monoid"
  | .LAW_009 => "Epistemic Non-Overclaim"
  | .LAW_010 => "Composition Soundness"
  | .LAW_011 => "Effect Authorization Soundness"
  | .LAW_012 => "Predicate Transformer (WP) Soundness"
  | .LAW_013 => "Join Commutativity"
  | .LAW_014 => "Join Associativity"
  | .LAW_015 => "Join Idempotence"
  | .LAW_016 => "Recreation Identity"
  | .LAW_017 => "Predicate Invalidation Soundness"
  | .LAW_018 => "Repair Soundness"

/-- Формальное содержание закона. -/
def holds : LawId → Prop
  | .LAW_001 => ∀ (L : TypeLattice) (a : TypeTag), L.IsSubtype a a
  | .LAW_002 => ∀ (L : TypeLattice) (a b c : TypeTag),
      L.IsSubtype a b → L.IsSubtype b c → L.IsSubtype a c
  | .LAW_003 => ∀ (o : Op) (s : KState),
      (∀ f : FactId, f ∉ o.kill → f ∉ o.produces →
        (o.exec s).factStatus f = s.factStatus f) ∧
      (∀ v : VarName, v ∉ o.modifies → (o.exec s).varValue v = s.varValue v)
  | .LAW_004 => ∀ (w : World) (st : Step) (i : ObjId),
      Step.legal w st = true → w.phaseOf i = some .Destroyed →
        (Step.apply w st).phaseOf i ≠ some .Available
  | .LAW_005 => ∀ (w : World) (i : ObjId),
      Step.legal w (.consume i) = true ↔ w.phaseOf i = some .Available
  | .LAW_006 => ∀ (o : Op) (s : KState) (f : FactId),
      f ∈ o.kill → f ∉ o.produces →
        eval (o.exec s) (.factExists f) ≠ .TRUE_KNOWN
  | .LAW_007 => ∀ sc : Scenario,
      (compile sc).verdict = .PASS → livenessViolation sc.goal sc.chain = none
  | .LAW_008 => ∀ l₁ l₂ : List EffectLevel,
      EffectLevel.aggregate (l₁ ++ l₂) =
        EffectLevel.join (EffectLevel.aggregate l₁) (EffectLevel.aggregate l₂)
  | .LAW_009 => ∀ (l : List UStep) (a : UStep), UChain (a :: l) →
      (∀ s ∈ a :: l, s.honest) → (∀ s ∈ a :: l, s.evidence = false) →
        a.uIn ≤ (List.getLast (a :: l) (by simp)).uOut
  | .LAW_010 => ∀ (a b : Op) (s : KState),
      (a.enabled s ∧ b.enabled (a.exec s)) ↔
        ∃ s' : KState, a.enabled s ∧ s' = a.exec s ∧ b.enabled s'
  | .LAW_011 => ∀ (s : KState) (o : Op), execAllowed s o → authStatus s o = .TRUE_KNOWN
  | .LAW_012 => ∀ (o : Op) (s : KState) (q : Pred),
      eval s (wp o q) = .TRUE_KNOWN → eval (o.exec s) q = .TRUE_KNOWN
  | .LAW_013 => ∀ a b : Belief, Belief.join a b = Belief.join b a
  | .LAW_014 => ∀ a b c : Belief,
      Belief.join (Belief.join a b) c = Belief.join a (Belief.join b c)
  | .LAW_015 => ∀ a : Belief, Belief.join a a = a
  | .LAW_016 => ∀ (w : World) (old new : ObjId),
      Step.legal w (.recreate old new) = true → new ≠ old
  | .LAW_017 => ∀ (o : Op) (s : KState) (f : FactId),
      f ∈ o.kill → f ∉ o.produces →
        eval (o.exec s) (.pnot (.factExists f)) ≠ .TRUE_KNOWN
  | .LAW_018 => ∀ (s : KState) (goal : Pred) (plans : List RepairPlan),
      (∀ p ∈ plans, p.sound s goal) → ∀ v : RVec,
        RVec.best (plans.map RepairPlan.vec) = some v →
          ∃ p ∈ plans, p.vec = v ∧ p.sound s goal ∧ ∀ q ∈ plans, RVec.le v q.vec

end LawId

/-- **Все 18 законов ядра OSA-4.0 доказаны.** -/
theorem lawbook_holds : ∀ l : LawId, l.holds := by
  intro l
  cases l with
  | LAW_001 => exact fun L a => L.isSubtype_refl a
  | LAW_002 => exact fun _ _ _ _ hab hbc => TypeLattice.isSubtype_trans _ hab hbc
  | LAW_003 =>
      exact fun o s =>
        ⟨fun f hk hp => factStatus_exec_untouched o s hk hp,
         fun v hv => varValue_exec_untouched o s hv⟩
  | LAW_004 => exact fun w st i hleg hd => law004_no_resurrection w st i hleg hd
  | LAW_005 => exact fun w i => law005_consume_iff_available w i
  | LAW_006 => exact fun o s f hk hp => law006_kill_live_fact o s hk hp
  | LAW_007 => exact fun sc h => pass_no_liveness_violation sc h
  | LAW_008 => exact fun l₁ l₂ => EffectLevel.aggregate_append l₁ l₂
  | LAW_009 => exact law009_no_overclaim
  | LAW_010 => exact fun a b s => law010_composition_sound a b s
  | LAW_011 => exact fun _ _ h => law011_exec_implies_authorized h
  | LAW_012 => exact fun o s q h => law012_wp_sound o s q h
  | LAW_013 => exact Belief.join_comm
  | LAW_014 => exact Belief.join_assoc
  | LAW_015 => exact Belief.join_idem
  | LAW_016 => exact fun w old new h => law016_recreate_new_id w old new h
  | LAW_017 => exact fun o s f hk hp => law017_invalidate_not_refute o s hk hp
  | LAW_018 => exact fun s goal plans hsound _ hbest => law018_repair_sound s goal plans hsound hbest

/-- Законов ровно восемнадцать. -/
theorem lawbook_card : Fintype.card LawId = 18 := by decide

/-- **Поправка аудита.**  Для напечатанной пятизначной таблицы слияния
LAW-014 не выполняется; закон верен для исправленной алгебры свидетельств. -/
theorem law014_fails_for_printed_table :
    (¬ ∀ x y z : EV, joinSpec (joinSpec x y) z = joinSpec x (joinSpec y z)) ∧
    LawId.LAW_014.holds :=
  ⟨joinSpec_not_assoc, lawbook_holds .LAW_014⟩

end Polymath.OSA4
