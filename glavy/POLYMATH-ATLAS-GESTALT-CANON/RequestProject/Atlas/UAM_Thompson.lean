import Mathlib.Tactic
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_RegularExpression
import RequestProject.Atlas.UAM_EpsilonNFA
import RequestProject.Atlas.UAM_DFAEval

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace UAM_Thompson

noncomputable section
open Classical

open UAM_RegularExpression UAM_RegularExpression.RegExp
open UAM_EpsilonNFA UAM_EpsilonNFA.EpsilonNFA

universe u

/-- States in the Thompson automaton.  Every expression has distinguished
entry and exit states; compound expressions contain tagged copies of the
states of their immediate subexpressions. -/
inductive ThompsonState {α : Type u} : RegExp α → Type u
  | entry {r} : ThompsonState r
  | exit {r} : ThompsonState r
  | left {r s} : ThompsonState r → ThompsonState (.alt r s)
  | right {r s} : ThompsonState s → ThompsonState (.alt r s)
  | first {r s} : ThompsonState r → ThompsonState (.concat r s)
  | second {r s} : ThompsonState s → ThompsonState (.concat r s)
  | body {r} : ThompsonState r → ThompsonState (.star r)

noncomputable instance instDecidableEqThompsonState {α : Type u} {r : RegExp α} :
    DecidableEq (ThompsonState r) := Classical.decEq _

private def ThompsonState.all {α : Type u} : (r : RegExp α) → List (ThompsonState r)
  | .empty_set => [.entry, .exit]
  | .empty_str => [.entry, .exit]
  | .atom _ => [.entry, .exit]
  | .alt r s => [.entry, .exit] ++ (all r).map .left ++ (all s).map .right
  | .concat r s => [.entry, .exit] ++ (all r).map .first ++ (all s).map .second
  | .star r => [.entry, .exit] ++ (all r).map .body

private theorem ThompsonState.mem_all {α : Type u} :
    ∀ {r : RegExp α} (q : ThompsonState r), q ∈ ThompsonState.all r
  | r, .entry => by cases r <;> simp [ThompsonState.all]
  | r, .exit => by cases r <;> simp [ThompsonState.all]
  | _, .left q => by simp [ThompsonState.all, ThompsonState.mem_all q]
  | _, .right q => by simp [ThompsonState.all, ThompsonState.mem_all q]
  | _, .first q => by simp [ThompsonState.all, ThompsonState.mem_all q]
  | _, .second q => by simp [ThompsonState.all, ThompsonState.mem_all q]
  | _, .body q => by simp [ThompsonState.all, ThompsonState.mem_all q]

noncomputable instance instFintypeThompsonState {α : Type u} {r : RegExp α} :
    Fintype (ThompsonState r) := Fintype.ofList (ThompsonState.all r) ThompsonState.mem_all

@[simp] private def thompsonAccepting {α : Type u} :
    (r : RegExp α) → Set (ThompsonState r)
  | .alt r s =>
      (ThompsonState.left '' thompsonAccepting r) ∪
        (ThompsonState.right '' thompsonAccepting s)
  | _ => {.exit}

/-- Thompson transition relation, including epsilon-labelled edges. -/
def thompsonTransition {α : Type u} :
    (r : RegExp α) → ThompsonState r → Option α → Set (ThompsonState r)
  | .empty_set, _, _ => ∅
  | .empty_str, .entry, none => {.exit}
  | .empty_str, _, _ => ∅
  | .atom a, .entry, some b => if a = b then {.exit} else ∅
  | .atom _, _, _ => ∅
  | .alt _ _, .entry, none => {.left .entry, .right .entry}
  | .alt r _, .left q, x => ThompsonState.left '' thompsonTransition r q x
  | .alt _ s, .right q, x => ThompsonState.right '' thompsonTransition s q x
  | .alt _ _, _, _ => ∅
  | .concat _ _, .entry, none => {.first .entry}
  | .concat r _, .first q, x =>
      (ThompsonState.first '' thompsonTransition r q x) ∪
        (if q ∈ thompsonAccepting r ∧ x = none then {.second .entry} else ∅)
  | .concat _ s, .second q, x =>
      (ThompsonState.second '' thompsonTransition s q x) ∪
        (if q ∈ thompsonAccepting s ∧ x = none then {.exit} else ∅)
  | .concat _ _, _, _ => ∅
  | .star _, .entry, none => {.exit, .body .entry}
  | .star r, .body q, x =>
      (ThompsonState.body '' thompsonTransition r q x) ∪
        (if q ∈ thompsonAccepting r ∧ x = none then {.exit, .body .entry} else ∅)
  | .star _, _, _ => ∅

/-- The epsilon-NFA obtained from a regular expression by Thompson's construction. -/
def thompsonNFA {α : Type u} (r : RegExp α) : EpsilonNFA α (ThompsonState r) where
  δ := thompsonTransition r
  q₀ := .entry
  F := thompsonAccepting r

/-- A word-labelled run, with epsilon closure before every consumed symbol and
at the end.  This is a relational presentation of `eEval`. -/
def EpsilonRun {α Q : Type u} [DecidableEq Q] (A : EpsilonNFA α Q) :
    Q → UAM_Free.FreeMonoid α → Q → Prop
  | q, [], q' => Relation.ReflTransGen A.epsStep q q'
  | q, a :: w, q' => ∃ p t, Relation.ReflTransGen A.epsStep q p ∧
      t ∈ A.δ p (some a) ∧ EpsilonRun A t w q'

private theorem mem_eEval_iff_run {α Q : Type u} [DecidableEq Q]
    (A : EpsilonNFA α Q) (S : Set Q) (w : UAM_Free.FreeMonoid α) (q' : Q) :
    q' ∈ A.eEval S w ↔ ∃ q ∈ S, EpsilonRun A q w q' := by
  induction' w with a w ih generalizing S q';
  · simp +decide [ EpsilonRun, EpsilonNFA.eEval, EpsilonNFA.epsilonClosure ];
  · simp +decide [ EpsilonRun, ih, EpsilonNFA.eEval ];
    simp only [EpsilonNFA.eStepSet, EpsilonNFA.epsilonClosure,
      Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, ⟨p, ⟨q, hqS, hqp⟩, hpt⟩, ht⟩
      exact ⟨q, hqS, p, hqp, t, hpt, ht⟩
    · rintro ⟨q, hqS, p, hqp, t, hpt, ht⟩
      exact ⟨t, ⟨p, ⟨q, hqS, hqp⟩, hpt⟩, ht⟩

private theorem mem_epsilonLanguage_iff_run {α Q : Type u} [DecidableEq Q]
    (A : EpsilonNFA α Q) (w : UAM_Free.FreeMonoid α) :
    w ∈ A.epsilonLanguage ↔ ∃ f ∈ A.F, EpsilonRun A A.q₀ w f := by
  constructor;
  · intro hw
    obtain ⟨q', hq', hq'_acc⟩ : ∃ q' ∈ A.eEval {A.q₀} w, q' ∈ A.F := by
      exact hw;
    obtain ⟨q, hq, hrun⟩ := (mem_eEval_iff_run A {A.q₀} w q').1 hq'
    have hqq : q = A.q₀ := Set.mem_singleton_iff.mp hq
    subst q
    exact ⟨q', hq'_acc, hrun⟩
  · rintro ⟨ f, hf, h ⟩;
    exact ⟨ f, by
      exact ⟨ by simpa using mem_eEval_iff_run _ _ _ _ |>.2 ⟨ _, by simp, h ⟩, hf ⟩ ⟩

private theorem thompson_empty_set_correct {α : Type u} :
    epsilonLanguage (thompsonNFA (.empty_set : RegExp α)) = languageOf .empty_set := by
  ext w;
  constructor;
  · rintro ⟨ q, hq ⟩;
    cases w <;> cases q;
    · cases hq.2;
    · simp_all +decide [ UAM_EpsilonNFA.EpsilonNFA.eReachable ];
      cases hq.1;
      rename_i h₁ h₂;
      cases h₂.2 ; simp_all +decide [ thompsonNFA ];
      cases ‹ThompsonState empty_set› <;> tauto;
    · cases hq.2;
    · unfold thompsonNFA at hq; simp_all +decide [ UAM_EpsilonNFA.EpsilonNFA.eReachable ] ;
      rename_i a w; contrapose! hq; simp_all +decide [ EpsilonNFA.eEval ] ;
      induction w <;> simp_all +decide [ EpsilonNFA.eEval, EpsilonNFA.eStepSet, EpsilonNFA.epsilonClosure ];
      · rintro x y hxy hx; rcases x with ( _ | _ | x ) <;> rcases y with ( _ | _ | y ) <;> tauto;
      · rename_i k hk ih; specialize ih; simp_all +decide [ thompsonTransition ] ;
  · intro hw
    exact False.elim hw

private theorem thompson_empty_str_correct {α : Type u} :
    epsilonLanguage (thompsonNFA (.empty_str : RegExp α)) = languageOf .empty_str := by
  convert Set.ext _;
  intro w;
  constructor;
  · rintro ⟨ q, hq ⟩;
    cases w <;> simp_all +decide [ thompsonNFA ];
    cases hq.2 ; simp_all +decide [ UAM_EpsilonNFA.EpsilonNFA.eReachable ];
    induction' ‹List α› with a w ih <;> simp_all +decide [ UAM_EpsilonNFA.EpsilonNFA.eEval, UAM_EpsilonNFA.EpsilonNFA.eStepSet ];
    · simp_all +decide [ UAM_EpsilonNFA.EpsilonNFA.epsilonClosure, thompsonTransition ];
    · contrapose! hq; simp_all +decide [ thompsonTransition ] ;
  · intro hw
    obtain ⟨q, hq⟩ : ∃ q ∈ (thompsonNFA (UAM_RegularExpression.RegExp.empty_str : UAM_RegularExpression.RegExp α)).epsilonClosure { (ThompsonState.entry : ThompsonState (UAM_RegularExpression.RegExp.empty_str : UAM_RegularExpression.RegExp α)) }, q = ThompsonState.exit ∧ w = [] := by
      exact ⟨ ThompsonState.exit, ⟨ ThompsonState.entry, by tauto, by tauto ⟩, rfl, by simpa using hw ⟩;
    refine ⟨q, ?_, ?_⟩
    · simpa [EpsilonNFA.eReachable, hq.2.2] using hq.1
    · simpa [thompsonNFA] using hq.2.1

private theorem thompson_atom_correct {α : Type u} (a : α) :
    epsilonLanguage (thompsonNFA (.atom a)) = languageOf (.atom a) := by
  -- Let's unfold the definition of `epsilonLanguage` and `languageOf`.
  ext w
  simp [epsilonLanguage, languageOf];
  constructor <;> intro h <;> simp_all +decide [ thompsonNFA, EpsilonNFA.eAccepts ];
  · unfold UAM_EpsilonNFA.EpsilonNFA.eReachable at h;
    rcases w with ( _ | ⟨ b, _ | ⟨ c, w ⟩ ⟩ ) <;> simp_all +decide [ UAM_EpsilonNFA.EpsilonNFA.eEval ];
    · simp_all +decide [ UAM_EpsilonNFA.EpsilonNFA.epsilonClosure ];
      cases h;
      cases ‹ThompsonState ( atom a ) › <;> tauto;
    · simp_all +decide [ UAM_EpsilonNFA.EpsilonNFA.epsilonClosure, UAM_EpsilonNFA.EpsilonNFA.eStepSet ];
      rcases h with ⟨ q, ⟨ i, hi, hq ⟩, hq' ⟩ ; rcases i with ( _ | _ | i ) <;> rcases q with ( _ | _ | q ) <;> simp_all +decide [ thompsonTransition ] ;
      rfl;
    · contrapose! h;
      simp +decide [ UAM_EpsilonNFA.EpsilonNFA.eStepSet, UAM_EpsilonNFA.EpsilonNFA.epsilonClosure ];
      induction w <;> simp_all +decide [ UAM_EpsilonNFA.EpsilonNFA.eEval ];
      · simp +decide [ UAM_EpsilonNFA.EpsilonNFA.epsilonClosure ];
        rintro x y hxy z hz w hw hw';
        cases y <;> cases z <;> cases w <;> cases x <;> simp_all +decide [ thompsonTransition ];
        cases hw;
        rename_i k hk₁ hk₂;
        cases k <;> cases hk₂;
      · rename_i k hk;
        convert hk _ using 1;
        · congr! 2;
          ext; simp [UAM_EpsilonNFA.EpsilonNFA.eStepSet, UAM_EpsilonNFA.EpsilonNFA.epsilonClosure];
          constructor <;> rintro ⟨ i, hi, j, hj, k, hk, hk' ⟩ <;> use i, hi, j, hj, k, hk;
          · cases i <;> cases j <;> cases k <;> simp_all +decide [ thompsonTransition ];
            cases hk;
            cases ‹ThompsonState ( atom a ) › <;> tauto;
          · cases i ; cases j ; cases k ; simp_all +decide [ thompsonTransition ];
            · cases hk';
            · cases k ; simp_all +decide [ thompsonTransition ];
              · cases hk;
                rename_i x hx₁ hx₂;
                cases x ; simp_all +decide [ UAM_EpsilonNFA.EpsilonNFA.epsStep ]; all_goals cases hx₂;
              · cases hk';
            · cases hj;
        · exact fun h' => h <| by simpa [ UAM_Free.FreeMonoid.of ] using congr_arg ( fun x => x ++ [ ‹_› ] ) h';
  · refine' ⟨ ThompsonState.exit, _, _ ⟩;
    · refine' Set.mem_iUnion₂.mpr ⟨ ThompsonState.entry, _, _ ⟩ <;> norm_num [ thompsonTransition ];
      exact ⟨ ThompsonState.entry, Set.mem_singleton _, Relation.ReflTransGen.refl ⟩;
    · rfl

private theorem alt_left_run {α : Type u} (r s : RegExp α)
    {q q' : ThompsonState r} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA r) q w q') :
    EpsilonRun (thompsonNFA (.alt r s)) (.left q) w (.left q') := by
  induction w generalizing q q' with
  | nil =>
      exact h.lift (fun x => ThompsonState.left (s := s) x)
        (fun {a b} hab => by
          change ThompsonState.left b ∈ thompsonTransition (.alt r s)
            (ThompsonState.left a) none
          exact Set.mem_image_of_mem _ hab)
  | cons a w ih =>
      obtain ⟨p, t, hp, ht, hw⟩ := h
      exact ⟨.left p, .left t,
        hp.lift (fun x => ThompsonState.left (s := s) x)
          (fun {a b} hab => by
            change ThompsonState.left b ∈ thompsonTransition (.alt r s)
              (ThompsonState.left a) none
            exact Set.mem_image_of_mem _ hab),
        Set.mem_image_of_mem _ ht, ih hw⟩

private theorem alt_right_run {α : Type u} (r s : RegExp α)
    {q q' : ThompsonState s} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA s) q w q') :
    EpsilonRun (thompsonNFA (.alt r s)) (.right q) w (.right q') := by
  induction w generalizing q q' with
  | nil =>
      exact h.lift (fun x => ThompsonState.right (r := r) x)
        (fun {a b} hab => by
          change ThompsonState.right b ∈ thompsonTransition (.alt r s)
            (ThompsonState.right a) none
          exact Set.mem_image_of_mem _ hab)
  | cons a w ih =>
      obtain ⟨p, t, hp, ht, hw⟩ := h
      exact ⟨.right p, .right t,
        hp.lift (fun x => ThompsonState.right (r := r) x)
          (fun {a b} hab => by
            change ThompsonState.right b ∈ thompsonTransition (.alt r s)
              (ThompsonState.right a) none
            exact Set.mem_image_of_mem _ hab),
        Set.mem_image_of_mem _ ht, ih hw⟩

private theorem alt_left_eps_inv {α : Type u} (r s : RegExp α)
    {q q' : ThompsonState r}
    (h : Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.left q) (.left q')) :
    Relation.ReflTransGen (thompsonNFA r).epsStep q q' := by
  have step_inv : ∀ p p' : ThompsonState (.alt r s), ∀ q'' : ThompsonState r,
      (thompsonNFA (.alt r s)).epsStep p p' → p = .left q'' →
      ∃ q' : ThompsonState r, p' = .left q' ∧ (thompsonNFA r).epsStep q'' q' := by
    intro p p' q'' h_eps hp
    rw [hp] at h_eps
    simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps ⊢
    obtain ⟨x, hx, hx'⟩ := h_eps
    exact ⟨x, hx'.symm, hx⟩
  have H : ∀ p : ThompsonState (.alt r s),
      Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.left q) p →
      ∃ q'' : ThompsonState r, p = .left q'' ∧ Relation.ReflTransGen (thompsonNFA r).epsStep q q'' := by
    intro p hp
    induction hp with
    | refl => exact ⟨q, rfl, Relation.ReflTransGen.refl⟩
    | tail b c ih =>
      obtain ⟨q'', hq'', hq'''⟩ := ih
      obtain ⟨q''', hp''', hq''''⟩ := step_inv _ _ q'' c hq''
      exact ⟨q''', hp''', hq'''.trans (Relation.ReflTransGen.single hq'''')⟩
  obtain ⟨q'', hq'', hq'''⟩ := H (.left q') h
  have : q' = q'' := by injection hq''
  rw [this]
  exact hq'''

private theorem alt_right_eps_inv {α : Type u} (r s : RegExp α)
    {q q' : ThompsonState s}
    (h : Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.right q) (.right q')) :
    Relation.ReflTransGen (thompsonNFA s).epsStep q q' := by
  have step_inv : ∀ p p' : ThompsonState (.alt r s), ∀ q'' : ThompsonState s,
      (thompsonNFA (.alt r s)).epsStep p p' → p = .right q'' →
      ∃ q' : ThompsonState s, p' = .right q' ∧ (thompsonNFA s).epsStep q'' q' := by
    intro p p' q'' h_eps hp
    rw [hp] at h_eps
    simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps ⊢
    obtain ⟨x, hx, hx'⟩ := h_eps
    exact ⟨x, hx'.symm, hx⟩
  have H : ∀ p : ThompsonState (.alt r s),
      Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.right q) p →
      ∃ q'' : ThompsonState s, p = .right q'' ∧ Relation.ReflTransGen (thompsonNFA s).epsStep q q'' := by
    intro p hp
    induction hp with
    | refl => exact ⟨q, rfl, Relation.ReflTransGen.refl⟩
    | tail b c ih =>
      obtain ⟨q'', hq'', hq'''⟩ := ih
      obtain ⟨q''', hp''', hq''''⟩ := step_inv _ _ q'' c hq''
      exact ⟨q''', hp''', hq'''.trans (Relation.ReflTransGen.single hq'''')⟩
  obtain ⟨q'', hq'', hq'''⟩ := H (.right q') h
  have : q' = q'' := by injection hq''
  rw [this]
  exact hq'''

private theorem alt_left_run_inv {α : Type u} (r s : RegExp α)
    {q q' : ThompsonState r} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA (.alt r s)) (.left q) w (.left q')) :
    EpsilonRun (thompsonNFA r) q w q' := by
  induction w generalizing q q' with
  | nil =>
    simp [EpsilonRun] at h ⊢
    exact alt_left_eps_inv r s h
  | cons a w ih =>
    simp [EpsilonRun] at h ⊢
    obtain ⟨p, hp, x, hx, hw⟩ := h
    cases p with
    | entry =>
        have : (thompsonNFA (r.alt s)).δ ThompsonState.entry (some a) = ∅ := by
          simp [thompsonNFA, thompsonTransition]
        rw [this] at hx; exact hx.elim
    | exit =>
        have : (thompsonNFA (r.alt s)).δ ThompsonState.exit (some a) = ∅ := by
          simp [thompsonNFA, thompsonTransition]
        rw [this] at hx; exact hx.elim
    | left p' =>
        have htrans : (thompsonNFA (r.alt s)).δ p'.left (some a) = ThompsonState.left '' (thompsonTransition r p' a) := by
          simp [thompsonNFA, thompsonTransition]
        rw [htrans] at hx
        obtain ⟨x', hx', rfl⟩ := hx
        exact ⟨p', alt_left_eps_inv r s hp, x', hx', ih hw⟩
    | right p' =>
        -- Epsilon transitions from .left states only reach .left states
        have h_eps_left : ∀ {q₁ : ThompsonState r} {q'' : ThompsonState (r.alt s)},
            q'' ∈ (thompsonNFA (r.alt s)).δ (ThompsonState.left q₁) none →
            ∃ q' : ThompsonState r, q'' = ThompsonState.left q' := by
          intro q₁ q'' hq''
          simp [thompsonNFA, thompsonTransition] at hq'' ⊢
          obtain ⟨q', hq', rfl⟩ := hq''
          exact ⟨q', rfl⟩
        -- By induction on ReflTransGen, all reachable states are .left
        have h_reflexive : ∀ {q₁ : ThompsonState r} {q'' : ThompsonState (r.alt s)},
            Relation.ReflTransGen (thompsonNFA (r.alt s)).epsStep (ThompsonState.left q₁) q'' →
            ∃ q' : ThompsonState r, q'' = ThompsonState.left q' := by
          intro q₁ q'' hq''
          induction hq'' with
          | refl => exact ⟨q₁, rfl⟩
          | @tail _ _ _ ih₁ ih₂ =>
            obtain ⟨q', hq'⟩ := ih₂
            rw [hq'] at ih₁
            exact h_eps_left ih₁
        obtain ⟨q', hq'⟩ := h_reflexive hp
        cases hq'

private theorem alt_right_run_inv {α : Type u} (r s : RegExp α)
    {q q' : ThompsonState s} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA (.alt r s)) (.right q) w (.right q')) :
    EpsilonRun (thompsonNFA s) q w q' := by
  induction w generalizing q q' with
  | nil =>
    simp [EpsilonRun] at h ⊢
    exact alt_right_eps_inv r s h
  | cons a w ih =>
    simp [EpsilonRun] at h ⊢
    obtain ⟨p, hp, x, hx, hw⟩ := h
    cases p with
    | entry =>
        have : (thompsonNFA (r.alt s)).δ ThompsonState.entry (some a) = ∅ := by
          simp [thompsonNFA, thompsonTransition]
        rw [this] at hx; exact hx.elim
    | exit =>
        have : (thompsonNFA (r.alt s)).δ ThompsonState.exit (some a) = ∅ := by
          simp [thompsonNFA, thompsonTransition]
        rw [this] at hx; exact hx.elim
    | left p' =>
        -- Epsilon transitions from .right states only reach .right states
        have h_eps_right : ∀ {q₁ : ThompsonState s} {q'' : ThompsonState (r.alt s)},
            q'' ∈ (thompsonNFA (r.alt s)).δ (ThompsonState.right q₁) none →
            ∃ q' : ThompsonState s, q'' = ThompsonState.right q' := by
          intro q₁ q'' hq''
          simp [thompsonNFA, thompsonTransition] at hq'' ⊢
          obtain ⟨q', hq', rfl⟩ := hq''
          exact ⟨q', rfl⟩
        -- By induction on ReflTransGen, all reachable states are .right
        have h_reflexive : ∀ {q₁ : ThompsonState s} {q'' : ThompsonState (r.alt s)},
            Relation.ReflTransGen (thompsonNFA (r.alt s)).epsStep (ThompsonState.right q₁) q'' →
            ∃ q' : ThompsonState s, q'' = ThompsonState.right q' := by
          intro q₁ q'' hq''
          induction hq'' with
          | refl => exact ⟨q₁, rfl⟩
          | @tail _ _ _ ih₁ ih₂ =>
            obtain ⟨q', hq'⟩ := ih₂
            rw [hq'] at ih₁
            exact h_eps_right ih₁
        obtain ⟨q', hq'⟩ := h_reflexive hp
        cases hq'
    | right p' =>
        have htrans : (thompsonNFA (r.alt s)).δ p'.right (some a) = ThompsonState.right '' (thompsonTransition s p' a) := by
          simp [thompsonNFA, thompsonTransition]
        rw [htrans] at hx
        obtain ⟨x', hx', rfl⟩ := hx
        exact ⟨p', alt_right_eps_inv r s hp, x', hx', ih hw⟩

private theorem epsilonRun_append {α Q : Type u} [DecidableEq Q]
    (A : EpsilonNFA α Q) {q q' q'' : Q} {w w' : UAM_Free.FreeMonoid α}
    (h : EpsilonRun A q w q') (h' : EpsilonRun A q' w' q'') :
    EpsilonRun A q (w ++ w') q'' := by
  induction' w with a w ih generalizing q q' q'';
  · induction' w' with a w' ih generalizing q q' q'';
    · exact Relation.ReflTransGen.trans h h';
    · obtain ⟨ p, t, hp, ht, h' ⟩ := h';
      exact ⟨ p, t, by exact Relation.ReflTransGen.trans h hp, ht, h' ⟩;
  · cases h;
    obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := ‹_›;
    exact ⟨ _, _, ht₁, ht₂, ih ht₃ h' ⟩

private theorem alt_left_accepting_run {α : Type u} (r s : RegExp α)
    {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA r) .entry w .exit) :
    EpsilonRun (thompsonNFA (.alt r s)) .entry w (.left .exit) := by
  have hpre : EpsilonRun (thompsonNFA (.alt r s)) .entry [] (.left .entry) := by
    exact Relation.ReflTransGen.single (Set.mem_union_left _ (Set.mem_singleton _))
  simpa using epsilonRun_append _ hpre (alt_left_run r s h)

private theorem alt_right_accepting_run {α : Type u} (r s : RegExp α)
    {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA s) .entry w .exit) :
    EpsilonRun (thompsonNFA (.alt r s)) .entry w (.right .exit) := by
  have hpre : EpsilonRun (thompsonNFA (.alt r s)) .entry [] (.right .entry) := by
    exact Relation.ReflTransGen.single (Set.mem_union_right _ (Set.mem_singleton _))
  simpa using epsilonRun_append _ hpre (alt_right_run r s h)

private theorem alt_entry_left_run_inv {α : Type u} (r s : RegExp α)
    {q' : ThompsonState r} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA (.alt r s)) .entry w (.left q')) :
    EpsilonRun (thompsonNFA r) .entry w q' := by
  induction w generalizing q' with
  | nil =>
    simp [EpsilonRun] at h ⊢
    -- h : Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep .entry (.left q')
    -- From .right states we can only reach .right states
    have right_only : ∀ {q'' : ThompsonState s} {q : ThompsonState (.alt r s)},
        Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.right q'') q →
        ∃ q' : ThompsonState s, q = .right q' := by
      intro q'' q hgen
      have step_inv : ∀ p' : ThompsonState (.alt r s), ∀ q''' : ThompsonState s,
          (thompsonNFA (.alt r s)).epsStep (.right q''') p' →
          ∃ q' : ThompsonState s, p' = .right q' := by
        intro p' q''' h_eps
        simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps ⊢
        obtain ⟨x, _, hx⟩ := h_eps
        exact ⟨x, hx.symm⟩
      induction hgen with
      | refl => exact ⟨q'', rfl⟩
      | tail p step ih =>
        obtain ⟨q', hq'⟩ := ih
        rw [hq'] at step
        obtain ⟨q'', hq''⟩ := step_inv _ q' step
        exact ⟨q'', hq''⟩
    have first_step : ∀ p : ThompsonState (.alt r s),
        (thompsonNFA (.alt r s)).epsStep .entry p →
        p = .left .entry ∨ p = .right .entry := by
      intro p hp
      simp [EpsilonNFA.epsStep, thompsonNFA] at hp ⊢
      exact hp
    have first_step' : ∀ {a b : ThompsonState (.alt r s)},
        Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep a b →
        a = b ∨ ∃ c, (thompsonNFA (.alt r s)).epsStep a c ∧ Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep c b := by
      intro a b hab
      induction hab with
      | refl => left; rfl
      | tail path step ih =>
        cases ih with
        | inl heq => right; subst heq; exact ⟨_, step, Relation.ReflTransGen.refl⟩
        | inr h' =>
          right
          obtain ⟨d, had, hdb⟩ := h'
          use d
          exact ⟨had, hdb.trans (Relation.ReflTransGen.single step)⟩
    rcases first_step' h with heq | ⟨b, hb1, hb2⟩
    · cases heq
    · rcases first_step b hb1 with hb3 | hb3
      · rw [hb3] at hb2; exact alt_left_eps_inv r s hb2
      · rw [hb3] at hb2
        obtain ⟨q'', hq''⟩ := right_only hb2
        have : q'.left = q''.right := hq''
        cases this
  | cons a w ih =>
    simp [EpsilonRun] at h ⊢
    obtain ⟨p, hp, x, hx, hw⟩ := h
    cases p with
    | entry =>
        have : (thompsonNFA (r.alt s)).δ ThompsonState.entry (some a) = ∅ := by
          simp [thompsonNFA, thompsonTransition]
        rw [this] at hx; exact hx.elim
    | exit =>
        have : (thompsonNFA (r.alt s)).δ ThompsonState.exit (some a) = ∅ := by
          simp [thompsonNFA, thompsonTransition]
        rw [this] at hx; exact hx.elim
    | left p' =>
        have htrans : (thompsonNFA (r.alt s)).δ p'.left (some a) = ThompsonState.left '' (thompsonTransition r p' a) := by
          simp [thompsonNFA, thompsonTransition]
        rw [htrans] at hx
        obtain ⟨x', hx', rfl⟩ := hx
        -- Decompose the epsilon path from .entry to p'.left
        have first_step : ∀ p : ThompsonState (.alt r s),
            (thompsonNFA (.alt r s)).epsStep .entry p →
            p = .left .entry ∨ p = .right .entry := by
          intro p hp
          simp [EpsilonNFA.epsStep, thompsonNFA] at hp ⊢
          exact hp
        have first_step' : ∀ {a b : ThompsonState (.alt r s)},
            Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep a b →
            a = b ∨ ∃ c, (thompsonNFA (.alt r s)).epsStep a c ∧ Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep c b := by
          intro a b hab
          induction hab with
          | refl => left; rfl
          | tail path step ih =>
            cases ih with
            | inl heq => right; subst heq; exact ⟨_, step, Relation.ReflTransGen.refl⟩
            | inr h' =>
              right
              obtain ⟨d, had, hdb⟩ := h'
              use d
              exact ⟨had, hdb.trans (Relation.ReflTransGen.single step)⟩
        rcases first_step' hp with heq | ⟨b, hb1, hb2⟩
        · cases heq
        · rcases first_step b hb1 with hb3 | hb3
          · rw [hb3] at hb2
            exact ⟨p', alt_left_eps_inv r s hb2, x', hx', alt_left_run_inv r s hw⟩
          · -- From .right .entry we can only reach .right states, so reaching .left p' is impossible
            have right_only : ∀ {q'' : ThompsonState s} {q : ThompsonState (.alt r s)},
                Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.right q'') q →
                ∃ q' : ThompsonState s, q = .right q' := by
              intro q'' q hgen
              have step_inv : ∀ p' : ThompsonState (.alt r s), ∀ q''' : ThompsonState s,
                  (thompsonNFA (.alt r s)).epsStep (.right q''') p' →
                  ∃ q' : ThompsonState s, p' = .right q' := by
                intro p' q''' h_eps
                simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps ⊢
                obtain ⟨x, _, hx⟩ := h_eps
                exact ⟨x, hx.symm⟩
              induction hgen with
              | refl => exact ⟨q'', rfl⟩
              | tail p step ih =>
                obtain ⟨q', hq'⟩ := ih
                rw [hq'] at step
                obtain ⟨q'', hq''⟩ := step_inv _ q' step
                exact ⟨q'', hq''⟩
            have right_run_only :
              ∀ (q'' : ThompsonState s) (q : ThompsonState (.alt r s)) (w : UAM_Free.FreeMonoid α),
                EpsilonRun (thompsonNFA (.alt r s)) (.right q'') w q → ∃ q' : ThompsonState s, q = .right q' := by
              suffices h : ∀ n, ∀ (q'' : ThompsonState s) (q : ThompsonState (.alt r s)) (w : UAM_Free.FreeMonoid α),
                  w.length = n → EpsilonRun (thompsonNFA (.alt r s)) (.right q'') w q →
                  ∃ q' : ThompsonState s, q = .right q' by
                intro q'' q w hrun
                exact h w.length q'' q w rfl hrun
              intro n
              induction n using Nat.strong_induction_on with
              | _ n ih =>
                intro q'' q w hw hrun
                unfold EpsilonRun at hrun
                cases w with
                | nil => exact right_only hrun
                | cons a rest =>
                  obtain ⟨p, t, hp, ht, hw'⟩ := hrun
                  obtain ⟨q', hp_eq⟩ := right_only hp
                  rw [hp_eq] at ht
                  simp [thompsonNFA, thompsonTransition] at ht
                  obtain ⟨t', _, ht_eq⟩ := ht
                  rw [ht_eq.symm] at hw'
                  have hlt : rest.length < n := by
                    rw [← hw]
                    exact Nat.lt_succ_self rest.length
                  exact ih rest.length hlt t' q rest rfl hw'
            rw [hb3] at hb2
            obtain ⟨q'', hq''⟩ := right_only hb2
            have : p'.left = q''.right := hq''
            cases this
    | right p' =>
        have htrans : (thompsonNFA (r.alt s)).δ p'.right (some a) = ThompsonState.right '' (thompsonTransition s p' a) := by
          simp [thompsonNFA, thompsonTransition]
        rw [htrans] at hx
        obtain ⟨x', hx', rfl⟩ := hx
        -- Decompose the epsilon path from .entry to p'.right
        have first_step : ∀ p : ThompsonState (.alt r s),
            (thompsonNFA (.alt r s)).epsStep .entry p →
            p = .left .entry ∨ p = .right .entry := by
          intro p hp
          simp [EpsilonNFA.epsStep, thompsonNFA] at hp ⊢
          exact hp
        have first_step' : ∀ {a b : ThompsonState (.alt r s)},
            Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep a b →
            a = b ∨ ∃ c, (thompsonNFA (.alt r s)).epsStep a c ∧ Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep c b := by
          intro a b hab
          induction hab with
          | refl => left; rfl
          | tail path step ih =>
            cases ih with
            | inl heq => right; subst heq; exact ⟨_, step, Relation.ReflTransGen.refl⟩
            | inr h' =>
              right
              obtain ⟨d, had, hdb⟩ := h'
              use d
              exact ⟨had, hdb.trans (Relation.ReflTransGen.single step)⟩
        rcases first_step' hp with heq | ⟨b, hb1, hb2⟩
        · cases heq
        · rcases first_step b hb1 with hb3 | hb3
          · -- From .left .entry we can only reach .left states, so reaching .right p' is impossible
            have left_only : ∀ {q'' : ThompsonState r} {q : ThompsonState (.alt r s)},
                Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.left q'') q →
                ∃ q' : ThompsonState r, q = .left q' := by
              intro q'' q hgen
              have step_inv : ∀ p' : ThompsonState (.alt r s), ∀ q''' : ThompsonState r,
                  (thompsonNFA (.alt r s)).epsStep (.left q''') p' →
                  ∃ q' : ThompsonState r, p' = .left q' := by
                intro p' q''' h_eps
                simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps ⊢
                obtain ⟨x, _, hx⟩ := h_eps
                exact ⟨x, hx.symm⟩
              induction hgen with
              | refl => exact ⟨q'', rfl⟩
              | tail p step ih =>
                obtain ⟨q', hq'⟩ := ih
                rw [hq'] at step
                obtain ⟨q'', hq''⟩ := step_inv _ q' step
                exact ⟨q'', hq''⟩
            rw [hb3] at hb2
            obtain ⟨q'', hq''⟩ := left_only hb2
            have : p'.right = q''.left := hq''
            cases this
          · rw [hb3] at hb2
            -- From .right x' we can only reach .right states, so reaching .left q' is impossible
            have right_only : ∀ {q'' : ThompsonState s} {q : ThompsonState (.alt r s)},
                Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.right q'') q →
                ∃ q' : ThompsonState s, q = .right q' := by
              intro q'' q hgen
              have step_inv : ∀ p' : ThompsonState (.alt r s), ∀ q''' : ThompsonState s,
                  (thompsonNFA (.alt r s)).epsStep (.right q''') p' →
                  ∃ q' : ThompsonState s, p' = .right q' := by
                intro p' q''' h_eps
                simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps ⊢
                obtain ⟨x, _, hx⟩ := h_eps
                exact ⟨x, hx.symm⟩
              induction hgen with
              | refl => exact ⟨q'', rfl⟩
              | tail p step ih =>
                obtain ⟨q', hq'⟩ := ih
                rw [hq'] at step
                obtain ⟨q'', hq''⟩ := step_inv _ q' step
                exact ⟨q'', hq''⟩
            -- hw is an epsilon run from .right x' to .left q', which is impossible
            unfold EpsilonRun at hw
            cases w with
            | nil =>
              exact absurd hw (by obtain ⟨q', hq'⟩ := right_only hw; cases hq')
            | cons a w =>
              obtain ⟨p, t, hp, ht, hw'⟩ := hw
              -- p = .right q' for some q'
              obtain ⟨q', hp_eq⟩ := right_only hp
              -- t ∈ δ (.right q') (some a) = .right '' (δ s q' a), so t = .right t'
              rw [hp_eq] at ht
              simp [thompsonNFA, thompsonTransition] at ht
              obtain ⟨t', _, ht_eq⟩ := ht
              -- hw' : EpsilonRun ... (.right t') w q'.left, which is impossible
              rw [ht_eq.symm] at hw'
              have right_run_only : ∀ {q'' : ThompsonState s} {q : ThompsonState (.alt r s)} {w : UAM_Free.FreeMonoid α},
                  EpsilonRun (thompsonNFA (.alt r s)) (.right q'') w q →
                  ∃ q' : ThompsonState s, q = .right q' := by
                suffices h : ∀ n, ∀ (q'' : ThompsonState s) (q : ThompsonState (.alt r s)) (w : UAM_Free.FreeMonoid α),
                    w.length = n → EpsilonRun (thompsonNFA (.alt r s)) (.right q'') w q →
                    ∃ q' : ThompsonState s, q = .right q' by
                  intro q'' q w hrun
                  exact h w.length q'' q w rfl hrun
                intro n
                induction n using Nat.strong_induction_on with
                | _ n ih =>
                  intro q'' q w hw hrun
                  unfold EpsilonRun at hrun
                  cases w with
                  | nil => exact right_only hrun
                  | cons a rest =>
                    obtain ⟨p, t, hp, ht, hw'⟩ := hrun
                    obtain ⟨q', hp_eq⟩ := right_only hp
                    rw [hp_eq] at ht
                    simp [thompsonNFA, thompsonTransition] at ht
                    obtain ⟨t', _, ht_eq⟩ := ht
                    rw [ht_eq.symm] at hw'
                    have hlt : rest.length < n := by
                      rw [← hw]
                      exact Nat.lt_succ_self rest.length
                    exact ih rest.length hlt t' q rest rfl hw'
              obtain ⟨q'', hq''⟩ := right_run_only hw'
              cases hq''

private theorem alt_entry_right_run_inv {α : Type u} (r s : RegExp α)
    {q' : ThompsonState s} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA (.alt r s)) .entry w (.right q')) :
    EpsilonRun (thompsonNFA s) .entry w q' := by
  induction w generalizing q' with
  | nil =>
    simp [EpsilonRun] at h ⊢
    -- h : Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep .entry (.right q')
    -- From .left states we can only reach .left states
    have left_only : ∀ {q'' : ThompsonState r} {q : ThompsonState (.alt r s)},
        Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.left q'') q →
        ∃ q' : ThompsonState r, q = .left q' := by
      intro q'' q hgen
      have step_inv : ∀ p' : ThompsonState (.alt r s), ∀ q''' : ThompsonState r,
          (thompsonNFA (.alt r s)).epsStep (.left q''') p' →
          ∃ q' : ThompsonState r, p' = .left q' := by
        intro p' q''' h_eps
        simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps ⊢
        obtain ⟨x, _, hx⟩ := h_eps
        exact ⟨x, hx.symm⟩
      induction hgen with
      | refl => exact ⟨q'', rfl⟩
      | tail p step ih =>
        obtain ⟨q', hq'⟩ := ih
        rw [hq'] at step
        obtain ⟨q'', hq''⟩ := step_inv _ q' step
        exact ⟨q'', hq''⟩
    have first_step : ∀ p : ThompsonState (.alt r s),
        (thompsonNFA (.alt r s)).epsStep .entry p →
        p = .left .entry ∨ p = .right .entry := by
      intro p hp
      simp [EpsilonNFA.epsStep, thompsonNFA] at hp ⊢
      exact hp
    have first_step' : ∀ {a b : ThompsonState (.alt r s)},
        Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep a b →
        a = b ∨ ∃ c, (thompsonNFA (.alt r s)).epsStep a c ∧ Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep c b := by
      intro a b hab
      induction hab with
      | refl => left; rfl
      | tail path step ih =>
        cases ih with
        | inl heq => right; subst heq; exact ⟨_, step, Relation.ReflTransGen.refl⟩
        | inr h' =>
          right
          obtain ⟨d, had, hdb⟩ := h'
          use d
          exact ⟨had, hdb.trans (Relation.ReflTransGen.single step)⟩
    rcases first_step' h with heq | ⟨b, hb1, hb2⟩
    · cases heq
    · rcases first_step b hb1 with hb3 | hb3
      · -- b = .left .entry case: all reachable states are .left
        have : b = ThompsonState.left ThompsonState.entry := hb3
        rw [this] at hb2
        obtain ⟨q'', hq''⟩ := left_only hb2
        have : q'.right = q''.left := hq''
        cases this
      · -- b = .right .entry case
        have : b = ThompsonState.right ThompsonState.entry := hb3
        rw [this] at hb2
        exact alt_right_eps_inv r s hb2
  | cons a w ih =>
    simp [EpsilonRun] at h ⊢
    obtain ⟨p, hp, x, hx, hw⟩ := h
    cases p with
    | entry =>
        have : (thompsonNFA (r.alt s)).δ ThompsonState.entry (some a) = ∅ := by
          simp [thompsonNFA, thompsonTransition]
        rw [this] at hx; exact hx.elim
    | exit =>
        have : (thompsonNFA (r.alt s)).δ ThompsonState.exit (some a) = ∅ := by
          simp [thompsonNFA, thompsonTransition]
        rw [this] at hx; exact hx.elim
    | left p' =>
        have htrans : (thompsonNFA (r.alt s)).δ p'.left (some a) = ThompsonState.left '' (thompsonTransition r p' a) := by
          simp [thompsonNFA, thompsonTransition]
        rw [htrans] at hx
        obtain ⟨x', hx', rfl⟩ := hx
        -- From .left .entry we can only reach .left states, so reaching .right q' is impossible
        have left_only : ∀ {q'' : ThompsonState r} {q : ThompsonState (.alt r s)},
            Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.left q'') q →
            ∃ q' : ThompsonState r, q = .left q' := by
          intro q'' q hgen
          have step_inv : ∀ p' : ThompsonState (.alt r s), ∀ q''' : ThompsonState r,
              (thompsonNFA (.alt r s)).epsStep (.left q''') p' →
              ∃ q' : ThompsonState r, p' = .left q' := by
            intro p' q''' h_eps
            simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps ⊢
            obtain ⟨x, _, hx⟩ := h_eps
            exact ⟨x, hx.symm⟩
          induction hgen with
          | refl => exact ⟨q'', rfl⟩
          | tail p step ih =>
            obtain ⟨q', hq'⟩ := ih
            rw [hq'] at step
            obtain ⟨q'', hq''⟩ := step_inv _ q' step
            exact ⟨q'', hq''⟩
        have reach_left : ∀ (z : ThompsonState r) (q : ThompsonState (.alt r s)),
            Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.left z) q →
            ∃ q' : ThompsonState r, q = .left q' := fun z q hp' => left_only hp'
        have no_right : ∀ (z : ThompsonState r) (w' : UAM_Free.FreeMonoid α),
            ¬ EpsilonRun (thompsonNFA (r.alt s)) (.left z) w' (.right q') := by
          intro z w'
          induction w' generalizing z with
          | nil =>
            intro p
            simp [EpsilonRun] at p
            obtain ⟨p'', hp''⟩ := reach_left z (.right q') p
            cases hp''
          | cons a' w'' ih' =>
            intro hp
            simp [EpsilonRun] at hp
            obtain ⟨p', hp, t, ht, hw''⟩ := hp
            obtain ⟨p'', hp''⟩ := reach_left z p' hp
            rw [hp''] at ht
            have htrans' : (thompsonNFA (r.alt s)).δ (.left p'') (some a') = ThompsonState.left '' (thompsonTransition r p'' a') := by
              simp [thompsonNFA, thompsonTransition]
            rw [htrans'] at ht
            obtain ⟨x_inner, hx_inner, hx_eq⟩ := ht
            rw [hx_eq.symm] at hw''
            exact ih' x_inner hw''
        exact False.elim (no_right x' w hw)
    | right p' =>
        have htrans : (thompsonNFA (r.alt s)).δ p'.right (some a) = ThompsonState.right '' (thompsonTransition s p' a) := by
          simp [thompsonNFA, thompsonTransition]
        rw [htrans] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        -- We need to show that from .right states in alt, we can only reach .right states via epsStep
        have right_only : ∀ {x'' : ThompsonState s} {q : ThompsonState (.alt r s)},
            Relation.ReflTransGen (thompsonNFA (.alt r s)).epsStep (.right x'') q →
            ∃ x''' : ThompsonState s, q = .right x''' := by
          intro x'' q hgen
          have step_inv : ∀ p' : ThompsonState (.alt r s), ∀ x''' : ThompsonState s,
              (thompsonNFA (.alt r s)).epsStep (.right x''') p' →
              ∃ x'''' : ThompsonState s, p' = .right x'''' := by
            intro p' x''' h_eps
            simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps ⊢
            obtain ⟨x, _, hx⟩ := h_eps
            exact ⟨x, hx.symm⟩
          induction hgen with
          | refl => exact ⟨x'', rfl⟩
          | tail p step ih' =>
            obtain ⟨x'', hq''⟩ := ih'
            rw [hq''] at step
            obtain ⟨x''', hq'''⟩ := step_inv _ x'' step
            exact ⟨x''', hq'''⟩

        -- Helper: epsilon steps from .right stay in .right
        have right_eps_step : ∀ {q : ThompsonState s} {p : ThompsonState (.alt r s)},
            (thompsonNFA (r.alt s)).epsStep (.right q) p → ∃ q' : ThompsonState s, p = .right q' := by
          intro q p hp
          simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at hp
          obtain ⟨p', _, hp'⟩ := hp
          exact ⟨p', hp'.symm⟩
        -- Helper: all states in reflTransGen from any .right state are .right
        have right_eps_closure : ∀ {p q : ThompsonState (.alt r s)} {x : ThompsonState s},
            p = ThompsonState.right x → Relation.ReflTransGen (thompsonNFA (r.alt s)).epsStep p q →
            ∃ y : ThompsonState s, q = ThompsonState.right y := by
          intros p q x hp hgen
          subst hp
          induction hgen with
          | refl => exact ⟨x, rfl⟩
          | tail q' step ih =>
            obtain ⟨y, hy⟩ := ih
            rw [hy] at step
            exact right_eps_step step
        -- Helper: convert epsilon paths from .right x'' to any p into paths from x'' to the corresponding state in s
        have right_eps_to_right : ∀ {x'' : ThompsonState s} {p : ThompsonState (.alt r s)},
            Relation.ReflTransGen (thompsonNFA (r.alt s)).epsStep (.right x'') p →
            ∃ q'' : ThompsonState s, p = .right q'' ∧ Relation.ReflTransGen (thompsonNFA s).epsStep x'' q'' := by
          intros x'' p hgen
          induction hgen with
          | refl => exact ⟨x'', rfl, Relation.ReflTransGen.refl⟩
          | tail q' step ih =>
            obtain ⟨y, hy, hy'⟩ := ih
            rw [hy] at step
            obtain ⟨q'', hq''⟩ := right_eps_step step
            have step_in_s : (thompsonNFA s).epsStep y q'' := by
              simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at step ⊢
              obtain ⟨x, hx, hx'⟩ := step
              have h : x = q'' := by injection hx'.trans hq''
              exact h ▸ hx
            exact ⟨q'', hq'', hy'.trans (Relation.ReflTransGen.single step_in_s)⟩
        -- Helper: convert epsilon runs from .right states
        have right_to_right : ∀ {x'' q'' : ThompsonState s} {w' : UAM_Free.FreeMonoid α},
            EpsilonRun (thompsonNFA (r.alt s)) (.right x'') w' (.right q'') →
            EpsilonRun (thompsonNFA s) x'' w' q'' := by
          intro x'' q'' w' hrun
          induction w' generalizing x'' q'' with
          | nil =>
            simp only [EpsilonRun] at hrun ⊢
            exact alt_right_eps_inv r s hrun
          | cons a' w' ih' =>
            simp only [EpsilonRun] at hrun
            obtain ⟨st, post_eps, hst_eps, hpost_eps_mem, hw''⟩ := hrun
            obtain ⟨tx', htx'⟩ := right_only hst_eps
            rw [htx'] at hpost_eps_mem
            simp [thompsonNFA, thompsonTransition] at hpost_eps_mem
            obtain ⟨tx'', htx''_mem, rfl⟩ := hpost_eps_mem
            rw [htx'] at hst_eps
            obtain ⟨q'', hq'', heps⟩ := right_eps_to_right hst_eps
            have htx'_eq : tx' = q'' := by simpa using hq''
            rw [htx'_eq] at htx''_mem
            exact ⟨q'', tx'', heps, htx''_mem, ih' hw''⟩
        -- Helper: epsStep (.right z) (.right y) in alt implies epsStep z y in s
        have right_eps_step_in_s : ∀ {z y : ThompsonState s},
            (thompsonNFA (r.alt s)).epsStep (.right z) (.right y) → (thompsonNFA s).epsStep z y := by
          intro z y step
          simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at step ⊢
          exact step
        -- Helper: if we can reach .right x from .entry via epsStep, then x is epsilon-reachable from .entry in s
        -- Helper: epsStep from .entry goes to .left .entry or .right .entry
        have entry_eps_step : ∀ {p : ThompsonState (.alt r s)},
            (thompsonNFA (r.alt s)).epsStep .entry p → p = .left .entry ∨ p = .right .entry := by
          intro p hp
          simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at hp ⊢
          exact hp
        -- Helper: any state reachable from entry is entry, left q, or right q for some q
        have entry_reachable : ∀ {q : ThompsonState (.alt r s)},
            Relation.ReflTransGen (thompsonNFA (r.alt s)).epsStep .entry q →
            q = .entry ∨ (∃ y : ThompsonState r, q = .left y) ∨ (∃ y : ThompsonState s, q = .right y) := by
          intro q hgen
          induction hgen with
          | refl => left; rfl
          | tail _ step ih =>
            rcases ih with h1 | ⟨y, hy⟩ | ⟨y, hy⟩
            · -- b✝ = entry case
              rw [h1] at step
              rcases entry_eps_step step with heq | heq
              · right; left; exact ⟨ThompsonState.entry, heq⟩
              · right; right; exact ⟨ThompsonState.entry, heq⟩
            · -- b✝ = y.left case
              -- Epsilon steps from left states stay in left
              have left_eps_step : ∀ {q : ThompsonState (.alt r s)} {z : ThompsonState r},
                  (thompsonNFA (r.alt s)).epsStep (.left z) q → ∃ z' : ThompsonState r, q = .left z' := by
                intro q z h_eps
                simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps
                obtain ⟨x, _, hx⟩ := h_eps
                exact ⟨x, hx.symm⟩
              rw [hy] at step
              obtain ⟨z, hz⟩ := left_eps_step step
              right; left; exact ⟨z, hz⟩
            · -- b✝ = y.right case
              -- Epsilon steps from right states stay in right
              have right_eps_step : ∀ {q : ThompsonState (.alt r s)} {z : ThompsonState s},
                  (thompsonNFA (r.alt s)).epsStep (.right z) q → ∃ z' : ThompsonState s, q = .right z' := by
                intro q z h_eps
                simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at h_eps
                obtain ⟨x, _, hx⟩ := h_eps
                exact ⟨x, hx.symm⟩
              rw [hy] at step
              obtain ⟨z, hz⟩ := right_eps_step step
              right; right; exact ⟨z, hz⟩
        -- Helper: from entry →* right x, we get entry.right →* right x
        have entry_to_right_entry : ∀ {p : ThompsonState (r.alt s)},
              Relation.ReflTransGen (thompsonNFA (r.alt s)).epsStep ThompsonState.entry p →
              p = ThompsonState.entry ∨
                (∃ y : ThompsonState r, p = ThompsonState.left y) ∨
                (∃ y : ThompsonState s, p = ThompsonState.right y ∧
                  Relation.ReflTransGen (thompsonNFA (r.alt s)).epsStep (ThompsonState.right ThompsonState.entry) p) := by
            intro p hgen
            induction hgen with
            | refl => left; rfl
            | tail _ step ih =>
              rcases ih with h1 | ⟨y, hy⟩ | ⟨y, hy, ih2⟩
              · rw [h1] at step
                rcases entry_eps_step step with hp | hp
                · right; left; exact ⟨ThompsonState.entry, hp⟩
                · right; right; subst hp; exact ⟨ThompsonState.entry, rfl, Relation.ReflTransGen.refl⟩
              · rw [hy] at step
                simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at step
                obtain ⟨w, _, hw⟩ := step
                right; left; exact ⟨w, hw.symm⟩
              · -- p = right y, and we have entry →* right y →* p
                -- Since step goes from right y to p, p must be right z for some z
                -- And we have right entry →* right y, so right entry →* p
                rw [hy] at step
                simp only [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at step
                obtain ⟨z, hz_mem, hz_eq⟩ := step
                have step' : (thompsonNFA (r.alt s)).epsStep (y.right) (z.right) := by
                  rw [EpsilonNFA.epsStep, thompsonNFA]
                  exact Set.mem_image_of_mem _ hz_mem
                rw [hy] at ih2
                rw [hz_eq.symm] at ⊢
                right; right; exact ⟨z, rfl, ih2.trans (Relation.ReflTransGen.single step')⟩
        have right_eps_to_s : ∀ (x : ThompsonState s),
            Relation.ReflTransGen (thompsonNFA (r.alt s)).epsStep .entry (ThompsonState.right x) →
            Relation.ReflTransGen (thompsonNFA s).epsStep .entry x := by
          intro x hgen
          have h' := entry_to_right_entry hgen
          -- entry →* x.right, so entry_to_right_entry gives us x.right = entry ∨ x.right = left y ∨ (x.right = right y ∧ right.entry →* x.right)
          -- Only the third case is possible
          rcases h' with heq | ⟨y, hy⟩ | ⟨y, hy, hy2⟩
          · -- x.right = entry is impossible
            cases heq
          · -- x.right = left y is impossible
            injection hy
          · -- x.right = right y means x = y
            have hxy : x = y := by injection hy
            subst hxy
            -- hy2 : right.entry →* x.right
            obtain ⟨q'', hq'', heps⟩ := right_eps_to_right hy2
            have : x = q'' := by injection hq''
            exact this ▸ heps
        -- Now we can finish: hp takes .entry to .right p', so p' is epsilon-reachable from .entry in s
        have hp'_eps : Relation.ReflTransGen (thompsonNFA s).epsStep .entry p' := right_eps_to_s p' hp
        -- Construct the full run in s: .entry →ε→ p' →a→ y →w→ q'
        exact ⟨p', hp'_eps, y, hy, right_to_right hw⟩

private theorem thompson_alt_language {α : Type u} (r s : RegExp α) :
    epsilonLanguage (thompsonNFA (.alt r s)) =
      epsilonLanguage (thompsonNFA r) ∪ epsilonLanguage (thompsonNFA s) := by
  ext w
  constructor
  · intro hw
    obtain ⟨f, hf, hrun⟩ :=
      (mem_epsilonLanguage_iff_run (thompsonNFA (.alt r s)) w).mp hw
    simp only [thompsonNFA, thompsonAccepting, Set.mem_union,
      Set.mem_image] at hf
    rcases hf with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl ((mem_epsilonLanguage_iff_run (thompsonNFA r) w).mpr
        ⟨q, hq, alt_entry_left_run_inv r s hrun⟩)
    · exact Or.inr ((mem_epsilonLanguage_iff_run (thompsonNFA s) w).mpr
        ⟨q, hq, alt_entry_right_run_inv r s hrun⟩)
  · rintro (hw | hw)
    · obtain ⟨f, hf, hrun⟩ :=
        (mem_epsilonLanguage_iff_run (thompsonNFA r) w).mp hw
      have hpre : EpsilonRun (thompsonNFA (.alt r s)) .entry [] (.left .entry) :=
        Relation.ReflTransGen.single (Set.mem_union_left _ (Set.mem_singleton _))
      exact (mem_epsilonLanguage_iff_run (thompsonNFA (.alt r s)) w).mpr
        ⟨.left f, by exact Set.mem_union_left _ (Set.mem_image_of_mem _ hf), by
          simpa using epsilonRun_append _ hpre (alt_left_run r s hrun)⟩
    · obtain ⟨f, hf, hrun⟩ :=
        (mem_epsilonLanguage_iff_run (thompsonNFA s) w).mp hw
      have hpre : EpsilonRun (thompsonNFA (.alt r s)) .entry [] (.right .entry) :=
        Relation.ReflTransGen.single (Set.mem_union_right _ (Set.mem_singleton _))
      exact (mem_epsilonLanguage_iff_run (thompsonNFA (.alt r s)) w).mpr
        ⟨.right f, by exact Set.mem_union_right _ (Set.mem_image_of_mem _ hf), by
          simpa using epsilonRun_append _ hpre (alt_right_run r s hrun)⟩

private theorem thompson_alt_correct {α : Type u} (r s : RegExp α)
    (hr : epsilonLanguage (thompsonNFA r) = languageOf r)
    (hs : epsilonLanguage (thompsonNFA s) = languageOf s) :
    epsilonLanguage (thompsonNFA (.alt r s)) = languageOf (.alt r s) := by
  rw [thompson_alt_language, hr, hs]
  rfl

private theorem concat_first_run {α : Type u} (r s : RegExp α)
    {q q' : ThompsonState r} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA r) q w q') :
    EpsilonRun (thompsonNFA (.concat r s)) (.first q) w (.first q') := by
  induction' w with a w ih generalizing q q' <;> simp_all +decide [EpsilonRun]
  · induction h
    · rfl
    · rename_i h₁ h₂ h₃
      exact h₃.tail (by
        exact Set.mem_union_left _ (Set.mem_image_of_mem _ h₂) |> fun h => by tauto)
  · obtain ⟨p, hp, x, hx, hx'⟩ := h
    refine ⟨p.first, ?_, x.first, ?_, ih hx'⟩
    · convert hp.lift _ _ using 1
      intro a b hab
      convert Set.mem_union_left _ (Set.mem_image_of_mem _ hab) using 1
    · exact Set.mem_union_left _ (Set.mem_image_of_mem _ hx)

private theorem concat_second_run {α : Type u} (r s : RegExp α)
    {q q' : ThompsonState s} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA s) q w q') :
    EpsilonRun (thompsonNFA (.concat r s)) (.second q) w (.second q') := by
  induction' w with a w ih generalizing q q' <;> simp_all +decide [ EpsilonRun ];
  · induction h;
    · rfl;
    · rename_i h₁ h₂ h₃;
      exact h₃.tail ( by
        exact Set.mem_union_left _ ( Set.mem_image_of_mem _ h₂ ) |> fun h => by tauto; );
  · obtain ⟨ p, hp, x, hx, hx' ⟩ := h;
    refine' ⟨ p.second, _, x.second, _, ih hx' ⟩;
    · convert hp.lift _ _ using 1;
      intro a b hab; exact (by
      convert Set.mem_union_left _ ( Set.mem_image_of_mem _ hab ) using 1);
    · exact Set.mem_union_left _ ( Set.mem_image_of_mem _ hx )

private theorem concat_second_to_exit_inv {α : Type u} (r s : RegExp α)
    {q : ThompsonState s} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA (.concat r s)) (.second q) w .exit) :
    ∃ f ∈ thompsonAccepting s, EpsilonRun (thompsonNFA s) q w f := by
  -- Helper: from any .second q', eps transitions only go to .second q'' or .exit (if q' is accepting)
  have second_eps_closed : ∀ (q' : ThompsonState s) {q'' : ThompsonState (r.concat s)},
      (thompsonNFA (.concat r s)).epsStep (.second q') q'' →
      (q'' = .exit ∧ q' ∈ thompsonAccepting s) ∨
      ∃ q''' : ThompsonState s, q'' = .second q''' ∧ (thompsonNFA s).epsStep q' q''' := by
    intro q' q'' hq''
    simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at hq''
    tauto
  -- Helper: transition from .second q' on some a goes to .second of transition in s
  have second_trans_closed : ∀ (q' : ThompsonState s) (a : α) {t : ThompsonState (r.concat s)},
      t ∈ (thompsonNFA (.concat r s)).δ (.second q') (some a) →
      ∃ t' : ThompsonState s, t = .second t' ∧ t' ∈ (thompsonNFA s).δ q' (some a) := by
    intro q' a t ht
    simp [thompsonNFA, thompsonTransition] at ht
    tauto
  -- Generalized helper for ReflTransGen
  have second_reflexive_closed : ∀ (q' : ThompsonState s) {q'' : ThompsonState (r.concat s)},
      Relation.ReflTransGen (thompsonNFA (.concat r s)).epsStep (.second q') q'' →
      (q'' = .exit ∧ ∃ q'''' : ThompsonState s, Relation.ReflTransGen (thompsonNFA s).epsStep q' q'''' ∧ q'''' ∈ thompsonAccepting s) ∨
      ∃ q'''' : ThompsonState s, q'' = .second q'''' ∧ Relation.ReflTransGen (thompsonNFA s).epsStep q' q'''' := by
    intro q' q'' h
    induction h with
    | refl => right; exact ⟨q', rfl, Relation.ReflTransGen.refl⟩
    | tail _ hstep a_ih =>
      rcases a_ih with ⟨rfl, q1, hq'refl, hq'acc⟩ | ⟨q1, rfl, hq'refl⟩
      · simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at hstep
      · cases hbc : second_eps_closed q1 hstep with
        | inl h' => left; exact ⟨h'.1, q1, hq'refl, h'.2⟩
        | inr h' =>
          obtain ⟨q2, rfl, hstep2⟩ := h'
          right; exact ⟨q2, rfl, hq'refl.trans (Relation.ReflTransGen.single hstep2)⟩
  -- Generalized statement for induction
  have key : ∀ (w : UAM_Free.FreeMonoid α) (q' : ThompsonState s),
      EpsilonRun (thompsonNFA (.concat r s)) (.second q') w .exit →
      ∃ f ∈ thompsonAccepting s, EpsilonRun (thompsonNFA s) q' w f := by
    intro w q'
    induction w generalizing q' with
    | nil =>
      intro h
      rcases second_reflexive_closed q' h with ⟨_, q'', hq''refl, hq''acc⟩ | ⟨q'', heq, _⟩
      · exact ⟨q'', hq''acc, hq''refl⟩
      · contradiction
    | cons a w' ih =>
      intro h
      -- Unfold EpsilonRun to get intermediate states
      rw [EpsilonRun.eq_def] at h
      obtain ⟨p, t, hprefl, htmemb, htail⟩ := h
      -- Use second_reflexive_closed to analyze hprefl
      rcases second_reflexive_closed q' hprefl with ⟨_, q'', hq''refl, hq''acc⟩ | ⟨q'', rfl, hq''refl⟩
      · -- p = .exit, but then transition from .exit is empty, contradiction
        subst p
        simp [thompsonNFA, thompsonTransition] at htmemb
      · -- p = .second q'', so we can apply second_trans_closed
        obtain ⟨t', ht_eq, ht_mem⟩ := second_trans_closed q'' a htmemb
        -- Now t = .second t', and t' ∈ δ s q'' (some a)
        rw [ht_eq] at htail
        -- Apply IH to get result for t'
        obtain ⟨f, hf_acc, ht'_run⟩ := ih t' htail
        -- Now we need to construct EpsilonRun from q' to f
        refine ⟨f, hf_acc, q'', t', hq''refl, ht_mem, ht'_run⟩
  exact key w q h

private theorem concat_first_to_exit_inv {α : Type u} (r s : RegExp α)
    {q : ThompsonState r} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA (.concat r s)) (.first q) w .exit) :
    ∃ u v, w = u ++ v ∧
      (∃ f ∈ thompsonAccepting r, EpsilonRun (thompsonNFA r) q u f) ∧
      (∃ g ∈ thompsonAccepting s, EpsilonRun (thompsonNFA s) .entry v g) := by
  -- Generalized helper for ReflTransGen from .first q'
  -- Returns: either we're at .first q''' with refl_trans q q''', or we're at .second .entry
  --   and the ORIGINAL q' is accepting in r
  have first_reflexive_closed : ∀ (q' : ThompsonState r) {q'' : ThompsonState (r.concat s)},
      Relation.ReflTransGen (thompsonNFA (.concat r s)).epsStep (.first q') q'' →
      (∃ q''' : ThompsonState r, q'' = .first q''' ∧
        Relation.ReflTransGen (thompsonNFA r).epsStep q' q''') ∨
      (∃ q_acc : ThompsonState r, q_acc ∈ thompsonAccepting r ∧
        Relation.ReflTransGen (thompsonNFA r).epsStep q' q_acc ∧ ∃ q_s : ThompsonState s,
        q'' = .second q_s ∧ Relation.ReflTransGen (thompsonNFA s).epsStep .entry q_s) ∨
      (∃ q_acc : ThompsonState r, q_acc ∈ thompsonAccepting r ∧
        Relation.ReflTransGen (thompsonNFA r).epsStep q' q_acc ∧ ∃ q_s : ThompsonState s,
        q_s ∈ thompsonAccepting s ∧ Relation.ReflTransGen (thompsonNFA s).epsStep .entry q_s ∧ q'' = .exit) := by
    intro q' q'' h
    -- Helper for epsStep from .second states
    have second_eps_closed : ∀ (q' : ThompsonState s) {q'' : ThompsonState (r.concat s)},
        (thompsonNFA (.concat r s)).epsStep (.second q') q'' →
        (q'' = .exit ∧ q' ∈ thompsonAccepting s) ∨
        ∃ q''' : ThompsonState s, q'' = .second q''' ∧ (thompsonNFA s).epsStep q' q''' := by
      intro q' q'' hq''
      simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition] at hq''
      tauto
    induction h with
    | refl => exact Or.inl ⟨q', rfl, Relation.ReflTransGen.refl⟩
    | @tail _ _ _ ih₁ ih₂ =>
      obtain ⟨q''', hqeq, hqrefl⟩ | ⟨q_acc, hq_acc, hqrefl, q_s, hqsec, hentry⟩ |
          ⟨q_acc, hq_acc, hqrefl, q_s, hq_acc_s, hentry, hq''⟩ := ih₂
      · -- b = .first q''', epsStep (.first q''') c
        -- From .first q''', epsilon goes to .first q'''' or .second .entry (if q''' accepting)
        rw [hqeq] at ih₁
        simp [thompsonNFA, epsStep, thompsonTransition] at ih₁
        rcases ih₁ with ih₁ | ⟨_, rfl⟩
        · -- c ∈ ThompsonState.first '' thompsonTransition r q''' none
          left
          obtain ⟨q'''', hq_in_trans, rfl⟩ := ih₁
          exact ⟨q'''', rfl, hqrefl.trans (Relation.ReflTransGen.single hq_in_trans)⟩
        · -- q''' is accepting, c = .second .entry
          right; left
          use q''', ‹q''' ∈ thompsonAccepting r›, hqrefl, .entry, rfl, Relation.ReflTransGen.refl
      · -- b = .second q_s, we have second disjunct
        -- ih₁ : epsStep (.second q_s) c
        rw [hqsec] at ih₁
        rcases second_eps_closed q_s ih₁ with ⟨hc_eq, h_acc⟩ | ⟨q', rfl, hstep⟩
        · -- c = .exit ∧ q_s ∈ thompsonAccepting s
          right; right
          exact ⟨q_acc, hq_acc, hqrefl, q_s, h_acc, hentry, hc_eq⟩
        · -- c = .second q' ∧ epsStep q_s q'
          right; left
          use q_acc, hq_acc, hqrefl
          exact ⟨q', rfl, hentry.trans (Relation.ReflTransGen.single hstep)⟩
      · -- b = .exit, but epsStep .exit is impossible
        subst hq''
        simp [thompsonNFA, epsStep, thompsonTransition] at ih₁
  -- Helper: transition from .first q' on some a goes to .first of transition in r
  have first_trans_closed : ∀ (q' : ThompsonState r) (a : α) {t : ThompsonState (r.concat s)},
      t ∈ (thompsonNFA (.concat r s)).δ (.first q') (some a) →
      ∃ t' : ThompsonState r, t = .first t' ∧ t' ∈ (thompsonNFA r).δ q' (some a) := by
    intro q' a t ht
    simp [thompsonNFA, thompsonTransition] at ht
    tauto
  -- Helper: transition from .second q goes to .second of transition in s
  have second_trans_closed_helper : ∀ (q : ThompsonState s) (a : α) {t : ThompsonState (r.concat s)},
      t ∈ (thompsonNFA (.concat r s)).δ (.second q) (some a) →
      ∃ t' : ThompsonState s, t = .second t' ∧ t' ∈ (thompsonNFA s).δ q (some a) := by
    intro q a t ht
    simp [thompsonNFA, thompsonTransition] at ht
    tauto
  -- Helper: from .second t', EpsilonRun to .exit gives accepting path in s
  have second_trans_closed : ∀ (q_s : ThompsonState s) (w' : UAM_Free.FreeMonoid α),
      EpsilonRun (thompsonNFA (.concat r s)) (.second q_s) w' .exit →
      ∃ g ∈ thompsonAccepting s, EpsilonRun (thompsonNFA s) q_s w' g := by
    intro q_s w' hw'
    obtain ⟨g, hg_acc, hg_run⟩ := concat_second_to_exit_inv r s hw'
    exact ⟨g, hg_acc, hg_run⟩
  -- Generalized statement for induction
  have key : ∀ (w : UAM_Free.FreeMonoid α) (q' : ThompsonState r),
      EpsilonRun (thompsonNFA (.concat r s)) (.first q') w .exit →
      ∃ u v, w = u ++ v ∧
        (∃ f ∈ thompsonAccepting r, EpsilonRun (thompsonNFA r) q' u f) ∧
        (∃ g ∈ thompsonAccepting s, EpsilonRun (thompsonNFA s) .entry v g) := by
    intro w q'
    induction w generalizing q' with
    | nil =>
      intro h
      -- h : EpsilonRun ... (.first q') [] .exit = ReflTransGen ... epsStep (.first q') .exit
      rcases first_reflexive_closed q' h with ⟨q'', hqeq, hqrefl⟩ | ⟨q_acc, hq_acc, hqrefl, q_s, hp_eq, hentry⟩ | hqexit
      · -- h = .first q'', but we need to reach .exit, impossible
        injection hqeq
      · -- p = .second q_s, but the target is .exit, contradiction
        injection hp_eq
      · -- p = .exit
        obtain ⟨q_acc, hq_acc, hqrefl, q_s, hq_acc_s, hentry, hp_eq⟩ := hqexit
        exact ⟨[], [], rfl, ⟨q_acc, hq_acc, hqrefl⟩, ⟨q_s, hq_acc_s, hentry⟩⟩
    | cons a w' ih =>
      intro h
      rw [EpsilonRun.eq_def] at h
      obtain ⟨p, t, hprefl, htmemb, htail⟩ := h
      rcases first_reflexive_closed q' hprefl with ⟨q'', hqeq, hqrefl⟩ | ⟨q_acc, hq_acc, hqrefl, q_s, hqsec⟩ | hqexit
      · -- p = .first q'', so we can apply first_trans_closed
        rw [hqeq] at htmemb
        obtain ⟨t', ht_eq, ht_mem⟩ := first_trans_closed q'' a htmemb
        rw [ht_eq] at htail
        -- Get result for t' on w'
        obtain ⟨u, v, hw_eq, hu, hv⟩ := ih t' htail
        refine ⟨[a] ++ u, v, by simp [hw_eq], ?_, hv⟩
        -- Need to construct run from q' on [a] ++ u
        obtain ⟨f, hf_acc, hf_run⟩ := hu
        refine ⟨f, hf_acc, ?_⟩
        -- hqrefl : q' =>* q'' in r, and hf_run : t' =>* f in r, with t' ∈ δ r q'' a
        rw [EpsilonRun.eq_def]
        exact ⟨q'', t', hqrefl, ht_mem, hf_run⟩
      · -- p = .second q_s, analyze transition on a
        -- Note: We can only reach .second .entry from .first via epsilon
        obtain ⟨hp_eq, hentry_q_s⟩ := hqsec
        -- q_s must be .entry since that's the only .second state reachable from .first
        rw [hp_eq] at htmemb
        obtain ⟨t', ht_eq, ht_mem⟩ := second_trans_closed_helper q_s a htmemb
        rw [ht_eq] at htail
        obtain ⟨g, hg_acc, hg_run⟩ := second_trans_closed t' w' htail
        refine ⟨[], a :: w', rfl, ⟨q_acc, hq_acc, hqrefl⟩, ⟨g, hg_acc, ?_⟩⟩
        rw [EpsilonRun.eq_def]
        exact ⟨q_s, t', hentry_q_s, ht_mem, hg_run⟩
      · -- p = .exit, but we have a transition on 'a', impossible
        obtain ⟨_, _, _, _, _, ⟨_, hp_eq⟩⟩ := hqexit
        subst hp_eq
        simp [thompsonNFA, thompsonTransition] at htmemb
  exact key w q h

private theorem concat_entry_to_exit_inv {α : Type u} (r s : RegExp α)
    {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA (.concat r s)) .entry w .exit) :
    ∃ u v, w = u ++ v ∧
      (∃ f ∈ thompsonAccepting r, EpsilonRun (thompsonNFA r) .entry u f) ∧
      (∃ g ∈ thompsonAccepting s, EpsilonRun (thompsonNFA s) .entry v g) := by
  -- There's an ε-transition from .entry to .first .entry
  have entry_to_first : (thompsonNFA (.concat r s)).epsStep .entry (.first .entry) := by
    show (.first .entry) ∈ ((thompsonNFA (.concat r s)).δ .entry none)
    simp [thompsonNFA, thompsonTransition]
  -- Key observation: from .entry, the only reachable state via ε is .first .entry
  -- And from .first .entry, we can reach any state reachable from .entry
  -- Helper: entry has no symbol transitions, so any state p before reading must be .first .entry
  have entry_no_symbol : ∀ a : α, ∀ t, t ∈ (thompsonNFA (.concat r s)).δ .entry (some a) → False := by
    intro a t ht
    simp [thompsonNFA, thompsonTransition] at ht
  -- Helper: any state ε-reachable from .entry (other than .entry itself) is ε-reachable from .first .entry
  let first_entry : ThompsonState (r.concat s) := ThompsonState.first (.entry : ThompsonState r)
  have reachability : ∀ q' : ThompsonState (r.concat s),
      Relation.ReflTransGen (thompsonNFA (.concat r s)).epsStep .entry q' →
      (q' = .entry ∨ Relation.ReflTransGen (thompsonNFA (.concat r s)).epsStep first_entry q') := by
    intro q' hp
    induction hp with
    | refl => left; rfl
    | @tail _ a b ih hstep =>
      -- ih : epsStep b a
      -- hstep : b = .entry ∨ ReflTransGen first_entry b
      rcases hstep with hb | hb
      · -- b = .entry
        -- ih : epsStep .entry a, so a = first_entry
        have ha : a = first_entry := by
          subst hb
          simp [epsStep, thompsonNFA, thompsonTransition] at ih
          exact ih
        rw [ha]; right; exact Relation.ReflTransGen.refl
      · -- ReflTransGen first_entry b
        right; exact hb.trans (Relation.ReflTransGen.single ih)
  have entry_to_first_run : EpsilonRun (thompsonNFA (.concat r s)) first_entry w .exit := by
    -- Case split on w
    cases w with
    | nil =>
      -- EpsilonRun from .entry to .exit on empty word is just ReflTransGen
      have hrun := h
      simp only [EpsilonRun] at hrun
      -- If .exit is reachable from .entry via ε, it's also reachable from .first .entry
      rcases reachability .exit hrun with h | h
      · -- .exit = .entry, contradiction
        contradiction
      · exact h
    | cons a w' =>
      -- EpsilonRun on a :: w' means there's an intermediate state p reachable via ε from .entry
      have h_def : ∃ p t, Relation.ReflTransGen (thompsonNFA (.concat r s)).epsStep .entry p ∧
          t ∈ (thompsonNFA (.concat r s)).δ p (some a) ∧
          EpsilonRun (thompsonNFA (.concat r s)) t w' .exit := by
        exact h
      obtain ⟨p, t, hp, htmemb, htail⟩ := h_def
      -- p ≠ .entry since .entry has no symbol transitions
      have hp_ne : p ≠ .entry := by
        rintro rfl
        exact entry_no_symbol a t htmemb
      rcases reachability p hp with hp' | hp'
      · contradiction
      · exact ⟨p, t, hp', htmemb, htail⟩
  -- Now use concat_first_to_exit_inv to get the witness split
  exact concat_first_to_exit_inv r s entry_to_first_run

private theorem thompson_concat_correct {α : Type u} (r s : RegExp α)
    (hr : epsilonLanguage (thompsonNFA r) = languageOf r)
    (hs : epsilonLanguage (thompsonNFA s) = languageOf s) :
    epsilonLanguage (thompsonNFA (.concat r s)) = languageOf (.concat r s) := by
  ext w
  constructor
  · intro hw
    obtain ⟨f, hf, hrun⟩ := (mem_epsilonLanguage_iff_run _ _).1 hw
    have hfeq : f = ThompsonState.exit := by simpa [thompsonNFA] using hf
    subst f
    obtain ⟨u, v, rfl, ⟨f, hf, hfrun⟩, ⟨g, hg, hgrun⟩⟩ :=
      concat_entry_to_exit_inv r s hrun
    refine ⟨u, v, rfl, ?_, ?_⟩
    · rw [← hr]
      exact (mem_epsilonLanguage_iff_run _ _).2 ⟨f, by simpa [thompsonNFA] using hf, hfrun⟩
    · rw [← hs]
      exact (mem_epsilonLanguage_iff_run _ _).2 ⟨g, by simpa [thompsonNFA] using hg, hgrun⟩
  · rintro ⟨u, v, rfl, hu, hv⟩
    rw [← hr] at hu
    rw [← hs] at hv
    obtain ⟨f, hf, hfrun⟩ := (mem_epsilonLanguage_iff_run _ _).1 hu
    obtain ⟨g, hg, hgrun⟩ := (mem_epsilonLanguage_iff_run _ _).1 hv
    have hfacc : f ∈ thompsonAccepting r := by simpa [thompsonNFA] using hf
    have hgacc : g ∈ thompsonAccepting s := by simpa [thompsonNFA] using hg
    have h1 : EpsilonRun (thompsonNFA (.concat r s)) .entry [] (.first .entry) := by
      apply Relation.ReflTransGen.single
      simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition]
    have h2 := concat_first_run r s hfrun
    have h3 : EpsilonRun (thompsonNFA (.concat r s)) (.first f) [] (.second .entry) := by
      apply Relation.ReflTransGen.single
      simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition, hfacc]
    have h4 := concat_second_run r s hgrun
    have h5 : EpsilonRun (thompsonNFA (.concat r s)) (.second g) [] .exit := by
      apply Relation.ReflTransGen.single
      simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition, hgacc]
    apply (mem_epsilonLanguage_iff_run _ _).2
    refine ⟨.exit, by simp [thompsonNFA], ?_⟩
    simpa using epsilonRun_append _ (epsilonRun_append _
      (epsilonRun_append _ (epsilonRun_append _ h1 h2) h3) h4) h5

private theorem star_body_run {α : Type u} (r : RegExp α)
    {q q' : ThompsonState r} {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA r) q w q') :
    EpsilonRun (thompsonNFA (.star r)) (.body q) w (.body q') := by
  induction' w with a w ih generalizing q q' <;> simp_all +decide [ EpsilonRun ];
  · induction h;
    · rfl;
    · rename_i h₁ h₂ h₃;
      exact h₃.tail ( by
        convert Set.mem_union_left _ ( Set.mem_image_of_mem _ h₂ ) using 1 );
  · obtain ⟨ p, hp₁, x, hx₁, hx₂ ⟩ := h;
    refine' ⟨ p.body, _, x.body, _, _ ⟩;
    · convert hp₁.lift _ _ using 1
      intro a b hab
      convert Set.mem_union_left _ (Set.mem_image_of_mem _ hab) using 1
    · exact Set.mem_union_left _ ( Set.mem_image_of_mem _ hx₁ );
    · exact ih hx₂

private theorem kleeneStar_decompose {α : Type u} {L : Set (UAM_Free.FreeMonoid α)}
    {w : UAM_Free.FreeMonoid α} (h : UAM_RegularLanguages.KleeneStar L w) :
    ∃ ws : List (UAM_Free.FreeMonoid α), (∀ x ∈ ws, x ∈ L) ∧ w = ws.flatten := by
  induction h with
  | empty => exact ⟨[], by simp⟩
  | word w hw => exact ⟨[w], by simpa⟩
  | concat w₁ w₂ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨ws₁, hws₁, rfl⟩ := ih₁
      obtain ⟨ws₂, hws₂, rfl⟩ := ih₂
      refine ⟨ws₁ ++ ws₂, ?_, by simp⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hws₁ x hx
      · exact hws₂ x hx

private theorem star_body_word_loop {α : Type u} (r : RegExp α)
    {w : UAM_Free.FreeMonoid α} (hw : w ∈ epsilonLanguage (thompsonNFA r)) :
    EpsilonRun (thompsonNFA (.star r)) (.body .entry) w (.body .entry) := by
  -- By definition of `epsilonLanguage`, there exists an accepting run from the entry state to some exit state.
  obtain ⟨f, hf⟩ := mem_epsilonLanguage_iff_run (thompsonNFA r) w |>.1 hw;
  have h_run : EpsilonRun (thompsonNFA (.star r)) (.body (thompsonNFA r).q₀) w (.body f) := by
    exact star_body_run r hf.2;
  have hfacc : f ∈ thompsonAccepting r := by simpa [thompsonNFA] using hf.1
  have h_run : EpsilonRun (thompsonNFA (.star r)) (.body f) [] (.body (thompsonNFA r).q₀) := by
    apply Relation.ReflTransGen.single
    simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition, hfacc]
  convert epsilonRun_append _ ‹_› h_run using 1;
  simp +decide [ List.append_nil ]

private theorem star_body_words_finish {α : Type u} (r : RegExp α)
    {x : UAM_Free.FreeMonoid α} {xs : List (UAM_Free.FreeMonoid α)}
    (hx : x ∈ epsilonLanguage (thompsonNFA r))
    (hxs : ∀ y ∈ xs, y ∈ epsilonLanguage (thompsonNFA r)) :
    EpsilonRun (thompsonNFA (.star r)) (.body .entry) (x ++ xs.flatten) .exit := by
  induction' xs with y ys ih generalizing x;
  · obtain ⟨ f, hf, h ⟩ := mem_epsilonLanguage_iff_run _ _ |>.1 hx;
    have := star_body_run r h;
    have hfacc : f ∈ thompsonAccepting r := by simpa [thompsonNFA] using hf
    have h_eps : Relation.ReflTransGen (thompsonNFA (.star r)).epsStep (.body f) .exit := by
      apply Relation.ReflTransGen.single
      simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition, hfacc]
    convert epsilonRun_append _ this _;
    exact h_eps;
  · convert epsilonRun_append _ _ _ using 1;
    exact ThompsonState.body ThompsonState.entry;
    · exact star_body_word_loop r hx;
    · convert ih ( hxs y ( by simp +decide ) ) ( fun z hz => hxs z ( by simp +decide [ hz ] ) ) using 1

private theorem star_language_backward {α : Type u} (r : RegExp α)
    (hr : epsilonLanguage (thompsonNFA r) = languageOf r) :
    ∀ {w}, UAM_RegularLanguages.KleeneStar (languageOf r) w →
      w ∈ epsilonLanguage (thompsonNFA (.star r)) := by
  intro w hw
  obtain ⟨ws, hws, rfl⟩ := kleeneStar_decompose hw
  cases ws with
  | nil =>
      apply (mem_epsilonLanguage_iff_run _ _).2
      refine ⟨.exit, by simp [thompsonNFA], ?_⟩
      apply Relation.ReflTransGen.single
      simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition]
  | cons x xs =>
      have hx : x ∈ epsilonLanguage (thompsonNFA r) := by
        rw [hr]
        exact hws x (by simp)
      have hxs : ∀ y ∈ xs, y ∈ epsilonLanguage (thompsonNFA r) := by
        intro y hy
        rw [hr]
        exact hws y (by simp [hy])
      have hrun := star_body_words_finish r hx hxs
      have hentry : EpsilonRun (thompsonNFA (.star r)) .entry [] (.body .entry) := by
        apply Relation.ReflTransGen.single
        simp [EpsilonNFA.epsStep, thompsonNFA, thompsonTransition]
      apply (mem_epsilonLanguage_iff_run _ _).2
      refine ⟨.exit, by simp [thompsonNFA], ?_⟩
      simpa using epsilonRun_append _ hentry hrun

private theorem star_epsilon_phase {α : Type u} (r : RegExp α)
    {u : UAM_Free.FreeMonoid α} {q : ThompsonState r}
    {p : ThompsonState (.star r)}
    (hu : EpsilonRun (thompsonNFA r) .entry u q)
    (hp : Relation.ReflTransGen (thompsonNFA (.star r)).epsStep (.body q) p) :
    (∃ ws : List (UAM_Free.FreeMonoid α),
      (∀ x ∈ ws, x ∈ epsilonLanguage (thompsonNFA r)) ∧
      u = ws.flatten ∧ p = .exit) ∨
    (∃ ws : List (UAM_Free.FreeMonoid α), ∃ v : UAM_Free.FreeMonoid α,
      ∃ q' : ThompsonState r,
      (∀ x ∈ ws, x ∈ epsilonLanguage (thompsonNFA r)) ∧
      u = ws.flatten ++ v ∧ p = .body q' ∧
      EpsilonRun (thompsonNFA r) .entry v q') := by
  induction' hp with q' q'' hq' hq'' ih;
  · exact Or.inr ⟨ [ ], u, q, by simp +decide, by simp +decide, rfl, hu ⟩;
  · rcases ih with ( ⟨ ws, hws, rfl, rfl ⟩ | ⟨ ws, v, q', hws, rfl, rfl, hv ⟩ );
    · cases hq'';
    · rcases q'' with ( _ | _ | _ | _ | _ );
      · cases hq'' <;> simp_all
      · refine' Or.inl ⟨ ws ++ [ v ], _, _, rfl ⟩;
        · simp_all +decide [ mem_epsilonLanguage_iff_run ];
          rintro x ( hx | rfl );
          · exact hws x hx;
          · cases hq'';
            · simp_all
            · refine ⟨q', ?_, hv⟩
              simp_all [thompsonNFA]
        · simp +decide [ List.flatten ];
      · unfold thompsonNFA at hq''; simp_all +decide [ EpsilonNFA.epsStep ] ;
        unfold thompsonTransition at hq''; simp_all +decide ;
        rcases hq'' with ( hq'' | ⟨ hq'', rfl ⟩ );
        · exact ⟨ ws, hws, v, rfl, hv |> fun h => by
            convert epsilonRun_append _ _ _ using 1;
            rotate_left;
            exact q';
            exact v;
            exact [ ];
            · assumption;
            · exact Relation.ReflTransGen.single hq'';
            · simp +decide [ List.append_nil ] ⟩;
        · use ws ++ [v];
          simp_all +decide [ List.flatten ];
          exact ⟨ fun x hx => hx.elim ( fun hx => hws x hx ) fun hx => hx.symm ▸ ( mem_epsilonLanguage_iff_run _ _ ).2 ⟨ q', hq'', hv ⟩, by exact Relation.ReflTransGen.refl ⟩

private theorem star_body_to_exit_decompose {α : Type u} (r : RegExp α)
    {u w : UAM_Free.FreeMonoid α} {q : ThompsonState r}
    (hu : EpsilonRun (thompsonNFA r) .entry u q)
    (h : EpsilonRun (thompsonNFA (.star r)) (.body q) w .exit) :
    ∃ ws : List (UAM_Free.FreeMonoid α),
      (∀ x ∈ ws, x ∈ epsilonLanguage (thompsonNFA r)) ∧
      u ++ w = ws.flatten := by
  induction' w with a w ih generalizing u q;
  · rcases star_epsilon_phase r hu h with hdone | hbody
    · obtain ⟨ws, hws, huw, _⟩ := hdone
      exact ⟨ws, hws, by simpa using huw⟩
    · obtain ⟨ws, v, q', hws, huv, hp, hv⟩ := hbody
      cases hp
  · obtain ⟨ p, t, hp, ht, h' ⟩ := h;
    obtain ⟨ ws, hws₁, hws₂ ⟩ := star_epsilon_phase r hu hp;
    · cases hws₂.2 ▸ ht;
    · rcases ‹_› with ⟨ ws, v, q', hws₁, rfl, rfl, hv ⟩;
      rcases ht with ⟨ ⟩;
      · obtain ⟨ x, hx, rfl ⟩ := ‹t ∈ ThompsonState.body '' thompsonTransition r q' ( some a ) ›;
        obtain ⟨ ws', hws'₁, hws'₂ ⟩ := ih ( show EpsilonRun ( thompsonNFA r ) ThompsonState.entry ( v ++ [ a ] ) x from by
                                              exact epsilonRun_append _ hv ( by exact ⟨ q', x, by tauto ⟩ ) ) h';
        refine ⟨ws ++ ws', ?_, ?_⟩
        · intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hws₁ z hz
          · exact hws'₁ z hz
        · rw [List.flatten_append]
          rw [← hws'₂]
          simp [List.append_assoc]
      · simp_all

private theorem star_run_decompose {α : Type u} (r : RegExp α)
    {w : UAM_Free.FreeMonoid α}
    (h : EpsilonRun (thompsonNFA (.star r)) .entry w .exit) :
    ∃ ws : List (UAM_Free.FreeMonoid α),
      (∀ x ∈ ws, x ∈ epsilonLanguage (thompsonNFA r)) ∧ w = ws.flatten := by
  rcases w with ( _ | ⟨ a, w ⟩ );
  · exact ⟨ [ ], by simp +decide ⟩;
  · obtain ⟨ q, hq ⟩ := h;
    rcases q with ( _ | _ | q ) <;> simp_all +decide [ thompsonNFA ];
    · cases hq.2 ; simp_all +decide [ thompsonTransition ];
    · cases hq.2 ; simp_all +decide [ thompsonTransition ];
    · obtain ⟨ q, hq ⟩ := hq.2;
      rcases q with ( _ | _ | q ) <;> simp_all +decide [ thompsonTransition ];
      have := star_body_to_exit_decompose r ( show EpsilonRun ( thompsonNFA r ) ThompsonState.entry [ a ] _ from by
                                                exact ⟨ _, _, by
                                                  rename_i h₁ h₂;
                                                  have := h₂.1; simp_all +decide [ thompsonNFA ] ;
                                                  have := this.cases_head; simp_all +decide [ EpsilonNFA.epsStep ] ;
                                                  rcases this with ⟨ c, hc₁, hc₂ ⟩ ; rcases c with ( _ | _ | c ) <;> simp_all +decide [ thompsonTransition ] ;
                                                  · have := hc₂.cases_head; simp_all +decide [ EpsilonNFA.epsStep ] ;
                                                    rcases this with ⟨ c, hc₁, hc₂ ⟩ ; rcases c with ( _ | _ | c ) <;> simp_all +decide [ thompsonTransition ] ;
                                                  · have := star_epsilon_phase r ( show EpsilonRun ( thompsonNFA r ) ThompsonState.entry [] _ from by
                                                                                    exact Relation.ReflTransGen.refl ) hc₂; simp_all +decide ;
                                                    obtain ⟨ ws, hws₁, hws₂, hws₃ ⟩ := this; exact hws₃;, hq.1, by
                                                  exact Relation.ReflTransGen.refl ⟩ ) hq.2
      simpa using this

private theorem star_language_forward {α : Type u} (r : RegExp α)
    (hr : epsilonLanguage (thompsonNFA r) = languageOf r) :
    ∀ {w}, w ∈ epsilonLanguage (thompsonNFA (.star r)) →
      UAM_RegularLanguages.KleeneStar (languageOf r) w := by
  intro w hw
  obtain ⟨f, hf, hrun⟩ := (mem_epsilonLanguage_iff_run _ _).1 hw
  have hfeq : f = ThompsonState.exit := by simpa [thompsonNFA] using hf
  subst f
  obtain ⟨ws, hws, rfl⟩ := star_run_decompose r hrun
  have hwords : ∀ x ∈ ws, x ∈ languageOf r := by
    intro x hx
    rw [← hr]
    exact hws x hx
  have hlist : ∀ (zs : List (UAM_Free.FreeMonoid α)),
      (∀ x ∈ zs, x ∈ languageOf r) →
      UAM_RegularLanguages.KleeneStar (languageOf r) zs.flatten := by
    intro zs hzs
    induction zs with
    | nil => exact UAM_RegularLanguages.KleeneStar.empty
    | cons x xs ih =>
        apply UAM_RegularLanguages.KleeneStar.concat x xs.flatten
        · exact UAM_RegularLanguages.KleeneStar.word x (hzs x (by simp))
        · exact ih (fun y hy => hzs y (by simp [hy]))
  exact hlist ws hwords

private theorem thompson_star_correct {α : Type u} (r : RegExp α)
    (hr : epsilonLanguage (thompsonNFA r) = languageOf r) :
    epsilonLanguage (thompsonNFA (.star r)) = languageOf (.star r) := by
  ext w
  constructor
  intro hw;
  · exact UAM_Thompson.star_language_forward r hr hw;
  · convert star_language_backward r hr using 1

/-- Thompson's construction denotes exactly the language of its expression. -/
theorem thompson_correct {α : Type u} (r : RegExp α) :
    epsilonLanguage (thompsonNFA (α := α) r) = languageOf r := by
  induction r with
  | empty_set => exact thompson_empty_set_correct
  | empty_str => exact thompson_empty_str_correct
  | atom a => exact thompson_atom_correct a
  | alt r s hr hs => exact thompson_alt_correct r s hr hs
  | concat r s hr hs => exact thompson_concat_correct r s hr hs
  | star r hr => exact thompson_star_correct r hr

end
end UAM_Thompson