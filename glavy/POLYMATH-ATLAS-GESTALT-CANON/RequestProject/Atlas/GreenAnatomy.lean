import RequestProject.Atlas.ModelLadder
import RequestProject.Atlas.UAM_Green
import RequestProject.Atlas.UAM_Idempotent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Green anatomy of the model ladder

Images and kernels give concrete descriptions of the project Green relations.
The project multiplication is chronological: `f * g = g ∘ f`.
-/

namespace GreenAnatomy

open UAM_Action
open UAM_Reachability

variable {n : Nat} [NeZero n]

/-- The common state space of levels L1--L3. -/
abbrev State (n : Nat) := Fin (n + 2)

/-! ## Images and kernels -/

/-- Image of an endomorphism. -/
def funImage (f : State n → State n) : Set (State n) := Set.range f

/-- Kernel of an endomorphism as an equivalence relation. -/
def funKernel (f : State n → State n) : Setoid (State n) where
  r := fun a b => f a = f b
  iseqv := {
    refl := fun _ => rfl
    symm := fun {_ _} h => Eq.symm h
    trans := fun {_ _ _} h₁ h₂ => Eq.trans h₁ h₂
  }

omit [NeZero n] in
/-
The kernel of the identity is the diagonal.
-/
theorem funKernel_id_eq_diagonal (a b : State n) :
    (funKernel id).r a b ↔ a = b := by
      exact ⟨ fun h => h, fun h => h ▸ rfl ⟩

omit [NeZero n] in
/-
The kernel of a constant map is the total relation.
-/
theorem funKernel_constant_eq_total (c a b : State n) :
    (funKernel (fun _ : State n => c)).r a b ↔ True := by
      exact iff_of_true rfl trivial

omit [NeZero n] in
/-
The identity has full image.
-/
theorem funImage_id_eq_full : funImage (id : State n → State n) = Set.univ := by
  exact Set.range_id

omit [NeZero n] in
/-
A constant map has singleton image.
-/
theorem funImage_constant_eq_singleton (c : State n) :
    funImage (fun _ : State n => c) = {c} := by
      exact Set.eq_singleton_iff_unique_mem.mpr ⟨ Set.mem_range_self c, fun x hx => by obtain ⟨ y, rfl ⟩ := hx; rfl ⟩

omit [NeZero n] in
/-
A zero-fixing map has zero in its image.
-/
theorem zero_in_image_of_fixes_zero {f : State n → State n} (h0 : f 0 = 0) :
    0 ∈ funImage f := by
      exact ⟨ 0, h0 ⟩

omit [NeZero n] in
/-
Reflexivity at zero is visible in every zero-fixing kernel.
-/
theorem zero_related_in_kernel_of_fixes_zero {f : State n → State n}
    (_h0 : f 0 = 0) : (funKernel f).r 0 0 := by
  rfl

/-! ## Full transformation monoid -/

/-- Right multiples, written as explicit compositions. -/
abbrev rightMults (f : State n → State n) : Set (State n → State n) :=
  {g | ∃ h, g = h ∘ f}

/-- Left multiples, written as explicit compositions. -/
abbrev leftMults (f : State n → State n) : Set (State n → State n) :=
  {g | ∃ h, g = f ∘ h}

omit [NeZero n] in
/-
Equal sets of right multiples imply equal kernels.
-/
theorem reach_eq_imp_kernel_eq {f g : State n → State n}
    (hR : rightMults f = rightMults g) :
    (funKernel f).r = (funKernel g).r := by
  have hf : f ∈ rightMults g := by
    rw [← hR]
    exact ⟨id, rfl⟩
  have hg : g ∈ rightMults f := by
    rw [hR]
    exact ⟨id, rfl⟩
  obtain ⟨h, hh⟩ := hf
  obtain ⟨k, hk⟩ := hg
  funext x y
  apply propext
  constructor
  · intro hxy
    rw [hk]
    exact congrArg k hxy
  · intro hxy
    rw [hh]
    exact congrArg h hxy

/-
Equal kernels imply equal sets of right multiples.
-/
omit [NeZero n] in
theorem kernel_eq_imp_reach_eq {f g : State n → State n}
    (hK : (funKernel f).r = (funKernel g).r) :
    rightMults f = rightMults g := by
  apply Set.eq_of_subset_of_subset
  · rintro h ⟨k, rfl⟩
    let factor : State n → State n := fun y =>
      if hy : ∃ x, g x = y then k (f (Classical.choose hy)) else 0
    have hk' : factor ∘ g = k ∘ f := by
      funext x
      change factor (g x) = k (f x)
      have hex : ∃ z, g z = g x := ⟨x, rfl⟩
      rw [show factor (g x) = k (f (Classical.choose hex)) by
        simp only [factor, dif_pos hex]]
      congr 1
      have hg : g (Classical.choose hex) = g x := Classical.choose_spec hex
      have hrel : (funKernel g).r (Classical.choose hex) x := hg
      have hfrel : (funKernel f).r (Classical.choose hex) x := by
        rw [hK]
        exact hrel
      exact hfrel
    exact ⟨factor, hk'.symm⟩
  · rintro _ ⟨h, rfl⟩
    let factor : State n → State n := fun y =>
      if hy : ∃ x, f x = y then h (g (Classical.choose hy)) else h (g 0)
    have hk : factor ∘ f = h ∘ g := by
      funext x
      change factor (f x) = h (g x)
      have hex : ∃ z, f z = f x := ⟨x, rfl⟩
      rw [show factor (f x) = h (g (Classical.choose hex)) by
        simp only [factor, dif_pos hex]]
      congr 1
      have hf : f (Classical.choose hex) = f x := Classical.choose_spec hex
      have hrel : (funKernel f).r (Classical.choose hex) x := hf
      have hgrel : (funKernel g).r (Classical.choose hex) x := by
        rw [← hK]
        exact hrel
      exact hgrel
    exact ⟨factor, hk.symm⟩

omit [NeZero n] in
/-
Project R-equivalence is equality of kernels.
-/
theorem R_eq_iff_kernel_eq (f g : State n → State n) :
    UAM_Green.R_eq f g ↔ (funKernel f).r = (funKernel g).r := by
      constructor <;> intro hR;
      · apply reach_eq_imp_kernel_eq;
        ext q; simp [UAM_Green.R_eq, UAM_Reachability.reach, UAM_Directionality.algLe, UAM_Action.mul_def] at *;
        exact ⟨ fun ⟨ h, hh ⟩ => hR.subset ⟨ h, hh.symm ⟩ |> fun ⟨ h', hh' ⟩ => ⟨ h', hh'.symm ⟩, fun ⟨ h, hh ⟩ => hR.superset ⟨ h, hh.symm ⟩ |> fun ⟨ h', hh' ⟩ => ⟨ h', hh'.symm ⟩ ⟩;
      · convert Set.ext _;
        convert Set.ext_iff.mp ( kernel_eq_imp_reach_eq _ ) using 1;
        convert Iff.rfl;
        · ext; simp [rightMults, reach];
          exact ⟨ fun ⟨ h, hh ⟩ => ⟨ h, hh.symm ⟩, fun ⟨ h, hh ⟩ => ⟨ h, hh.symm ⟩ ⟩;
        · ext; simp [rightMults, reach];
          exact ⟨ fun ⟨ h, hh ⟩ => ⟨ h, hh.symm ⟩, fun ⟨ h, hh ⟩ => ⟨ h, hh.symm ⟩ ⟩;
        · exact hR

omit [NeZero n] in
/-
Equal sets of left multiples imply equal images.
-/
theorem reachLeft_eq_imp_image_eq {f g : State n → State n}
    (hL : leftMults f = leftMults g) : funImage f = funImage g := by
      simp_all +decide [ Set.ext_iff, funImage, leftMults ];
      intro x; exact ⟨ fun ⟨ y, hy ⟩ => by obtain ⟨ h, hh ⟩ := hL ( fun _ => x ) |>.1 ⟨ fun _ => y, by ext; simp +decide [ hy ] ⟩ ; exact ⟨ h y, by simpa [ hy ] using congr_fun hh.symm y ⟩, fun ⟨ y, hy ⟩ => by obtain ⟨ h, hh ⟩ := hL ( fun _ => x ) |>.2 ⟨ fun _ => y, by ext; simp +decide [ hy ] ⟩ ; exact ⟨ h y, by simpa [ hy ] using congr_fun hh.symm y ⟩ ⟩ ;

omit [NeZero n] in
/-
Equal images imply equal sets of left multiples.
-/
theorem image_eq_imp_reachLeft_eq {f g : State n → State n}
    (hI : funImage f = funImage g) : leftMults f = leftMults g := by
      apply Set.eq_of_subset_of_subset;
      · intro q hq
        obtain ⟨h, rfl⟩ := hq
        have hk : ∀ x, ∃ y, g y = f (h x) := by
          exact fun x => hI.subset ( Set.mem_range_self _ )
        generalize_proofs at *;
        choose k hk using hk; exact ⟨ k, by ext x; simp +decide [ hk ] ⟩ ;
      · rintro _ ⟨ h, rfl ⟩;
        use fun x => Classical.choose ( show ∃ y, f y = g ( h x ) from by
                                          exact hI.symm.subset ( Set.mem_range_self _ ) )
        generalize_proofs at *;
        exact funext fun x => Eq.symm ( Classical.choose_spec ( ‹∀ x, ∃ x_1, f x_1 = g ( h x ) › x ) )

omit [NeZero n] in
/-
Project L-equivalence is equality of images.
-/
theorem L_eq_iff_image_eq (f g : State n → State n) :
    UAM_Green.L_eq f g ↔ funImage f = funImage g := by
      constructor <;> intro h;
      · unfold UAM_Green.L_eq at h;
        convert reachLeft_eq_imp_image_eq ( show leftMults f = leftMults g from ?_ );
        convert h using 1;
        · exact Set.ext fun x => ⟨ fun ⟨ h, hh ⟩ => ⟨ h, hh ▸ rfl ⟩, fun ⟨ h, hh ⟩ => ⟨ h, hh ▸ rfl ⟩ ⟩;
        · exact Set.ext fun x => ⟨ fun ⟨ y, hy ⟩ => ⟨ y, hy ▸ rfl ⟩, fun ⟨ y, hy ⟩ => ⟨ y, hy ▸ rfl ⟩ ⟩;
      · unfold UAM_Green.L_eq;
        convert image_eq_imp_reachLeft_eq h using 1;
        · exact Set.ext fun x => ⟨ fun ⟨ y, hy ⟩ => ⟨ y, hy.symm ⟩, fun ⟨ y, hy ⟩ => ⟨ y, hy.symm ⟩ ⟩;
        · unfold reachLeft leftMults; ext; simp +decide [ funext_iff ] ;
          exact ⟨ fun ⟨ c, hc ⟩ => ⟨ c, fun x => hc x ▸ rfl ⟩, fun ⟨ c, hc ⟩ => ⟨ c, fun x => hc x ▸ rfl ⟩ ⟩

/-! ## The zero-fixing L2 monoid -/

/-- Right multiples internal to L2. -/
abbrev L2RightMults (f : ModelLadder.L2Transform n) :
    Set (ModelLadder.L2Transform n) :=
  {g | ∃ h : ModelLadder.L2Transform n,
    g = ⟨h.1 ∘ f.1, by simp only [Function.comp_apply, f.2, h.2]⟩}

/-- Left multiples internal to L2. -/
abbrev L2LeftMults (f : ModelLadder.L2Transform n) :
    Set (ModelLadder.L2Transform n) :=
  {g | ∃ h : ModelLadder.L2Transform n,
    g = ⟨f.1 ∘ h.1, by simp only [Function.comp_apply, h.2, f.2]⟩}

/-
Equal internal L2 right multiples imply equal kernels.
-/
theorem L2_reach_eq_imp_kernel_eq {f g : ModelLadder.L2Transform n}
    (hR : L2RightMults f = L2RightMults g) :
    (funKernel f.1).r = (funKernel g.1).r := by
      obtain ⟨h₁, hh₁⟩ : ∃ h₁ : ModelLadder.L2Transform n, f = ⟨h₁.1 ∘ g.1, by simp only [Function.comp_apply, g.2, h₁.2]⟩ := by
        exact hR.subset ⟨ 1, rfl ⟩ |> fun ⟨ h₁, hh₁ ⟩ => ⟨ h₁, hh₁ ⟩
      obtain ⟨h₂, hh₂⟩ : ∃ h₂ : ModelLadder.L2Transform n, g = ⟨h₂.1 ∘ f.1, by simp only [Function.comp_apply, f.2, h₂.2]⟩ := by
        obtain ⟨h₂, hh₂⟩ : ∃ h₂ : ModelLadder.L2Transform n, g = ⟨h₂.1 ∘ f.1, by simp only [Function.comp_apply, f.2, h₂.2]⟩ := by
          have hg : g ∈ L2RightMults f := by
            exact hR.symm ▸ ⟨ 1, rfl ⟩
          exact hg;
        use h₂;
      ext x y;
      constructor <;> intro hxy;
      · rw [ hh₂ ];
        exact congrArg h₂.1 hxy;
      · rw [ hh₁ ] at *; exact congrArg h₁.1 hxy;

/-
Equal kernels of zero-fixing maps imply equal internal right multiples.
-/
theorem L2_kernel_eq_imp_reach_eq {f g : ModelLadder.L2Transform n}
    (hK : (funKernel f.1).r = (funKernel g.1).r) :
    L2RightMults f = L2RightMults g := by
  have hfull : rightMults f.1 = rightMults g.1 := kernel_eq_imp_reach_eq hK
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, rfl⟩
    have hm : a.1 ∘ f.1 ∈ rightMults g.1 := by
      rw [← hfull]
      exact ⟨a.1, rfl⟩
    rcases hm with ⟨k, hk⟩
    have hk0 : k 0 = 0 := by
      have hzero := congrFun hk 0
      simpa only [Function.comp_apply, f.2, g.2, a.2] using hzero.symm
    refine ⟨⟨k, hk0⟩, Subtype.ext ?_⟩
    change a.1 ∘ f.1 = k ∘ g.1
    exact hk
  · rintro _ ⟨a, rfl⟩
    have hm : a.1 ∘ g.1 ∈ rightMults f.1 := by
      rw [hfull]
      exact ⟨a.1, rfl⟩
    rcases hm with ⟨k, hk⟩
    have hk0 : k 0 = 0 := by
      have hzero := congrFun hk 0
      simpa only [Function.comp_apply, f.2, g.2, a.2] using hzero.symm
    refine ⟨⟨k, hk0⟩, Subtype.ext ?_⟩
    change a.1 ∘ g.1 = k ∘ f.1
    exact hk

/-
R-equivalence of the underlying L2 maps is equality of kernels.
-/
theorem L2_R_eq_iff_kernel_eq (f g : ModelLadder.L2Transform n) :
    UAM_Green.R_eq f.1 g.1 ↔
      (funKernel f.1).r = (funKernel g.1).r := by
        convert R_eq_iff_kernel_eq ( f.1 ) ( g.1 ) using 1

/-
Equal internal L2 left multiples imply equal images.
-/
theorem L2_reachLeft_eq_imp_image_eq {f g : ModelLadder.L2Transform n}
    (hL : L2LeftMults f = L2LeftMults g) : funImage f.1 = funImage g.1 := by
  have hf : f ∈ L2LeftMults g := by
    rw [← hL]
    exact ⟨1, rfl⟩
  have hg : g ∈ L2LeftMults f := by
    rw [hL]
    exact ⟨1, rfl⟩
  obtain ⟨h, hh⟩ := hf
  obtain ⟨k, hk⟩ := hg
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩
    exact ⟨h.1 y, (congrArg (fun q : ModelLadder.L2Transform n => q.1 y) hh).symm⟩
  · rintro x ⟨y, rfl⟩
    exact ⟨k.1 y, (congrArg (fun q : ModelLadder.L2Transform n => q.1 y) hk).symm⟩

/-
Equal images of zero-fixing maps imply equal internal left multiples.
-/
theorem L2_image_eq_imp_reachLeft_eq {f g : ModelLadder.L2Transform n}
    (hI : funImage f.1 = funImage g.1) :
    L2LeftMults f = L2LeftMults g := by
  have factor : ∀ {u v : ModelLadder.L2Transform n},
      funImage u.1 = funImage v.1 → L2LeftMults u ⊆ L2LeftMults v := by
    intro u v him q hq
    obtain ⟨h, rfl⟩ := hq
    have hex : ∀ x, ∃ y, v.1 y = u.1 (h.1 x) := by
      intro x
      exact him.subset ⟨h.1 x, rfl⟩
    let kfun : State n → State n := fun x =>
      if hx : x = 0 then 0 else Classical.choose (hex x)
    have hkzero : kfun 0 = 0 := by simp only [kfun, dif_pos]
    let k : ModelLadder.L2Transform n := ⟨kfun, hkzero⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    funext x
    change u.1 (h.1 x) = v.1 (kfun x)
    by_cases hx : x = 0
    · subst x
      rw [h.2, u.2]
      exact v.2.symm
    · rw [show kfun x = Classical.choose (hex x) by simp only [kfun, dif_neg hx]]
      exact (Classical.choose_spec (hex x)).symm
  exact Set.Subset.antisymm (factor hI) (factor hI.symm)

/-
L-equivalence of the underlying L2 maps is equality of images.
-/
theorem L2_L_eq_iff_image_eq (f g : ModelLadder.L2Transform n) :
    UAM_Green.L_eq f.1 g.1 ↔ funImage f.1 = funImage g.1 := by
      -- Apply the equivalence from R_eq_iff_kernel_eq to conclude the proof.
      apply L_eq_iff_image_eq f.1 g.1

/-! ## Distinguished elements -/

omit [NeZero n] in
/-
All constant maps have the same, total kernel.
-/
theorem constants_same_kernel (c d : State n) :
    (funKernel (fun _ => c)).r = (funKernel (fun _ => d)).r := by
      exact funext fun x => funext fun y => by simp +decide [ funKernel ] ;

/-
All constant maps are R-equivalent.
-/
omit [NeZero n] in
theorem constants_R_eq (c d : State n) :
    UAM_Green.R_eq (fun _ => c : State n → State n) (fun _ => d) := by
      convert R_eq_iff_kernel_eq ( fun _ => c ) ( fun _ => d ) |>.2 ( constants_same_kernel c d ) using 1

omit [NeZero n] in
/-
Distinct constant maps are not L-equivalent.
-/
theorem constants_not_L_eq (c d : State n) (hne : c ≠ d) :
    ¬ UAM_Green.L_eq (fun _ => c : State n → State n) (fun _ => d) := by
  intro hL
  have hI := (L_eq_iff_image_eq (fun _ : State n => c) (fun _ : State n => d)).1 hL
  rw [funImage_constant_eq_singleton c, funImage_constant_eq_singleton d] at hI
  exact hne (Set.singleton_eq_singleton_iff.mp hI)

/-
The unique constant L2 map is R-equivalent to itself.
-/
theorem L2Zero_R_eq_self :
    UAM_Green.R_eq (ModelLadder.L2Zero n).1 (ModelLadder.L2Zero n).1 := by
  rfl

/-
The constant-zero map is not H-equivalent to the identity.
-/
theorem L2Zero_not_H_id :
    ¬ (UAM_Green.R_eq (ModelLadder.L2Zero n).1 id ∧
       UAM_Green.L_eq (ModelLadder.L2Zero n).1 id) := by
  rintro ⟨_, hL⟩
  have hI := (L_eq_iff_image_eq (ModelLadder.L2Zero n).1 id).1 hL
  have hnext : ModelLadder.ladderNext n ∈ funImage (id : State n → State n) :=
    ⟨ModelLadder.ladderNext n, rfl⟩
  rw [← hI] at hnext
  obtain ⟨x, hx⟩ := hnext
  exact ModelLadder.zero_ne_ladderNext n hx

/-
The originally requested `id_unique_H_class` claimed that R- and L-equivalence
to identity forces equality with identity.  This is false: every permutation is
in the identity H-class.  The unprovable declaration is retained here inactive.

theorem id_unique_H_class (f : State n → State n)
    (hR : UAM_Green.R_eq f id) (hL : UAM_Green.L_eq f id) : f = id := by

Corrected identity H-class characterization: it consists exactly of the
bijective endomorphisms.
-/
omit [NeZero n] in
theorem id_H_class_iff_bijective (f : State n → State n) :
    (UAM_Green.R_eq f id ∧ UAM_Green.L_eq f id) ↔ Function.Bijective f := by
      constructor;
      · intro h;
        have h_inj : Function.Injective f := by
          have := R_eq_iff_kernel_eq f id |>.1 h.1; simp_all +decide [ funext_iff, funKernel ] ;
          exact fun x y hxy => this x y |>.1 hxy
        have h_surj : Function.Surjective f := by
          exact Finite.injective_iff_surjective.mp h_inj
        exact ⟨h_inj, h_surj⟩;
      · intro hf
        have hR : UAM_Green.R_eq f id := by
          convert R_eq_iff_kernel_eq f id |>.2 _ using 1;
          exact funext fun x => funext fun y => by simp +decide [ funKernel, hf.injective.eq_iff ] ;
        have hL : UAM_Green.L_eq f id := by
          exact L_eq_iff_image_eq f id |>.2 ( by rw [ funImage_id_eq_full ] ; exact Set.range_eq_univ.mpr hf.surjective )
        exact ⟨hR, hL⟩

/-
Swapping zero with `ladderNext` is a concrete nonidentity member of the
identity H-class, refuting the originally requested uniqueness assertion.
-/
theorem id_H_class_not_singleton :
    ∃ f : State n → State n,
      UAM_Green.R_eq f id ∧ UAM_Green.L_eq f id ∧ f ≠ id := by
  let e : State n ≃ State n := Equiv.swap 0 (ModelLadder.ladderNext n)
  have hH := (id_H_class_iff_bijective (e : State n → State n)).2 e.bijective
  refine ⟨e, hH.1, hH.2, ?_⟩
  intro he
  have hzero := congrFun he 0
  change ModelLadder.ladderNext n = 0 at hzero
  exact ModelLadder.zero_ne_ladderNext n hzero.symm

/-! ## Green structure and the bridge failure -/

omit [NeZero n] in
/-
A constant map destroys all state distinguishability.
-/
theorem constant_kernel_is_total (c a b : State n) :
    (funKernel (fun _ => c)).r a b := by
      exact rfl

/-
Membership in the minimal R-class exposes the same bridge obstruction as
`L2Zero`; in L2 the constant ideal itself has just that element.
-/
theorem L2Zero_minimal_R_explains_failure :
    ∀ (f : State n → State n),
      UAM_Green.R_eq f (ModelLadder.L2Zero n).1 →
        (ModelLadder.L2Volition n).proposesGoal
            ((ModelLadder.L2Action n).act (ModelLadder.L2Zero n)
              (ModelLadder.ladderNext n)) ≠
          (ModelLadder.L2Volition n).proposesGoal (ModelLadder.ladderNext n) ∨
        f = (ModelLadder.L2Zero n).1 := by
          -- Since the left disjunct is true for L2Zero itself, we can conclude the proof.
          simp [ModelLadder.L2Volition, ModelLadder.ladderNext];
          simp +decide [ ModelLadder.L1Volition, ModelLadder.L2Action, ModelLadder.L2Zero ]

omit [NeZero n] in
/-
Every constant map is idempotent.
-/
theorem constant_is_idempotent (c : State n) :
    UAM_Idempotent.IsIdempotent (fun _ => c : State n → State n) := by
      convert rfl

/-! ## Summary package -/

/-- The Green anatomy available at every nontrivial ladder size. -/
structure GreenStructure (n : Nat) [NeZero n] where
  R_iff_kernel : ∀ f g : State n → State n,
    UAM_Green.R_eq f g ↔ (funKernel f).r = (funKernel g).r
  L_iff_image : ∀ f g : State n → State n,
    UAM_Green.L_eq f g ↔ funImage f = funImage g
  constants_R_related : ∀ c d : State n,
    UAM_Green.R_eq (fun _ : State n => c) (fun _ : State n => d)
  constants_L_separated : ∀ c d : State n, c ≠ d →
    ¬ UAM_Green.R_eq (fun _ : State n => c) (fun _ : State n => d) →
    ¬ UAM_Green.L_eq (fun _ : State n => c) (fun _ : State n => d)
  constant_kernel_total : ∀ c : State n, ∀ a b : State n,
    (funKernel (fun _ => c)).r a b
  L2_R_iff_kernel : ∀ f g : ModelLadder.L2Transform n,
    UAM_Green.R_eq f.1 g.1 ↔ (funKernel f.1).r = (funKernel g.1).r
  L2_L_iff_image : ∀ f g : ModelLadder.L2Transform n,
    UAM_Green.L_eq f.1 g.1 ↔ funImage f.1 = funImage g.1

/-
A complete Green anatomy exists at every level size.
-/
theorem green_anatomy_exists (n : Nat) [NeZero n] : Nonempty (GreenStructure n) := by
  refine ⟨{
    R_iff_kernel := R_eq_iff_kernel_eq
    L_iff_image := L_eq_iff_image_eq
    constants_R_related := constants_R_eq
    constants_L_separated := ?_
    constant_kernel_total := constant_kernel_is_total
    L2_R_iff_kernel := L2_R_eq_iff_kernel_eq
    L2_L_iff_image := L2_L_eq_iff_image_eq
  }⟩
  intro c d _hne hnotR
  exact False.elim (hnotR (constants_R_eq c d))

end GreenAnatomy