import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Green            -- R_eq, L_eq, H_eq
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_HClass           -- HClass, green_theorem
import RequestProject.Atlas.UAM_Regular          -- IsRegular

/-!
# UAM — Layer 5: D-отношение Грина (Schutzenberger)

D-отношение Грина `D_rel` — наименьшее отношение эквивалентности,
содержащее объединение отношений `R` и `L`. D-классы — «клетки» полугруппы.
Файл импортирует канонические определения Layer 0–4 и `IsRegular`
из `UAM_Regular` и не переопределяет их.
-/

namespace UAM_Schutzenberger
universe u

open UAM_Directionality UAM_Reachability UAM_Green UAM_Idempotent UAM_HClass UAM_Regular

variable {M : Type u} [Monoid M]

/-! ### §0. Собственные определения -/

/-- D-отношение Грина: наименьшее отношение эквивалентности,
    содержащее `R ∪ L`. -/
def D_rel (a b : M) : Prop :=
  Relation.EqvGen (fun x y : M => R_eq x y ∨ L_eq x y) a b

/-- D-класс элемента `a`: множество всех элементов, D-эквивалентных `a`. -/
def DClass (a : M) : Set M := { b | D_rel a b }

/-- Регулярная полугруппа: каждый элемент регулярен. -/
def IsRegularSemigroup (M : Type u) [Monoid M] : Prop := ∀ a : M, UAM_Regular.IsRegular a

/-! ### §1. D как отношение эквивалентности -/

theorem D_rel_refl (a : M) : D_rel a a :=
  Relation.EqvGen.refl a

theorem D_rel_symm {a b : M} (h : D_rel a b) : D_rel b a :=
  Relation.EqvGen.symm _ _ h

theorem D_rel_trans {a b c : M} (h1 : D_rel a b) (h2 : D_rel b c) : D_rel a c :=
  Relation.EqvGen.trans _ _ _ h1 h2

theorem R_imp_D {a b : M} (h : R_eq a b) : D_rel a b :=
  Relation.EqvGen.rel a b (Or.inl h)

theorem L_imp_D {a b : M} (h : L_eq a b) : D_rel a b :=
  Relation.EqvGen.rel a b (Or.inr h)

/-! ### §2. Связь H и D -/

theorem H_imp_D {a b : M} (h : H_eq a b) : D_rel a b :=
  R_imp_D h.1

theorem H_subset_DClass (a : M) : HClass a ⊆ DClass a :=
  fun _ h => H_imp_D h

theorem DClass_nonempty (a : M) : (DClass a).Nonempty :=
  ⟨a, D_rel_refl a⟩

/-! ### §3. D-класс стабилизируется R и L -/

/-- Если `D a b` и `R a c`, то `D c b`. -/
theorem R_preserves_DClass {a b c : M} (hD : D_rel a b) (hR : R_eq a c) :
    D_rel c b :=
  D_rel_trans (D_rel_symm (R_imp_D hR)) hD

/-- Если `D a b` и `L a c`, то `D c b`. -/
theorem L_preserves_DClass {a b c : M} (hD : D_rel a b) (hL : L_eq a c) :
    D_rel c b :=
  D_rel_trans (D_rel_symm (L_imp_D hL)) hD

/-! ### §4. D-класс и принадлежность -/

theorem DClass_mem_iff_D_rel {a b : M} : b ∈ DClass a ↔ D_rel a b := Iff.rfl

/-! ### §5. Характеризации отношений Грина через кратные -/

/-
`R`-эквивалентность равносильна взаимной правой достижимости.
-/
theorem R_eq_iff {a b : M} :
    R_eq a b ↔ (∃ u, a * u = b) ∧ (∃ v, b * v = a) := by
  constructor <;> intro h;
  · unfold R_eq at h; simp_all +decide [ Set.ext_iff ] ;
    exact ⟨ h b |>.2 ⟨ 1, by simp +decide ⟩, h a |>.1 ⟨ 1, by simp +decide ⟩ ⟩;
  · ext x;
    constructor <;> intro hx <;> obtain ⟨ u, hu ⟩ := hx <;> obtain ⟨ v, hv ⟩ := h.1 <;> obtain ⟨ w, hw ⟩ := h.2 <;> simp_all +decide [ reach ];
    · exact ⟨ w * u, by rw [ ← hu, ← mul_assoc, ← hw ] ⟩;
    · exact ⟨ v * u, by rw [ ← mul_assoc, hv, hu ] ⟩

/-
`L`-эквивалентность равносильна взаимной левой достижимости.
-/
theorem L_eq_iff {a b : M} :
    L_eq a b ↔ (∃ s, s * a = b) ∧ (∃ t, t * b = a) := by
  constructor <;> intro h;
  · exact ⟨ h.symm.subset ⟨ 1, by simp +decide ⟩, h.subset ⟨ 1, by simp +decide ⟩ ⟩;
  · obtain ⟨ ⟨ s, hs ⟩, ⟨ t, ht ⟩ ⟩ := h;
    ext x;
    constructor <;> rintro ⟨ y, rfl ⟩;
    · use y * t;
      rw [ mul_assoc, ht ];
    · exact ⟨ y * s, by simp +decide [ mul_assoc, hs ] ⟩

/-
Лемма Грина (перестановка `L` и `R`): если `x L y` и `y R z`, то
    существует `d` с `x R d` и `d L z`.
-/
theorem green_swap {x y z : M} (hL : L_eq x y) (hR' : R_eq y z) :
    ∃ d, R_eq x d ∧ L_eq d z := by
  obtain ⟨s, hs⟩ : ∃ s : M, s * x = y := by
    exact L_eq_iff.mp hL |>.1
  obtain ⟨t, ht⟩ : ∃ t : M, t * y = x :=
    L_eq_iff.mp hL |>.2
  obtain ⟨u, hu⟩ : ∃ u : M, y * u = z := by
    exact R_eq_iff.mp hR' |>.1
  obtain ⟨v, hv⟩ : ∃ v : M, z * v = y := by
    exact R_eq_iff.mp hR' |>.2;
  refine ⟨x * u, ?_, ?_⟩
  · refine R_eq_iff.mpr ⟨⟨u, rfl⟩, ?_⟩
    refine ⟨v, ?_⟩
    rw [← ht]
    simp only [mul_assoc]
    rw [← mul_assoc y u v, hu, hv]
  · refine L_eq_iff.mpr ⟨?_, ?_⟩
    · exact ⟨s, by rw [← mul_assoc, hs, hu]⟩
    · exact ⟨t, by rw [← hu, ← mul_assoc, ht]⟩

/-! ### §6. Цель: D = R ∘ L

  Классический результат теории D-классов: `D = R ∘ L`. Он выполняется
  в любом моноиде (лемма Грина `green_swap`); гипотеза регулярности `hR`
  не требуется и оставлена по условию задачи. -/
theorem D_eq_R_comp_L_regular : IsRegularSemigroup M → ∀ a b : M,
    (D_rel a b ↔ ∃ c, R_eq a c ∧ L_eq c b) := by
  intro _ a b
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
        rcases hxy with hr | hl
        · exact ⟨y, hr, L_eq_refl y⟩
        · exact ⟨x, R_eq_refl x, hl⟩
    | refl x => exact ⟨x, R_eq_refl x, L_eq_refl x⟩
    | symm x y _ ih =>
        obtain ⟨c, hxc, hcy⟩ := ih
        exact green_swap (L_eq_symm hcy) (R_eq_symm hxc)
    | trans x y z _ _ ihxy ihyz =>
        obtain ⟨c, hxc, hcy⟩ := ihxy
        obtain ⟨d, hyd, hdz⟩ := ihyz
        obtain ⟨m, hcm, hmd⟩ := green_swap hcy hyd
        exact ⟨m, R_eq_trans hxc hcm, L_eq_trans hmd hdz⟩
  · rintro ⟨c, hr, hl⟩
    exact D_rel_trans (R_imp_D hr) (L_imp_D hl)

end UAM_Schutzenberger