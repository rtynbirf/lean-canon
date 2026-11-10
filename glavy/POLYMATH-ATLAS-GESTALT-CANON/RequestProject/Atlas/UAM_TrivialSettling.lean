import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Free
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Group
import RequestProject.Atlas.UAM_FiniteSemigroup

/-!
# UAM_TrivialSettling — Тривиальность и настоящность застывания

Когда конечный моноид «застывает» (обязательный идемпотент из UAM_Beginning),
этот факт имеет разный «вес»:

* В **группе** единственный идемпотент — `1`. Застывание тривиально.
* В **не-групповом** моноиде есть «настоящий» идемпотент `e ≠ 1`.
  Застывание порождает качественно новое состояние.

Основной результат: конечный моноид является группой тогда и только тогда,
когда все его идемпотенты тривиальны.

Это уточняет claim 2 из `UAM_Thesis`: там мы могли только утверждать
`∃ e, IsIdempotent e` для всякого конечного моноида. Теперь мы знаем: если
моноид не группа, то идемпотент настоящий (`e ≠ 1`).
-/

namespace UAM_TrivialSettling

open UAM_Idempotent

/-- Моноид имеет только тривиальный идемпотент: единственный идемпотент — `1`. -/
def HasOnlyTrivialIdempotent (M : Type*) [Monoid M] : Prop :=
  ∀ e : M, IsIdempotent e → e = 1

/-- В моноиде существует нетривиальный идемпотент, отличный от `1`. -/
def HasNonTrivialIdempotent (M : Type*) [Monoid M] : Prop :=
  ∃ e : M, IsIdempotent e ∧ e ≠ 1

/-- **Теорема 1.** Единица всегда является идемпотентом. -/
theorem trivial_idempotent_one (M : Type*) [Monoid M] :
    IsIdempotent (1 : M) := by
  simp [IsIdempotent]

/-- **Теорема 2.** Тривиальность всех идемпотентов равносильна отсутствию
нетривиального идемпотента. Конечность для этого логического факта не нужна. -/
theorem only_trivial_iff_not_nontrivial (M : Type*) [Monoid M] [Finite M] :
    HasOnlyTrivialIdempotent M ↔ ¬ HasNonTrivialIdempotent M := by
  constructor
  · intro h ⟨e, he, hne⟩
    exact hne (h e he)
  · intro h e he
    by_contra hne
    exact h ⟨e, he, hne⟩

/-- **Теорема 3.** Во всякой группе единственный идемпотент — единица. -/
theorem group_has_only_trivial_idempotent (G : Type*) [Group G] :
    HasOnlyTrivialIdempotent G := by
  intro e he
  calc
    e = e⁻¹ * (e * e) := by simp
    _ = e⁻¹ * e := by rw [he]
    _ = 1 := inv_mul_cancel e

/-- **Теорема 4.** Групповой источник гомоморфизма имеет только тривиальный
идемпотент; сам гомоморфизм для этого внутреннего факта несущественен. -/
theorem only_trivial_idempotent_of_subgroup {M : Type*} [Monoid M]
    {G : Type*} [Group G] (_f : G →* M) :
    HasOnlyTrivialIdempotent G := by
  exact group_has_only_trivial_idempotent G

/-- **Теорема 5.** Конечный моноид с только тривиальным идемпотентом является
группой. Указанное сокращение сохранено как часть формулировки, но оказывается
излишним: положительная идемпотентная степень уже даёт обратный элемент. -/
theorem finite_only_trivial_imp_group_of_cancel {M : Type*} [Monoid M] [Finite M]
    (_h_cancel : ∀ a b c : M, a * b = a * c → b = c)
    (h_trivial : HasOnlyTrivialIdempotent M) :
    UAM_Group.IsGroup M := by
  letI := Fintype.ofFinite M
  intro a
  obtain ⟨n, hn_pos, hn_idem⟩ := UAM_FiniteSemigroup.exists_idempotent_pow a
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
  have hk_one : a ^ (k + 1) = 1 := h_trivial _ hn_idem
  refine ⟨a ^ k, ?_, ?_⟩
  · rw [← pow_succ']
    exact hk_one
  · rw [← pow_succ]
    exact hk_one

/-- **Теорема 6.** Конечный коммутативный моноид с только тривиальным
идемпотентом является группой. -/
theorem finite_comm_only_trivial_imp_group {M : Type*} [CommMonoid M] [Finite M]
    (h_trivial : HasOnlyTrivialIdempotent M) :
    UAM_Group.IsGroup M := by
  letI := Fintype.ofFinite M
  intro a
  obtain ⟨n, hn_pos, hn_idem⟩ := UAM_FiniteSemigroup.exists_idempotent_pow a
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
  have hk_one : a ^ (k + 1) = 1 := h_trivial _ hn_idem
  refine ⟨a ^ k, ?_, ?_⟩
  · rw [← pow_succ']
    exact hk_one
  · rw [← pow_succ]
    exact hk_one

/-- **Теорема 7.** Конечный моноид, все идемпотенты которого тривиальны,
обязан быть группой; дополнительных условий сокращения не требуется. -/
theorem finite_only_trivial_imp_group {M : Type*} [Monoid M] [Finite M]
    (h_trivial : HasOnlyTrivialIdempotent M) :
    UAM_Group.IsGroup M := by
  letI := Fintype.ofFinite M
  intro a
  obtain ⟨n, hn_pos, hn_idem⟩ := UAM_FiniteSemigroup.exists_idempotent_pow a
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
  have hk_one : a ^ (k + 1) = 1 := h_trivial _ hn_idem
  refine ⟨a ^ k, ?_, ?_⟩
  · rw [← pow_succ']
    exact hk_one
  · rw [← pow_succ]
    exact hk_one

/-- **Теорема 8.** Конечный негрупповой моноид имеет нетривиальный
идемпотент — точку настоящего застывания. -/
theorem non_group_finite_has_nontrivial_idempotent {M : Type*} [Monoid M] [Finite M]
    (h_not_group : ¬ UAM_Group.IsGroup M) :
    HasNonTrivialIdempotent M := by
  by_contra h
  have htrivial : HasOnlyTrivialIdempotent M :=
    (only_trivial_iff_not_nontrivial M).2 h
  exact h_not_group (finite_only_trivial_imp_group htrivial)

/-- **Теорема 9.** В группе застывание иллюзорно: всякий идемпотент уже
равен единице, поэтому нового состояния не возникает. -/
theorem group_settling_is_vacuous (G : Type*) [Group G] :
    ∀ e : G, IsIdempotent e → e = 1 := by
  exact group_has_only_trivial_idempotent G

/-- Внутренняя форма группового факта для принятого в проекте предиката
`UAM_Group.IsGroup`. -/
theorem group_only_trivial_of_isGroup {M : Type*} [Monoid M]
    (hgroup : UAM_Group.IsGroup M) (e : M) (he : IsIdempotent e) : e = 1 := by
  obtain ⟨b, heb, _⟩ := hgroup e
  calc
    e = e * 1 := (mul_one e).symm
    _ = e * (e * b) := by rw [heb]
    _ = (e * e) * b := by rw [mul_assoc]
    _ = e * b := by rw [he]
    _ = 1 := heb

/-- **Теорема 10.** Настоящее застывание в конечном моноиде происходит
ровно тогда, когда моноид не является группой. -/
theorem real_settling_characterization (M : Type*) [Monoid M] [Finite M] :
    HasNonTrivialIdempotent M ↔ ¬ UAM_Group.IsGroup M := by
  constructor
  · rintro ⟨e, he, hne⟩ hgroup
    exact hne (group_only_trivial_of_isGroup hgroup e he)
  · exact non_group_finite_has_nontrivial_idempotent

end UAM_TrivialSettling
