/-
# Gestalt L4/L5 — голографический сканер и условия возникновения (Genesis Conditions)

Два слоя Gestalt, которые до сих пор оставались неформализованными, записаны
здесь как проверяемые утверждения, а не как метафоры.

**L4 «Голографический сканер».**  Сканер — пара «кодировщик/восстановитель»
`Scanner S L`.  Точность восстановления определена как `Faithful`
(`decode ∘ encode = id`).  Доказано:

* `faithful_iff_leftInverse`, `Faithful.injective` — точный сканер в точности
  тот, у которого кодировщик обратим слева, а значит инъективен;
* `exists_faithful_iff_exists_injective` — точный сканер существует ровно
  тогда, когда существует инъективное кодирование;
* `no_faithful_scanner_of_card_lt` — **предел сжатия**: если латентное
  пространство меньше пространства состояний, точного сканера не существует;
* `exists_reconstruction_error` — более того, у *любого* сканера найдётся
  состояние, которое он восстанавливает неверно.

Это и есть формальный аналог «границы Фано» для данной постановки: сжатие
ниже мощности пространства состояний обязано терять информацию.

**L5 «Genesis Conditions».**  Условия возникновения адаптивного агента
записаны как структура `GenesisConditions` (поля-гипотезы, не аксиомы):
живая среда, планировщик-минимизатор и *геометрическое* условие сжатия —
апостериорное распределение пропускается через латентный код меньшей
мощности.  Главная теорема слоя — `genesis_implies_preconditions`:
Genesis Conditions **влекут** `AdaptivePreconditions` (C1–C3), причём C3
получается не постулированием, а принципом Дирихле.

Непустота слоя проверена конкретным свидетелем (`demoGenesis`).
-/
import RequestProject.AdaptiveAgent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PolymathAtlas.Gestalt.Holographic

open PolymathAtlas.AdaptiveAgent

/-! ## L4 — голографический сканер -/

/-- Голографический сканер: кодирование состояния в латентное пространство и
восстановление состояния по коду. -/
structure Scanner (S L : Type*) where
  /-- Кодировщик. -/
  encode : S → L
  /-- Восстановитель. -/
  decode : L → S

namespace Scanner

variable {S L : Type*}

/-- Сканер **точен**, если восстановление возвращает исходное состояние. -/
def Faithful (sc : Scanner S L) : Prop := ∀ s, sc.decode (sc.encode s) = s

theorem faithful_iff_leftInverse (sc : Scanner S L) :
    sc.Faithful ↔ Function.LeftInverse sc.decode sc.encode := Iff.rfl

/-- Точный сканер кодирует состояния различимо. -/
theorem Faithful.injective {sc : Scanner S L} (h : sc.Faithful) :
    Function.Injective sc.encode :=
  Function.LeftInverse.injective h

/-- Точный сканер существует ровно тогда, когда существует инъективное
кодирование. -/
theorem exists_faithful_iff_exists_injective [Nonempty S] :
    (∃ sc : Scanner S L, sc.Faithful) ↔ ∃ f : S → L, Function.Injective f := by
  constructor
  · rintro ⟨sc, h⟩
    exact ⟨sc.encode, h.injective⟩
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg⟩ := hf.hasLeftInverse
    exact ⟨⟨f, g⟩, hg⟩

/-- **Предел сжатия.**  Если латентное пространство строго меньше
пространства состояний, точного сканера не существует. -/
theorem no_faithful_scanner_of_card_lt [Fintype S] [Fintype L]
    (h : Fintype.card L < Fintype.card S) : ¬ ∃ sc : Scanner S L, sc.Faithful := by
  rintro ⟨sc, hsc⟩
  exact absurd (Fintype.card_le_of_injective sc.encode hsc.injective) (by omega)

/-- **Ошибка восстановления неизбежна.**  У любого сканера в пересжатое
латентное пространство есть состояние, восстановленное неверно. -/
theorem exists_reconstruction_error [Fintype S] [Fintype L]
    (h : Fintype.card L < Fintype.card S) (sc : Scanner S L) :
    ∃ s : S, sc.decode (sc.encode s) ≠ s := by
  by_contra hcon
  push_neg at hcon
  exact no_faithful_scanner_of_card_lt h ⟨sc, hcon⟩

/-- Пересжатие обязательно склеивает два различных состояния. -/
theorem exists_collision [Fintype S] [Fintype L]
    (h : Fintype.card L < Fintype.card S) (f : S → L) :
    ∃ y z : S, y ≠ z ∧ f y = f z := by
  have hni : ¬ Function.Injective f := fun hf =>
    absurd (Fintype.card_le_of_injective f hf) (by omega)
  rw [Function.not_injective_iff] at hni
  obtain ⟨y, z, hfz, hne⟩ := hni
  exact ⟨y, z, hne, hfz⟩

end Scanner

/-! ## L5 — Genesis Conditions -/

/-- **Условия возникновения адаптивного агента.**  Поля — гипотезы о
конкретной системе, а не аксиомы:

* `alive` — среда продолжает порождать сигнал (живой поток);
* `plans_minimally` — планировщик выбирает действие с минимальной ожидаемой
  свободной энергией;
* `code` вместе с `code_determines_posterior` — апостериорное распределение
  пропускается через латентный код;
* `latent_smaller` — латентное пространство строго меньше пространства
  состояний.

Последние два поля — «порождающее сжатие»: не постулат о существовании двух
неразличимых состояний, а геометрическое условие на размерность кода. -/
structure GenesisConditions {S A Latent : Type*} [Fintype Latent] [Fintype S]
    (M : ActivePolicyAgent S A Latent) (s : ObservationStream) (x : S) : Prop where
  /-- G1: поток наблюдений не умирает. -/
  alive : Live s
  /-- G2: планировщик минимизирует ожидаемую свободную энергию. -/
  plans_minimally : ∀ a, M.efe x (M.plan x) ≤ M.efe x a
  /-- G3a: апостериорное распределение пропускается через латентный код. -/
  compresses_through_code : ∃ code : S → Latent,
    ∀ y z : S, code y = code z → M.family.posterior y = M.family.posterior z
  /-- G3b: латентное пространство строго меньше пространства состояний. -/
  latent_smaller : Fintype.card Latent < Fintype.card S

/-- **Genesis Conditions влекут AdaptivePreconditions.**  Условие C3
(«латентный код действительно сжимает») здесь не постулируется, а выводится:
пересжатие обязано склеить два различных состояния (принцип Дирихле), а склейка
кода по G3b влечёт совпадение апостериорных распределений. -/
theorem genesis_implies_preconditions {S A Latent : Type*} [Fintype Latent] [Fintype S]
    {M : ActivePolicyAgent S A Latent} {s : ObservationStream} {x : S}
    (G : GenesisConditions M s x) : AdaptivePreconditions M s x where
  live := G.alive
  optimal := G.plans_minimally
  compresses := by
    obtain ⟨code, hcode⟩ := G.compresses_through_code
    obtain ⟨y, z, hne, hcol⟩ := Scanner.exists_collision G.latent_smaller code
    exact ⟨y, z, hne, hcode y z hcol⟩

/-- Отсюда — полная спецификация L6 при добавлении двух оставшихся условий. -/
theorem genesis_spec_of_acts_bounded {S A Latent : Type*} [Fintype Latent] [Fintype S]
    {M : ActivePolicyAgent S A Latent} {s : ObservationStream} {x : S}
    (G : GenesisConditions M s x)
    (hacts : ∃ y : S, M.forward y (M.plan y) ≠ y)
    (hbound : ∃ B : ℝ, ∀ (y : S) (a : A), M.efe y a ≤ B) :
    AdaptiveAgentSpec M s x where
  toAdaptivePreconditions := genesis_implies_preconditions G
  acts := hacts
  bounded := hbound

/-! ## Непустота: конкретный свидетель -/

/-- Поток наблюдений, активный в каждый момент. -/
def demoStream : ObservationStream := fun _ => ⟨0, 1⟩

theorem demoStream_live : Live demoStream :=
  fun t => ⟨t, le_refl t, by simp [demoStream, Active]⟩

/-- Флип-агент на `Bool` с латентным пространством `Unit` удовлетворяет
условиям возникновения: код тривиален, латентное пространство меньше
пространства состояний, поток жив, планировщик минимален. -/
noncomputable def demoAgent : ActivePolicyAgent Bool Bool Unit where
  family :=
    { prior := fun _ => 1
      posterior := fun _ _ => 1
      prior_pos := fun _ => one_pos
      posterior_pos := fun _ _ => one_pos
      prior_sum := by simp
      posterior_sum := by intro _; simp }
  forward := fun s _ => !s
  preference := fun _ => 0
  preference_nonpos := fun _ => le_refl 0
  plan := fun _ => true

@[simp] theorem demoAgent_efe (s a : Bool) : demoAgent.efe s a = 0 := by
  simp [ActivePolicyAgent.efe, ActivePolicyAgent.risk, ActivePolicyAgent.ambiguity,
    demoAgent, VariationalFamily.complexity, klDiv]

/-- Свидетель условий возникновения. -/
theorem demoGenesis (x : Bool) : GenesisConditions demoAgent demoStream x where
  alive := demoStream_live
  plans_minimally a := by simp
  compresses_through_code := ⟨fun _ => (), by intro y z _; rfl⟩
  latent_smaller := by decide

/-- Условия возникновения непусты и действительно дают адаптивного агента. -/
theorem demoGenesis_preconditions (x : Bool) : AdaptivePreconditions demoAgent demoStream x :=
  genesis_implies_preconditions (demoGenesis x)

end PolymathAtlas.Gestalt.Holographic
