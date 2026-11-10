import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Idempotent        -- IsIdempotent
import RequestProject.Atlas.UAM_Directionality     -- algLe
import RequestProject.Atlas.UAM_Reachability       -- reach (использует algLe)
import RequestProject.Atlas.UAM_Cayley             -- Transform, rho, cayley_embedding
import RequestProject.Atlas.UAM_Morphism           -- MonoidMorphism
import RequestProject.Atlas.UAM_Submonoid          -- eMe
import RequestProject.Atlas.UAM_FiniteSemigroup    -- exists_idempotent_pow

/-!
# UAM — Невозможность «чистого начала» (Beginning)

Этот модуль формализует невозможность «чистой алгебры действия» — структуры,
в которой существует лишь действие и ни один объект никогда не фиксируется.

Ключевое наблюдение: теорема Кэли применима к ЛЮБОМУ моноиду безусловно,
поэтому всякая попытка построить моноид «чистого действия» неизбежно
овеществляет действия в объекты через моноид преобразований (`Transform M`).
А в конечном случае принцип Дирихле заставляет появиться идемпотент —
неподвижную точку действия, — что напрямую противоречит идее «чистого начала».

## Замечания о формулировках

* Импорты в исходной постановке задачи указывали `reach` в модуле
  `UAM_Directionality`; на самом деле `reach` определён в
  `UAM_Reachability` (через `algLe`), а `eMe` — в `UAM_Submonoid`.
  Поэтому здесь добавлены корректные импорты.
* «Философские аксиомы» из определения `IsBeginningStructure` формализованы
  буквально. Второй конъюнкт `∀ a c, a * c ≠ a` при `c = 1` даёт `a * 1 ≠ a`,
  что противоречит `mul_one`; таким образом, эта аксиома сама по себе делает
  структуру нереализуемой в любом моноиде. Мы сохраняем формулировку как в
  постановке, но для доказательства невозможности в конечном случае опираемся
  на первый конъюнкт (отсутствие идемпотентов).
-/

namespace UAM_Beginning
universe u

open UAM_Idempotent UAM_Directionality UAM_Reachability
open UAM_Cayley UAM_Morphism UAM_Submonoid UAM_FiniteSemigroup

variable {M : Type u} [Monoid M]

/-! ### §1. Определения структуры «чистого начала» -/

/-- Структура «чистого начала»: моноид, в котором
    * ни один элемент не идемпотентен (`∀ a, ¬IsIdempotent a`) — нет
      неподвижных точек;
    * ни один элемент не является правой неподвижной точкой умножения
      (`∀ a c, a * c ≠ a`) — нет остановки.

    Это прямая формализация философских аксиом «нет неподвижных точек» и
    «нет остановки». -/
def IsBeginningStructure (M : Type u) [Monoid M] : Prop :=
  (∀ a : M, ¬IsIdempotent a) ∧ (∀ a c : M, a * c ≠ a)

/-- Элемент `a` обладает «бесконечным течением», если множество его правой
    достижимости не схлопывается в одноточечное `{a}`: действие, начатое из
    `a`, не возвращается немедленно к `a`. -/
def IsInfiniteFlow (M : Type u) [Monoid M] (a : M) : Prop := reach a ≠ {a}

/-! ### §2. Кэли овеществляет любое «чистое действие» -/

/-- **Теорема Кэли убивает «начало».** Любой моноид `M` (в том числе всякая
    предполагаемая структура «чистого действия») вкладывается инъективным
    моноидным морфизмом в моноид преобразований `Transform M`.

    Философский смысл: представление Кэли работает для ЛЮБОГО моноида, поэтому
    структуры «чистого действия» всё равно овеществляются в объекты. Гипотеза
    `h` намеренно не используется — в этом и состоит суть утверждения. -/
theorem cayley_kills_beginning : IsBeginningStructure M →
    ∃ f : MonoidMorphism M (Transform M), Function.Injective f.toFun :=
  fun _ => cayley_embedding

/-! ### §3. Конечность порождает идемпотент -/

/-- **В конечном моноиде достижимость всякого элемента содержит идемпотент.**
    Рассматривая степени `a, a², a³, …`, по принципу Дирихле получаем
    периодичность, откуда некоторая положительная степень `aⁿ` идемпотентна;
    будучи правым кратным `a`, она лежит в `reach a`. -/
theorem finite_forces_idempotent [Fintype M] (a : M) :
    ∃ e : M, IsIdempotent e ∧ e ∈ reach a := by
  obtain ⟨n, hn, hidem⟩ := exists_idempotent_pow a
  refine ⟨a ^ n, hidem, ?_⟩
  -- `a ^ n ∈ reach a` означает `algLe a (a ^ n)`, т.е. `∃ c, a * c = a ^ n`.
  show algLe a (a ^ n)
  refine ⟨a ^ (n - 1), ?_⟩
  have hn1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  calc a * a ^ (n - 1) = a ^ (n - 1 + 1) := (pow_succ' a (n - 1)).symm
    _ = a ^ n := by rw [hn1]

/-! ### §4. Невозможность «начала» в конечном случае -/

/-- **Невозможность структуры «чистого начала» в конечном моноиде.**
    Прямое следствие `finite_forces_idempotent`, применённого к единице:
    полученный идемпотент противоречит первому конъюнкту
    `IsBeginningStructure` (отсутствию идемпотентов). -/
theorem finite_beginning_impossible [Fintype M] : ¬IsBeginningStructure M := by
  intro h
  obtain ⟨e, he, _⟩ := finite_forces_idempotent (1 : M)
  exact h.1 e he

/-! ### §5. У «начала» нет локальной единицы -/

/-- **У структуры «чистого начала» нет локальной единицы.** Не существует
    идемпотента `e`, в локальный моноид `eMe e` которого попадал бы `a`,
    поскольку само существование идемпотента `e` противоречит первому
    конъюнкту `IsBeginningStructure`. -/
theorem no_beginning_has_local_unit (h : IsBeginningStructure M) (a : M) :
    ¬∃ e, IsIdempotent e ∧ a ∈ UAM_Submonoid.eMe e := by
  rintro ⟨e, he, -⟩
  exact h.1 e he

/-! ### §6. Бесконечное течение не схлопывается -/

/-- Исходная формулировка `infinite_flow_implies_no_idempotent_reach`,
    а именно `¬∃ e, IsIdempotent e ∧ (e ∈ reach a → e ∈ reach a)`, вырождена:
    условие `e ∈ reach a → e ∈ reach a` тождественно истинно, а единица `1`
    всегда идемпотентна, поэтому исходное экзистенциальное высказывание всегда
    верно, а его отрицание — всегда ложно.

    Ниже дана содержательная и истинная версия того же намерения: если у `a`
    «бесконечное течение» (`reach a ≠ {a}`), то в `reach a` действительно есть
    элемент, строго отличный от `a`, — течение не «оседает» немедленно на `a`. -/
theorem infinite_flow_implies_no_idempotent_reach {a : M}
    (ha : IsInfiniteFlow M a) : ∃ b, b ∈ reach a ∧ b ≠ a := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ b, b ∈ reach a → b = a`, откуда `reach a = {a}` — противоречие.
  apply ha
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · show algLe a a
    exact ⟨1, mul_one a⟩
  · intro x hx
    exact hcon x hx

/-! ### §7. Монотонность достижимости -/

/-- **Монотонность достижимости.** Если `b` достижимо из `a` (`algLe a b`),
    то всё достижимое из `b` достижимо и из `a`: `reach b ⊆ reach a`. -/
theorem reach_monotone {a b : M} (h : algLe a b) : reach b ⊆ reach a := by
  intro d hd
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := hd
  show algLe a d
  refine ⟨c * c', ?_⟩
  rw [← mul_assoc, hc, hc']

end UAM_Beginning
