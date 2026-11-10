import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_Beginning
import RequestProject.Atlas.UAM_AutomatonStops
import RequestProject.Atlas.UAM_InfiniteBeginning
import RequestProject.Atlas.UAM_Cayley
import RequestProject.Atlas.UAM_Morphism
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_FiniteSemigroup

/-!
# UAM — Тезис

Этот файл завершает весь ход рассуждения четырьмя связанными утверждениями.
Конечный моноид не может быть «чистым началом»: конечность неизбежно даёт
идемпотент, поэтому отсутствие всякой остановки несовместимо с конечностью.
Первые два пункта выражают две стороны одного препятствия — невозможность
начала и положительное существование точки оседания.

Обратное ограничение неверно: бесконечность сама по себе не заставляет
действия оседать. Свободный моноид над непустым алфавитом служит слабым
началом — его единственный идемпотент есть пустое слово, тогда как всякое
действительное, непустое слово не идемпотентно.

Однако этот выход остаётся частичным. Теорема Кэли не требует ни конечности,
ни идемпотентов, ни какой-либо готовности моноида к «овеществлению»: всякий
моноид безусловно вкладывается в моноид преобразований своего носителя.
Таким образом, свободное действие избегает нетривиального внутреннего
оседания, но всё равно становится объектом представления.

Во втором пункте утверждается существование идемпотента без требования
`e ≠ 1`. Более сильная формулировка ложна даже для конечных нетривиальных
моноидов: в любой нетривиальной конечной группе единственный идемпотент —
единица. Именно данная формулировка является точным общим утверждением для
всех конечных моноидов.
-/

namespace UAM_Thesis

/--
**Итоговый тезис.** Конечность исключает чистое начало и порождает
идемпотент; свободный моноид реализует слабое бесконечное начало; при этом
представление Кэли безусловно превращает действия любого моноида в
преобразования.
-/
theorem thesis :
    -- Утверждение 1: конечный моноид не может быть чистым началом.
    (∀ (M : Type) [Monoid M] [Fintype M],
        ¬ UAM_Beginning.IsBeginningStructure M) ∧
    -- Утверждение 2: всякий конечный моноид содержит идемпотент.
    (∀ (M : Type) [Monoid M] [Fintype M],
        ∃ e : M, UAM_Idempotent.IsIdempotent e) ∧
    -- Утверждение 3: свободный моноид над непустым алфавитом — слабое начало.
    (∀ (α : Type) [Nonempty α],
        UAM_InfiniteBeginning.IsWeakBeginningStructure (UAM_Free.FreeMonoid α)) ∧
    -- Утверждение 4: Кэли безусловно овеществляет любой моноид.
    (∀ (M : Type) [Monoid M],
        ∃ f : UAM_Morphism.MonoidMorphism M (UAM_Cayley.Transform M),
          Function.Injective f.toFun) := by
  constructor
  · intro M monoid_M fintype_M
    exact UAM_Beginning.finite_beginning_impossible
  constructor
  · intro M monoid_M fintype_M
    exact UAM_FiniteSemigroup.exists_idempotent
  constructor
  · intro α nonempty_α
    exact UAM_InfiniteBeginning.free_monoid_weak_beginning
  · intro M monoid_M
    exact UAM_Cayley.cayley_embedding

end UAM_Thesis
