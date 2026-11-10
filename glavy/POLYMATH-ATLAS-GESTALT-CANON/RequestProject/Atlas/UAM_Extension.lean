import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import RequestProject.Atlas.UAM_Directionality   -- algLe
import RequestProject.Atlas.UAM_Idempotent       -- IsIdempotent
import RequestProject.Atlas.UAM_Regular           -- IsRegular, IsZero
import RequestProject.Atlas.UAM_Ideal            -- IsIdeal, reesCongruence, principalIdeal
import RequestProject.Atlas.UAM_Congruence       -- IsCongruence, QuotientMonoid
import RequestProject.Atlas.UAM_Morphism         -- MonoidMorphism, kernel, range

/-!
# UAM — Layer 10: Расширения полугрупп (Extension)

Расширение полугруппы `N` идеалом моноида `M` — вложение `N` как двустороннего
идеала `I ⊆ M`. Простейший пример — Rees-фактор по идеалу (Layer 7).
Устанавливается связь ядра канонической проекции `M → M/I` с Rees-конгруэнцией.
-/

namespace UAM_Extension
universe u

open UAM_Directionality UAM_Idempotent UAM_Regular UAM_Ideal UAM_Congruence UAM_Morphism

variable {M N : Type u} [Monoid M] [Monoid N]

/-! ### §0. Собственные определения -/

/-- Расширение `N` идеалом в `M`: морфизм `N → M`, образ которого лежит
    в двустороннем идеале `I ⊆ M`. -/
structure IsExtension (M N : Type u) [Monoid M] [Monoid N] where
  ideal : Set M
  isIdeal : UAM_Ideal.IsIdeal ideal
  embedding : MonoidMorphism N M
  embed_into_ideal : ∀ n : N, embedding.toFun n ∈ ideal

/-! ### §1. Свойства расширений -/

/-- Идеал расширения непуст. -/
theorem extension_ideal_nonempty (E : IsExtension M N) : E.ideal.Nonempty :=
  E.isIdeal.nonempty

/-- Образ любого элемента `N` лежит в идеале расширения. -/
theorem extension_embedding_mem (E : IsExtension M N) (n : N) :
    E.embedding.toFun n ∈ E.ideal :=
  E.embed_into_ideal n

/-- Идеал расширения поглощает образ `N` с обеих сторон. -/
theorem extension_ideal_absorbs_image (E : IsExtension M N) (n : N) (m : M) :
    m * E.embedding.toFun n ∈ E.ideal ∧ E.embedding.toFun n * m ∈ E.ideal :=
  ⟨E.isIdeal.left_absorb m _ (E.embed_into_ideal n),
   E.isIdeal.right_absorb m _ (E.embed_into_ideal n)⟩

/-- В Rees-факторе `M/I` все образы элементов `N` попадают в один класс. -/
theorem extension_comp_constant (E : IsExtension M N) (n₁ n₂ : N) :
    (QuotientMonoid.mk (E.embedding.toFun n₁) :
      QuotientMonoid (reesCongruence E.ideal E.isIdeal)) =
    QuotientMonoid.mk (E.embedding.toFun n₂) :=
  QuotientMonoid.mk_eq_iff.mpr
    (reesCongruence_ideal_class E.isIdeal (E.embed_into_ideal n₁) (E.embed_into_ideal n₂))

/-- В Rees-факторе класс элемента идеала поглощает правое умножение. -/
theorem rees_factor_zero_class (I : Set M) (hI : UAM_Ideal.IsIdeal I)
    {a : M} (ha : a ∈ I) (b : M) :
    (QuotientMonoid.mk (a * b) : QuotientMonoid (reesCongruence I hI)) =
    QuotientMonoid.mk a :=
  QuotientMonoid.mk_eq_iff.mpr (reesCongruence_ideal_absorb hI ha)

/-- Тривиальное расширение: идеал — весь моноид, вложение — тождество. -/
def trivial_extension (M : Type u) [Monoid M] : IsExtension M M where
  ideal := Set.univ
  isIdeal :=
    { nonempty := ⟨1, Set.mem_univ 1⟩
      left_absorb := fun _ _ _ => Set.mem_univ _
      right_absorb := fun _ _ _ => Set.mem_univ _ }
  embedding := MonoidMorphism.idMorphism
  embed_into_ideal := fun _ => Set.mem_univ _

/-! ### §2. Сохранение свойств вложением -/

/-- Расширение сохраняет регулярность: образ регулярного элемента регулярен. -/
theorem extension_preserves_regular (E : IsExtension M N) {n : N}
    (hn : UAM_Regular.IsRegular n) : UAM_Regular.IsRegular (E.embedding.toFun n) :=
  MonoidMorphism.map_isRegular (f := E.embedding) hn

/-- Расширение сохраняет идемпотентность. -/
theorem extension_preserves_idempotent (E : IsExtension M N) {n : N}
    (hn : IsIdempotent n) : IsIdempotent (E.embedding.toFun n) :=
  MonoidMorphism.map_idempotent (f := E.embedding) hn

/-! ### §3. Идеал как расширение и связь ядра с Rees-конгруэнцией -/

/-- Любой морфизм `f : N → M` с образом в идеале `I` задаёт расширение. -/
def ideal_image_in_ideal {I : Set M} (hI : UAM_Ideal.IsIdeal I)
    (f : MonoidMorphism N M) (hf : ∀ n, f.toFun n ∈ I) :
    IsExtension M N where
  ideal := I
  isIdeal := hI
  embedding := f
  embed_into_ideal := hf

/-- Ядро канонической проекции `M → M/I` совпадает с Rees-конгруэнцией по `I`. -/
theorem rees_quotient_kernel (I : Set M) (hI : UAM_Ideal.IsIdeal I) (a b : M) :
    (QuotientMonoid.mk a : QuotientMonoid (reesCongruence I hI)) =
      QuotientMonoid.mk b ↔
    (reesCongruence I hI).r a b :=
  QuotientMonoid.mk_eq_iff

end UAM_Extension
