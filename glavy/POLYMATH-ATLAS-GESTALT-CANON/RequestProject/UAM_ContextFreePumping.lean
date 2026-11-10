/-
# UAM — накачка контекстно-свободных языков

Модуль формализует **механизм накачки** (pumping) для КС-грамматик:
самовложение нетерминала порождает бесконечное семейство слов языка.

Что доказано:

* `SelfEmbedding g A u v` — нетерминал `A` выводит `u · A · v`;
* `selfEmbedding_of_rule` — достаточное условие: правило вида
  `A → δ₁ A δ₂`, где `δ₁` выводит `u`, а `δ₂` выводит `v`;
* `pump` — накачка на уровне нетерминала: `A ⇒* uⁿ x vⁿ` для всех `n`;
* `pump_language` — накачка внутри контекста: если из старта выводится
  `p · A · s`, то все слова `p uⁿ x vⁿ s` принадлежат языку;
* `language_infinite_of_selfEmbedding` — при `u ++ v ≠ []` язык бесконечен;
* пример: язык `aⁿbⁿ` бесконечен по этому механизму.

**Граница результата (документируется честно).**  Здесь доказана *достаточная*
половина леммы о накачке: наличие самовложения влечёт накачку и бесконечность.
Классическая лемма о накачке содержит и вторую половину — что всякое
достаточно длинное слово КС-языка обязательно порождается через самовложение;
она требует нормальной формы Хомского и оценки высоты дерева вывода и в этом
модуле **не** доказана.
-/
import RequestProject.UAM_ContextFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UAM.ContextFree

universe u

variable {N T : Type u}

/-! ## Повторение слова -/

/-- Слово `u`, повторённое `n` раз. -/
def rep (u : List T) : ℕ → List T
  | 0 => []
  | n + 1 => u ++ rep u n

@[simp] theorem rep_zero (u : List T) : rep u 0 = [] := rfl

@[simp] theorem rep_succ (u : List T) (n : ℕ) : rep u (n + 1) = u ++ rep u n := rfl

theorem rep_succ' (u : List T) (n : ℕ) : rep u (n + 1) = rep u n ++ u := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc rep u (n + 2) = u ++ rep u (n + 1) := rfl
        _ = u ++ (rep u n ++ u) := by rw [ih]
        _ = (u ++ rep u n) ++ u := by rw [List.append_assoc]
        _ = rep u (n + 1) ++ u := rfl

@[simp] theorem length_rep (u : List T) (n : ℕ) : (rep u n).length = n * u.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-! ## Самовложение нетерминала -/

/-- **Самовложение.**  Нетерминал `A` выводит `u · A · v`: всякий вывод из `A`
можно обернуть в контекст `(u, v)`. -/
def SelfEmbedding (g : Grammar N T) (A : N) (u v : List T) : Prop :=
  ∀ x, Yields g [Sum.inl A] x → Yields g [Sum.inl A] (u ++ x ++ v)

/-- Достаточное условие самовложения: правило `A → δ₁ A δ₂`, где `δ₁` выводит
`u`, а `δ₂` выводит `v`. -/
theorem selfEmbedding_of_rule (g : Grammar N T) {A : N} {d₁ d₂ : List (N ⊕ T)}
    {u v : List T} (hr : g.rule A (d₁ ++ Sum.inl A :: d₂))
    (h₁ : Yields g d₁ u) (h₂ : Yields g d₂ v) :
    SelfEmbedding g A u v := by
  intro x hx
  have hmid : Yields g (Sum.inl A :: d₂) (x ++ v) := by
    simpa using Yields.append hx h₂
  have hbody : Yields g (d₁ ++ Sum.inl A :: d₂) (u ++ (x ++ v)) :=
    Yields.append h₁ hmid
  have := Yields.nonterm (g := g) (A := A) (α := []) hr hbody Yields.nil
  simpa [List.append_assoc] using this

/-! ## Накачка -/

/-- **Накачка на уровне нетерминала.**  Если `A` самовложен с контекстом
`(u, v)` и выводит `x`, то он выводит `uⁿ x vⁿ` для всякого `n`. -/
theorem pump {g : Grammar N T} {A : N} {u v x : List T}
    (h : SelfEmbedding g A u v) (hx : Yields g [Sum.inl A] x) :
    ∀ n, Yields g [Sum.inl A] (rep u n ++ x ++ rep v n) := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have hwrap := h _ ih
      rw [rep_succ u n, rep_succ' v n]
      simpa [List.append_assoc] using hwrap

/-- **Накачка внутри контекста.**  Если из стартового нетерминала выводится
форма `p · A · s` (в смысле гипотезы `hctx`), то накачанные слова
`p uⁿ x vⁿ s` принадлежат языку. -/
theorem pump_language {g : Grammar N T} {A : N} {u v x p s : List T}
    (hctx : ∀ y, Yields g [Sum.inl A] y → (p ++ y ++ s) ∈ g.language)
    (h : SelfEmbedding g A u v) (hx : Yields g [Sum.inl A] x) (n : ℕ) :
    (p ++ (rep u n ++ x ++ rep v n) ++ s) ∈ g.language :=
  hctx _ (pump h hx n)

/-! ## Бесконечность языка -/

/-- Длина накачанного слова строго растёт, если контекст непуст. -/
theorem length_pumped {u v x p s : List T} (n : ℕ) :
    (p ++ (rep u n ++ x ++ rep v n) ++ s).length =
      p.length + (n * u.length + x.length + n * v.length) + s.length := by
  simp only [List.length_append, length_rep]

/-- **Бесконечность языка при самовложении.**  Если нетерминал `A` самовложен
с непустым контекстом, выводит хотя бы одно слово и встречается в выводимой из
старта форме, то язык грамматики бесконечен. -/
theorem language_infinite_of_selfEmbedding {g : Grammar N T} {A : N} {u v x p s : List T}
    (hctx : ∀ y, Yields g [Sum.inl A] y → (p ++ y ++ s) ∈ g.language)
    (h : SelfEmbedding g A u v) (hx : Yields g [Sum.inl A] x)
    (hne : u ++ v ≠ []) :
    g.language.Infinite := by
  have hlen0 : (u ++ v).length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
  have hpos : 0 < u.length + v.length := by
    simpa [List.length_append] using Nat.pos_of_ne_zero hlen0
  set f : ℕ → List T := fun n => p ++ (rep u n ++ x ++ rep v n) ++ s with hf
  have hmem : ∀ n, f n ∈ g.language := fun n => pump_language hctx h hx n
  have hlen : ∀ n, (f n).length = p.length + (n * u.length + x.length + n * v.length)
      + s.length := fun n => length_pumped n
  have hinj : Function.Injective f := by
    intro m n hmn
    have := congrArg List.length hmn
    rw [hlen m, hlen n] at this
    have hmul : m * (u.length + v.length) = n * (u.length + v.length) := by
      have h1 : m * u.length + m * v.length = n * u.length + n * v.length := by omega
      simpa [Nat.mul_add] using h1
    exact Nat.eq_of_mul_eq_mul_right hpos hmul
  exact Set.infinite_of_injective_forall_mem hinj hmem

/-! ## Пример: язык `aⁿbⁿ` бесконечен -/

/-- Стартовый нетерминал грамматики `aⁿbⁿ` самовложен с контекстом
`([a], [b])`. -/
theorem anbn_selfEmbedding : SelfEmbedding anbn () [AB.a] [AB.b] := by
  refine selfEmbedding_of_rule anbn (d₁ := [Sum.inr AB.a]) (d₂ := [Sum.inr AB.b])
    (Or.inr rfl) ?_ ?_
  · simpa using Yields.term (g := anbn) (a := AB.a) Yields.nil
  · simpa using Yields.term (g := anbn) (a := AB.b) Yields.nil

/-- Пустое слово выводится грамматикой `aⁿbⁿ`. -/
theorem anbn_yields_nil : Yields anbn [Sum.inl ()] ([] : List AB) := by
  simpa using Yields.nonterm (g := anbn) (A := ()) (α := []) (Or.inl rfl) Yields.nil Yields.nil

/-- **Язык `aⁿbⁿ` бесконечен** — по механизму накачки, а не перечислением. -/
theorem anbn_language_infinite : anbn.language.Infinite := by
  refine language_infinite_of_selfEmbedding (p := []) (s := [])
    (fun y hy => ?_) anbn_selfEmbedding anbn_yields_nil (by simp)
  simpa [Grammar.language] using hy

end UAM.ContextFree
