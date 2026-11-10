/-
# OSA-4.0 — WitnessGenerator: реестр свидетелей, его ацикличность и завершаемость

Запрос аудита:

* «проверь зависимости: witness не зависит от себя»;
* «проверь завершаемость: `generateWitnesses` терминирует».

Каждый закон ядра подтверждается **свидетелем** — доказанным утверждением
проекта.  Свидетели не независимы: обоснование одного опирается на другое
(например, LAW-012 в форме `law012_wp_sound` получается из точной
характеризации WP `eval_exec_eq_eval_wp`).  Реестр `witnessTable` фиксирует
эти зависимости вместе с рангом (номером слоя) свидетеля.

Доказано:

* реестр корректен (`witnessTable_wf`): каждая зависимость есть в реестре и
  строго меньшего ранга; имена свидетелей уникальны (`witnessTable_nodup`);
* **никакой свидетель не зависит от себя** — ни прямо (`no_self_dependency`),
  ни через цепочку любой длины (`witness_acyclic`); это доказано в общем виде
  для любого корректного реестра;
* **генератор завершается**: разрешение зависимостей `resolve` с топливом
  `maxRank + 1` никогда не исчерпывает топливо (`resolve_terminates`), а
  стратифицированный генератор `generateWitnesses` выдаёт каждое имя реестра
  ровно один раз, причём зависимости стоят строго раньше зависящего от них
  свидетеля (`generateWitnesses_deps_precede`).

Все перечисленные в реестре имена — реально существующие доказанные
утверждения проекта; это проверяется компилятором в `witnessNames_exist`.
-/
import RequestProject.OSA4.Audit.Bridges
import RequestProject.OSA4.Basis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Polymath.OSA4

/-! ## Реестр свидетелей -/

/-- Узел реестра свидетелей: имя доказанного утверждения, подтверждаемый закон,
ранг (номер слоя) и имена свидетелей, на которые опирается обоснование. -/
structure WitnessNode where
  /-- Имя доказанного утверждения проекта. -/
  name : String
  /-- Закон, который подтверждает свидетель. -/
  law : LawId
  /-- Номер слоя: свидетель опирается только на свидетелей меньшего ранга. -/
  rank : ℕ
  /-- Свидетели, на которые опирается обоснование. -/
  deps : List String
  deriving DecidableEq, Repr, Inhabited

/-- Реестр свидетелей ядра OSA-4.0. -/
def witnessTable : List WitnessNode :=
  [ ⟨"TypeLattice.isSubtype_refl", .LAW_001, 0, []⟩,
    ⟨"TypeLattice.isSubtype_trans", .LAW_002, 0, []⟩,
    ⟨"factStatus_exec_untouched", .LAW_003, 0, []⟩,
    ⟨"varValue_exec_untouched", .LAW_003, 0, []⟩,
    ⟨"law004_no_resurrection", .LAW_004, 0, []⟩,
    ⟨"law005_consume_iff_available", .LAW_005, 0, []⟩,
    ⟨"factStatus_exec_kill", .LAW_006, 0, []⟩,
    ⟨"EffectLevel.aggregate_append", .LAW_008, 0, []⟩,
    ⟨"law009_no_overclaim", .LAW_009, 0, []⟩,
    ⟨"law010_composition_sound", .LAW_010, 0, []⟩,
    ⟨"law011_exec_implies_authorized", .LAW_011, 0, []⟩,
    ⟨"eval_exec_eq_eval_wp", .LAW_012, 0, []⟩,
    ⟨"Belief.join_comm", .LAW_013, 0, []⟩,
    ⟨"Belief.join_assoc", .LAW_014, 0, []⟩,
    ⟨"Belief.join_idem", .LAW_015, 0, []⟩,
    ⟨"law016_recreate_new_id", .LAW_016, 0, []⟩,
    ⟨"law018_repair_sound", .LAW_018, 0, []⟩,
    ⟨"law006_kill_live_fact", .LAW_006, 1, ["factStatus_exec_kill"]⟩,
    ⟨"law017_invalidate_not_refute", .LAW_017, 1, ["factStatus_exec_kill"]⟩,
    ⟨"law012_wp_sound", .LAW_012, 1, ["eval_exec_eq_eval_wp"]⟩,
    ⟨"torture_T12_double_consume", .LAW_005, 1, ["law005_consume_iff_available"]⟩,
    ⟨"recreate_keeps_old_destroyed", .LAW_016, 1, ["law016_recreate_new_id"]⟩,
    ⟨"basis_law002_positive", .LAW_002, 1, ["TypeLattice.isSubtype_trans"]⟩,
    ⟨"pass_no_liveness_violation", .LAW_007, 1, []⟩,
    ⟨"consume_kills_fact", .LAW_005, 2,
      ["law006_kill_live_fact", "law017_invalidate_not_refute"]⟩,
    ⟨"pass_chain_executable", .LAW_007, 2,
      ["pass_no_liveness_violation", "law012_wp_sound"]⟩,
    ⟨"lawbook_holds", .LAW_007, 2,
      ["TypeLattice.isSubtype_refl", "TypeLattice.isSubtype_trans",
       "factStatus_exec_untouched", "varValue_exec_untouched",
       "law004_no_resurrection", "law005_consume_iff_available",
       "law006_kill_live_fact", "pass_no_liveness_violation",
       "EffectLevel.aggregate_append", "law009_no_overclaim",
       "law010_composition_sound", "law011_exec_implies_authorized",
       "law012_wp_sound", "Belief.join_comm", "Belief.join_assoc",
       "Belief.join_idem", "law016_recreate_new_id",
       "law017_invalidate_not_refute", "law018_repair_sound"]⟩,
    ⟨"bridge4_lawbook_compiler", .LAW_007, 3, ["pass_chain_executable"]⟩ ]

/-- Все имена реестра — существующие доказанные утверждения проекта: их
существование проверяется компилятором при элаборации этого утверждения. -/
theorem witnessNames_exist : True := by
  have _ := @TypeLattice.isSubtype_refl
  have _ := @TypeLattice.isSubtype_trans
  have _ := @factStatus_exec_untouched
  have _ := @varValue_exec_untouched
  have _ := @law004_no_resurrection
  have _ := @law005_consume_iff_available
  have _ := @factStatus_exec_kill
  have _ := @EffectLevel.aggregate_append
  have _ := @law009_no_overclaim
  have _ := @law010_composition_sound
  have _ := @law011_exec_implies_authorized
  have _ := @eval_exec_eq_eval_wp
  have _ := @Belief.join_comm
  have _ := @Belief.join_assoc
  have _ := @Belief.join_idem
  have _ := @law016_recreate_new_id
  have _ := @law018_repair_sound
  have _ := @law006_kill_live_fact
  have _ := @law017_invalidate_not_refute
  have _ := @law012_wp_sound
  have _ := @torture_T12_double_consume
  have _ := @recreate_keeps_old_destroyed
  have _ := @basis_law002_positive
  have _ := @pass_no_liveness_violation
  have _ := @consume_kills_fact
  have _ := @pass_chain_executable
  have _ := @lawbook_holds
  have _ := @bridge4_lawbook_compiler
  trivial

/-! ## Корректность реестра -/

/-- Поиск узла по имени. -/
def lookupNode (table : List WitnessNode) (s : String) : Option WitnessNode :=
  table.find? (fun n => n.name == s)

/-- Ранг свидетеля по имени (для имени вне реестра — 0). -/
def rankOf (table : List WitnessNode) (s : String) : ℕ :=
  match lookupNode table s with
  | some n => n.rank
  | none => 0

/-- Корректность реестра: каждая зависимость объявлена в реестре и имеет
строго меньший ранг. -/
def WFTable (table : List WitnessNode) : Prop :=
  ∀ n ∈ table, ∀ d ∈ n.deps, ∃ m ∈ table, m.name = d ∧ m.rank < n.rank

instance (table : List WitnessNode) : Decidable (WFTable table) := by
  unfold WFTable; infer_instance

/-- Имена свидетелей уникальны. -/
theorem witnessTable_nodup : (witnessTable.map WitnessNode.name).Nodup := by
  decide

/-- **Реестр свидетелей корректен.** -/
theorem witnessTable_wf : WFTable witnessTable := by decide

/-- При уникальных именах поиск находит именно тот узел, который в реестре. -/
theorem lookupNode_eq_of_mem {table : List WitnessNode}
    (huniq : (table.map WitnessNode.name).Nodup) {n : WitnessNode} (hn : n ∈ table) :
    lookupNode table n.name = some n := by
  induction table with
  | nil => exact absurd hn (by simp)
  | cons a t ih =>
      rw [List.map_cons, List.nodup_cons] at huniq
      rcases List.mem_cons.mp hn with rfl | ht
      · simp [lookupNode]
      · have hne : ¬ (a.name = n.name) := fun h => huniq.1 (h ▸ List.mem_map_of_mem ht)
        rw [lookupNode, List.find?_cons_of_neg (by simpa using hne)]
        exact ih huniq.2 ht

/-- Ранг узла реестра совпадает с рангом его имени. -/
theorem rankOf_eq {table : List WitnessNode} (huniq : (table.map WitnessNode.name).Nodup)
    {n : WitnessNode} (hn : n ∈ table) : rankOf table n.name = n.rank := by
  rw [rankOf, lookupNode_eq_of_mem huniq hn]

/-! ## Зависимости: отсутствие самозависимости и ацикличность -/

/-- Свидетель `a` зависит от свидетеля `b`. -/
def Depends (table : List WitnessNode) (a b : String) : Prop :=
  ∃ n ∈ table, n.name = a ∧ b ∈ n.deps

/-- Вдоль зависимости ранг строго убывает. -/
theorem rankOf_lt_of_depends {table : List WitnessNode}
    (huniq : (table.map WitnessNode.name).Nodup) (hwf : WFTable table)
    {a b : String} (h : Depends table a b) : rankOf table b < rankOf table a := by
  obtain ⟨n, hn, rfl, hd⟩ := h
  obtain ⟨m, hm, hmn, hlt⟩ := hwf n hn _ hd
  have hb : rankOf table b = m.rank := by
    rw [← hmn]; exact rankOf_eq huniq hm
  have ha : rankOf table n.name = n.rank := rankOf_eq huniq hn
  omega

/-- **Свидетель не зависит от себя** (прямая зависимость). -/
theorem no_self_dependency {table : List WitnessNode}
    (huniq : (table.map WitnessNode.name).Nodup) (hwf : WFTable table)
    (a : String) : ¬ Depends table a a := by
  intro h
  have := rankOf_lt_of_depends huniq hwf h
  omega

/-- Вдоль цепочки зависимостей любой длины ранг строго убывает. -/
theorem rankOf_lt_of_transGen {table : List WitnessNode}
    (huniq : (table.map WitnessNode.name).Nodup) (hwf : WFTable table)
    {a b : String} (h : Relation.TransGen (Depends table) a b) :
    rankOf table b < rankOf table a := by
  induction h with
  | single hab => exact rankOf_lt_of_depends huniq hwf hab
  | tail _ hbc ih => exact lt_trans (rankOf_lt_of_depends huniq hwf hbc) ih

/-- **Граф зависимостей свидетелей ацикличен**: ни один свидетель не участвует
в собственном обосновании ни на каком расстоянии. -/
theorem witness_acyclic {table : List WitnessNode}
    (huniq : (table.map WitnessNode.name).Nodup) (hwf : WFTable table)
    (a : String) : ¬ Relation.TransGen (Depends table) a a := by
  intro h
  have := rankOf_lt_of_transGen huniq hwf h
  omega

/-- Реестр проекта: самозависимостей нет. -/
theorem witnessTable_no_self_dependency (a : String) : ¬ Depends witnessTable a a :=
  no_self_dependency witnessTable_nodup witnessTable_wf a

/-- Реестр проекта: граф зависимостей ацикличен. -/
theorem witnessTable_acyclic (a : String) :
    ¬ Relation.TransGen (Depends witnessTable) a a :=
  witness_acyclic witnessTable_nodup witnessTable_wf a

/-! ## Завершаемость разрешения зависимостей -/

/-- Сбор результатов по списку: `none`, если хотя бы один результат `none`. -/
def collect (f : String → Option (List String)) : List String → Option (List String)
  | [] => some []
  | d :: t =>
      match f d, collect f t with
      | some a, some b => some (a ++ b)
      | _, _ => none

/-- Если каждый элемент разрешается, разрешается и весь список. -/
theorem collect_isSome {f : String → Option (List String)} :
    ∀ l : List String, (∀ d ∈ l, (f d).isSome) → (collect f l).isSome := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons d t ih =>
      intro h
      have hd : (f d).isSome := h d (by simp)
      have ht : (collect f t).isSome := ih (fun x hx => h x (by simp [hx]))
      rw [collect]
      cases hf : f d with
      | none => rw [hf] at hd; exact absurd hd (by simp)
      | some a =>
          cases hc : collect f t with
          | none => rw [hc] at ht; exact absurd ht (by simp)
          | some b => rfl

/-- Разрешение зависимостей свидетеля с ограниченным «топливом»:
`none` означает, что топливо исчерпано (что было бы признаком цикла). -/
def resolve (table : List WitnessNode) : ℕ → String → Option (List String)
  | 0, _ => none
  | k + 1, s =>
      match lookupNode table s with
      | none => some [s]
      | some n => (collect (resolve table k) n.deps).map (fun l => l ++ [s])

/-- **Завершаемость (общий случай).**  Для корректного реестра разрешение
зависимостей никогда не исчерпывает топливо, если топлива больше ранга
свидетеля. -/
theorem resolve_isSome_of_rank_lt {table : List WitnessNode}
    (huniq : (table.map WitnessNode.name).Nodup) (hwf : WFTable table) :
    ∀ (k : ℕ) (s : String), rankOf table s < k → (resolve table k s).isSome := by
  intro k
  induction k with
  | zero => intro s h; omega
  | succ k ih =>
      intro s hs
      rw [resolve]
      cases hl : lookupNode table s with
      | none => simp
      | some n =>
          have hmem : n ∈ table := List.mem_of_find?_eq_some hl
          have hname : n.name = s := by
            have := List.find?_some hl
            simpa using this
          have hrank : rankOf table s = n.rank := by rw [rankOf, hl]
          have hdeps : ∀ d ∈ n.deps, (resolve table k d).isSome := by
            intro d hd
            obtain ⟨m, hm, hmn, hlt⟩ := hwf n hmem d hd
            have : rankOf table d = m.rank := by rw [← hmn]; exact rankOf_eq huniq hm
            exact ih d (by omega)
          have hcol := collect_isSome (f := resolve table k) n.deps hdeps
          cases hc : collect (resolve table k) n.deps with
          | none => rw [hc] at hcol; simp at hcol
          | some l => simp [hc]

/-- Наибольший ранг реестра. -/
def maxRank (table : List WitnessNode) : ℕ := table.foldl (fun m n => max m n.rank) 0

private theorem le_foldl_max : ∀ (l : List WitnessNode) (x : ℕ),
    x ≤ l.foldl (fun m n => max m n.rank) x := by
  intro l
  induction l with
  | nil => intro x; exact le_rfl
  | cons a t ih =>
      intro x
      simp only [List.foldl_cons]
      exact le_trans (le_max_left x a.rank) (ih (max x a.rank))

private theorem rank_le_foldl_max : ∀ (l : List WitnessNode) (x : ℕ) (n : WitnessNode),
    n ∈ l → n.rank ≤ l.foldl (fun m n => max m n.rank) x := by
  intro l
  induction l with
  | nil => intro x n hn; exact absurd hn (by simp)
  | cons a t ih =>
      intro x n hn
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hn with rfl | ht
      · exact le_trans (le_max_right x n.rank) (le_foldl_max t (max x n.rank))
      · exact ih _ n ht

/-- Ранг любого узла не превосходит `maxRank`. -/
theorem rank_le_maxRank {table : List WitnessNode} {n : WitnessNode} (hn : n ∈ table) :
    n.rank ≤ maxRank table :=
  rank_le_foldl_max table 0 n hn

/-- **Завершаемость генератора для реестра проекта.**  Разрешение зависимостей
любого свидетеля завершается при топливе `maxRank + 1`. -/
theorem resolve_terminates (n : WitnessNode) (hn : n ∈ witnessTable) :
    (resolve witnessTable (maxRank witnessTable + 1) n.name).isSome := by
  refine resolve_isSome_of_rank_lt witnessTable_nodup witnessTable_wf _ _ ?_
  rw [rankOf_eq witnessTable_nodup hn]
  have := rank_le_maxRank hn
  omega

/-! ## Стратифицированный генератор -/

/-- Имена свидетелей ранга `k`. -/
def levelOf (table : List WitnessNode) (k : ℕ) : List String :=
  (table.filter (fun n => n.rank == k)).map WitnessNode.name

/-- **Генератор свидетелей**: имена, перечисленные по слоям возрастающего
ранга.  Функция тотальна по построению (рекурсии нет — только перебор
конечного диапазона рангов). -/
def generateWitnesses (table : List WitnessNode) : List String :=
  (List.range (maxRank table + 1)).flatMap (levelOf table)

/-- Генератор выдаёт каждое имя реестра. -/
theorem generateWitnesses_complete {table : List WitnessNode} {n : WitnessNode}
    (hn : n ∈ table) : n.name ∈ generateWitnesses table := by
  rw [generateWitnesses, List.mem_flatMap]
  refine ⟨n.rank, ?_, ?_⟩
  · rw [List.mem_range]
    have := rank_le_maxRank hn
    omega
  · rw [levelOf, List.mem_map]
    exact ⟨n, List.mem_filter.mpr ⟨hn, by simp⟩, rfl⟩

/-- Генератор не выдумывает имён. -/
theorem generateWitnesses_sound {table : List WitnessNode} {s : String}
    (hs : s ∈ generateWitnesses table) : ∃ n ∈ table, n.name = s := by
  rw [generateWitnesses, List.mem_flatMap] at hs
  obtain ⟨k, _, hk⟩ := hs
  rw [levelOf, List.mem_map] at hk
  obtain ⟨n, hn, rfl⟩ := hk
  exact ⟨n, (List.mem_filter.mp hn).1, rfl⟩

/-- Для реестра проекта генератор выдаёт ровно 28 имён, без повторов. -/
theorem generateWitnesses_nodup :
    (generateWitnesses witnessTable).length = 28 ∧
    (generateWitnesses witnessTable).Nodup ∧
    (generateWitnesses witnessTable).length = witnessTable.length := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Зависимости предшествуют**: в выданном порядке каждый свидетель стоит
строго позже всех своих зависимостей — порядок пригоден для последовательной
проверки. -/
theorem generateWitnesses_deps_precede :
    ∀ n ∈ witnessTable, ∀ d ∈ n.deps,
      (generateWitnesses witnessTable).idxOf d <
        (generateWitnesses witnessTable).idxOf n.name := by
  decide

end Polymath.OSA4
