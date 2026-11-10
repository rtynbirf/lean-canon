import RequestProject.Atlas.Canon.Correspondence
import RequestProject.Atlas.Bridges.CanonUAM
import RequestProject.Atlas.Bridges.ApostleUAM
import RequestProject.Atlas.Bridges.CanonApostle
import RequestProject.Atlas.Bridges.CanonRSIA
import RequestProject.Atlas.Bridges.ApostleRSIA
import RequestProject.Atlas.Bridges.CanonL0L42
import RequestProject.Atlas.Arithmetic_Rice

/-!
# Реестр связей между проектами

`Canon/Correspondence.lean` задаёт «шов» как пустое множество: связь, которая
ничего не содержит. Этот файл ничего в нём не меняет и не опровергает — он
добавляет второй, непустой слой: реестр уже доказанных связей.

Реестр устроен так, что его нельзя заполнить незаслуженно: каждая запись
`Bridge` несёт не только имена двух проектов, но и само утверждение вместе
с его доказательством. Список `bridges` поэтому проверяется системой типов:
если утверждение не доказано, запись не существует.

* `Bridge` — запись реестра: пара проектов, утверждение и его доказательство;
* `bridges` — все установленные связи;
* `bridges_endpoints_are_projects` — концы каждой связи принадлежат списку
  проектов;
* `bridged` — отношение «между проектами есть доказанная связь»;
* `canon_uam_bridged`, `canon_rsia_bridged`, `canon_apostle_bridged`,
  `apostle_uam_bridged`, `apostle_rsia_bridged`, `uam_idealai_bridged`,
  `l0l42_canon_bridged`, `l0l42_uam_bridged` — какие пары уже связаны;
* `shore_empty_yet_bridges_exist` — шов остаётся пустым, но связи существуют:
  одно не отменяет другого.
-/

namespace Bridges.Links

open Bridges

/-- Запись реестра: связь между двумя проектами, её утверждение и
доказательство. Запись невозможно создать без доказательства. -/
structure Bridge where
  /-- Имя проекта-источника. -/
  source : String
  /-- Имя проекта-цели. -/
  target : String
  /-- Утверждение связи. -/
  claim : Prop
  /-- Доказательство утверждения. -/
  proof : claim

/-- Список проектов, дополненный конвейером апостолов и шкалой L0–L42. -/
def projects : List String :=
  Canon.Correspondence.projects ++ ["ApostlePipeline", "Канон L0–L42"]

/-- Все доказанные связи между проектами. -/
def bridges : List Bridge :=
  [ { source := "Канон Горизонтов"
      target := "UAM"
      claim := ∀ (n : Nat) (L : Layer n),
        (∀ w : UAM_Free.FreeMonoid Unit, (CanonUAM.shiftAction n).act w L ≈ L) ∧
        (∀ w : UAM_Free.FreeMonoid Unit, w ≠ [] →
          (CanonUAM.shiftAction n).act w L ≠ L)
      proof := fun _n L => CanonUAM.spiral_structural_not_literal L },
    { source := "Канон Горизонтов"
      target := "UAM"
      claim := CanonUAM.canonDFA.language =
        {w : UAM_Free.FreeMonoid Unit | w.length < canonicalShiftCount}
      proof := CanonUAM.canonDFA_language },
    { source := "Канон Горизонтов"
      target := "RSIA"
      claim := ∀ (n : Nat) (L : Layer n),
        ((shift^[canonicalShiftCount]) L ≠ L) ∧
        ((shift^[canonicalShiftCount]) L ≈ L) ∧
        CanonRSIA.toPhase ((shift^[canonicalShiftCount]) L) = CanonRSIA.toPhase L
      proof := fun _n L => CanonRSIA.spiral_projects_onto_ring L },
    { source := "Канон Горизонтов"
      target := "ApostlePipeline"
      claim := CanonApostle.apostleLayer.StrictlyOrdered ∧
        ¬ CanonApostle.apostleLayer.HasCanonicalArity
      proof := ⟨CanonApostle.apostleLayer_strictlyOrdered,
        CanonApostle.apostleLayer_lacks_canonical_arity⟩ },
    { source := "ApostlePipeline"
      target := "UAM"
      claim := ∀ p : ApostlePipeline.Params,
        ApostlePipeline.orderToJudas ∈ (ApostleUAM.pipelineDFA p).language ↔
          ApostlePipeline.reduced p ≤ p.capacity
      proof := ApostleUAM.judas_word_mem_language_iff },
    { source := "ApostlePipeline"
      target := "UAM"
      claim := ∀ p : ApostlePipeline.Params,
        ApostlePipeline.flow ∈ (ApostleUAM.pipelineDFA p).language
      proof := ApostleUAM.flow_mem_language },
    { source := "ApostlePipeline"
      target := "RSIA"
      claim := ApostleRSIA.toRSIA ApostlePipeline.Phase.paul =
          ApostleRSIA.toRSIA ApostlePipeline.Phase.peter ∧
        ApostlePipeline.Phase.paul ≠ ApostlePipeline.Phase.peter
      proof := ApostleRSIA.pipeline_spiral_not_cycle },
    { source := "UAM"
      target := "IdealAI"
      claim := ∀ (enumeration : Arithmetic_Rice.PartialComputableEnumeration)
          (property : ℕ → Prop),
          Arithmetic_Rice.ExtensionalProperty enumeration property →
          Arithmetic_Rice.SemanticallyNontrivial property →
          ¬ ∃ decider : ℕ → Bool,
            ∀ program, decider program = true ↔ property program
      proof := Arithmetic_Rice.rice_theorem },
    { source := "Канон L0–L42"
      target := "Канон Горизонтов"
      claim := shift CanonL0L42.scaleLayer ≈ CanonL0L42.scaleLayer ∧
        (shift CanonL0L42.scaleLayer).idx = CanonL0L42.scaleLayer.idx + 1 ∧
        ∀ i : Fin 43, ((shift CanonL0L42.scaleLayer).canons i).selfReferenceLevel =
          (CanonL0L42.scaleLayer.canons i).selfReferenceLevel + 1
      proof := CanonL0L42.exit_is_shift },
    { source := "Канон L0–L42"
      target := "UAM"
      claim := ∀ w : UAM_Free.FreeMonoid Unit, w ≠ [] →
        (CanonUAM.shiftAction 43).act w CanonL0L42.scaleLayer ≠ CanonL0L42.scaleLayer
      proof := CanonL0L42.exit_never_returns } ]

/-- Реестр непуст: связи есть. -/
theorem bridges_ne_nil : bridges ≠ [] := by
  simp [bridges]

/-- Концы каждой связи — имена из списка проектов. -/
theorem bridges_endpoints_are_projects :
    ∀ b ∈ bridges, b.source ∈ projects ∧ b.target ∈ projects := by
  intro b hb
  simp only [bridges, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact ⟨by decide, by decide⟩

/-- Между проектами `p` и `q` есть доказанная связь. -/
def bridged (p q : String) : Prop :=
  ∃ b ∈ bridges, b.source = p ∧ b.target = q

theorem canon_uam_bridged : bridged "Канон Горизонтов" "UAM" := by
  refine ⟨bridges[0], ?_, rfl, rfl⟩
  simp [bridges]

theorem canon_rsia_bridged : bridged "Канон Горизонтов" "RSIA" := by
  refine ⟨bridges[2], ?_, rfl, rfl⟩
  simp [bridges]

theorem canon_apostle_bridged : bridged "Канон Горизонтов" "ApostlePipeline" := by
  refine ⟨bridges[3], ?_, rfl, rfl⟩
  simp [bridges]

theorem apostle_uam_bridged : bridged "ApostlePipeline" "UAM" := by
  refine ⟨bridges[4], ?_, rfl, rfl⟩
  simp [bridges]

theorem apostle_rsia_bridged : bridged "ApostlePipeline" "RSIA" := by
  refine ⟨bridges[6], ?_, rfl, rfl⟩
  simp [bridges]

theorem uam_idealai_bridged : bridged "UAM" "IdealAI" := by
  refine ⟨bridges[7], ?_, rfl, rfl⟩
  simp [bridges]

theorem l0l42_canon_bridged : bridged "Канон L0–L42" "Канон Горизонтов" := by
  refine ⟨bridges[8], ?_, rfl, rfl⟩
  simp [bridges]

theorem l0l42_uam_bridged : bridged "Канон L0–L42" "UAM" := by
  refine ⟨bridges[9], ?_, rfl, rfl⟩
  simp [bridges]

/-- Шов из карты соответствия остаётся пустым множеством, и одновременно
реестр доказанных связей непуст: пустой шов не означает отсутствия связей. -/
theorem shore_empty_yet_bridges_exist :
    (∀ p q : String, Canon.Correspondence.shore p q = ∅) ∧ bridges ≠ [] :=
  ⟨fun _p _q => rfl, bridges_ne_nil⟩

end Bridges.Links
