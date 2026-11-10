/-
  Polymath Atlas v107.0 — Phenomenal Module
  Imperial Archive: Chapter X (Phenomenal Ground)
  
  Status: SPECIFIED (type definitions for phenomenal concepts)
  Evidence: tracked=true, specified=true, witness=false
  
  GAP STATUS: P0-02 (Phenomenal gap — requires phenomenological formalization)
  
  HONESTY STATEMENT:
    - Defines types for phenomenal experience (qualia, intentionality)
    - Does NOT reduce qualia to computation (anti-functionalist stance)
    - This is a TYPE SKELETON for future philosophical work
-/

import PolymathAtlas.Core

namespace PolyMath.Atlas

/-!
## §1. Phenomenal Types

Типы для феноменологических концептов.
-/

/-- Квалиа — качественный характер опыта -/
structure Qualia where
  id          : String
  name        : String   -- e.g., "redness", "pain", "sweetness"
  category    : String   -- sensory, emotional, cognitive
  describable : Bool     -- можно ли вербализовать?
  shared      : Bool     -- интерсубъективен?
  deriving Repr

/-- Интенциональность — направленность сознания на объект -/
structure Intentionality where
  object      : String   -- на что направлено
  mode        : String   -- восприятие, воображение, воспоминание
  fulfilled   : Bool     -- выполнена (по Гуссерлю)?
  evidence    : EvidenceVector
  deriving Repr

/-- Уровень феноменологического данности -/
inductive GivennessLevel : Type
  | Implicit     -- имплицитное (фон)
  | Horizonal    -- горизонтальное (возможное)
  | Explicit     -- эксплицитное (фокус внимания)
  | Constituted  -- конституированное (активно сформированное)
  deriving Repr, DecidableEq, Inhabited

/-!
## §2. Phenomenal Structure

Запись о феноменологическом наблюдении.
-/
structure PhenomenalObservation where
  id            : String
  observer      : String   -- кто наблюдает (идентификатор)
  qualia        : List Qualia
  intentionality: Option Intentionality
  givenness    : GivennessLevel
  timestamp     : Nat      -- временная метка (логическая)
  description   : String   -- вербальное описание
  evidence      : EvidenceVector
  deriving Repr

namespace PhenomenalObservation

/-- Валидна ли запись? -/
def isValid (po : PhenomenalObservation) : Bool :=
  po.evidence.tracked && !po.qualia.isEmpty

/-- Является ли наблюдение "фокусным" (explicit)? -/
def isFocal (po : PhenomenalObservation) : Bool :=
  po.givenness == .Explicit || po.givenness == .Constituted

end PhenomenalObservation

/-!
## §3. Phenomenal Gap (P0-02)

Этот модуль представляет GAP в системе:
- Типы определены, но нет операциональной семантики
- Нет редукции квалиа к вычислениям (и не будет)
- Требует феноменологической методологии (epoché, reduction)

gapRecord : Gap для этого модуля.
-/
phenomenalGap : Gap := {
  id := "P0-02",
  name := "Phenomenal Ground Gap",
  convergence := (1, 8),  -- 1/8 измерений закрыто
  mceLevel := 1,         -- критический
  status := .Specified,
  evidence := {
    tracked := true, specified := true, witness := false,
    compiled := false, axiom_audited := false,
    empirical := false, reproducible := false,
    independently_sourced := false },
  blocker := "Phenomenological methodology not formalized; qualia irreducible to computation" }

/-!
## §4. Evidence for this Module -/
moduleEvidence : EvidenceVector :=
  { tracked               := true
    specified             := true
    witness               := false  -- нет operational semantics
    compiled              := false  -- TBD
    axiom_audited         := false  -- TBD
    empirical             := false  -- TBD: first-person data
    reproducible          := false  -- субъективный опыт уникален
    independently_sourced := false }

moduleStatus : CanonicalStatus := moduleEvidence.toStatus

end PolyMath.Atlas
