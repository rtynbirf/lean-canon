/-
  Polymath Atlas v107.0 — Grounding Module
  Imperial Archive: Chapter XI (Ontological Grounding)
  
  Status: SPECIFIED (type definitions for grounding relations)
  Evidence: tracked=true, specified=true, witness=false
  
  GAP STATUS: P0-03 (Grounding gap — requires ontological commitment)
  
  HONESTY STATEMENT:
    - Defines types for ontological grounding
    - Does NOT solve the grounding problem (philosophically open)
    - Provides framework for tracking grounding claims
-/

import PolymathAtlas.Core

namespace PolyMath.Atlas

/-!
## §1. Grounding Types

Типы для онтологического базирования.
-/

/-- Тип базирования (по Schaffer) -/
inductive GroundType : Type
  | FullGround       -- полное базирование (necessary & sufficient)
  | PartialGround    -- частичное базирование (necessary but not sufficient)
  | WeakGround       -- слабое базирование (contributory)
  deriving Repr, DecidableEq, Inhabited

/-- Онтологическая категория -/
inductive OntologicalCategory : Type
  | Concrete         -- конкретный объект
  | Abstract         -- абстрактный объект
  | Event            -- событие / процесс
  | Proposition      -- пропозиция / факт
  | Universal        -- универсалия
  | Moment           -- момент (trope, property instance)
  deriving Repr, DecidableEq, Inhabited

/-!
## §2. Grounding Relation

Отношение базирования между сущностями.
-/
structure GroundingRelation where
  groundee     : String   -- что базируется (id)
  grounder     : String   -- на чём базируется (id)
  groundType   : GroundType
  categoryGrounder : OntologicalCategory
  categoryGroundee : OntologicalCategory
  verified     : Bool     -- верифицировано формально?
  source       : String   -- источник (axiom, theorem, postulate)
  evidence     : EvidenceVector
  deriving Repr

namespace GroundingRelation

/-- Валидно ли отношение? -/
def isValid (gr : GroundingRelation) : Bool :=
  gr.evidence.tracked &&
  gr.groundee != gr.grounder  -- no self-grounding (usually)

/-- Является ли полным базированием? -/
def isFull (gr : GroundingRelation) : Bool :=
  gr.groundType == .FullGround && gr.verified

end GroundingRelation

/-!
## §3. Grounding Chain

Цепочка базирования (regress analysis).
-/
structure GroundingChain where
  terminal     : String   -- терминальный элемент (fundamental)
  links        : List GroundingChainLink
  complete     : Bool     -- достигнут фундаментальный уровень?
  deriving Repr

-- Вспомогательный тип для звена цепи
structure GroundingChainLink where
  from         : String
  to           : String
  groundType   : GroundType
  deriving Repr

namespace GroundingChain

/-- Пустая цепь (только терминал) -/
def empty (terminal : String) : GroundingChain :=
  { terminal, links := [], complete := true }

/-- Добавление звена -/
def addLink (chain : GroundingChain) (link : GroundingChainLink) : GroundingChain :=
  { chain with links := link :: chain.links, complete := false }

/-- Длина цепи -/
def length (chain : GroundingChain) : Nat :=
  chain.links.length

/-- Проверка на бесконечный регресс (эвристика: длина > 10) -/
def potentialInfiniteRegress (chain : GroundingChain) : Bool :=
  chain.length > 10

end GroundingChain

/-!
## §4. Grounding Gap (P0-03)

groundingGap : Gap для этого модуля.
-/
groundingGap : Gap := {
  id := "P0-03",
  name := "Ontological Grounding Gap",
  convergence := (1, 8),
  mceLevel := 2,  -- серьёзный, но не критический
  status := .Specified,
  evidence := {
    tracked := true, specified := true, witness := false,
    compiled := false, axiom_audited := false,
    empirical := false, reproducible := false,
    independently_sourced := false },
  blocker := "Fundamental ground not established; regress problem unsolved" }

/-!
## §5. Evidence for this Module -/
moduleEvidence : EvidenceVector :=
  { tracked               := true
    specified             := true
    witness               := false  -- no fundamental ground proven
    compiled              := false  -- TBD
    axiom_audited         := false  -- TBD
    empirical             := false  -- TBD
    reproducible          := true
    independently_sourced := false }

moduleStatus : CanonicalStatus := moduleEvidence.toStatus

end PolyMath.Atlas
