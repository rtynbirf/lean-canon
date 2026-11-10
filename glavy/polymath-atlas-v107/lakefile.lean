-- Polymath Atlas v107.1-FINAL — Lake Build Configuration
--
-- HONEST CONFIGURATION (audit-fixed):
--   - Toolchain pinned in lean-toolchain: leanprover/lean4:v4.28.0
--     (MUST match Mathlib tag v4.28.0 — Mathlib releases are tied to toolchains)
--   - Requires Mathlib v4.28.0 (large dependency, ~3 GB)
--   - 14 modules in PolymathAtlas/
--   - No executable target: Main.lean intentionally absent (library only)
--
-- BUILD INSTRUCTIONS:
--   1. elan install leanprover/lean4:v4.28.0
--   2. lake exe cache get   (optional; fetches prebuilt Mathlib oleans)
--   3. lake update          (resolves Mathlib — first time ~30 min)
--   4. lake build           (compiles all 14 modules)

import Lake
open Lake DSL

package «polymath-atlas» where
  defaultTargets := #[`PolymathAtlas]

-- Зависимость от Mathlib v4.28.0
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

-- Библиотека: все 14 модулей PolymathAtlas
-- (единственное объявление lean_lib — дубликаты недопустимы)
lean_lib «PolymathAtlas» where
  roots := #[
    `PolymathAtlas.Core,
    `PolymathAtlas.AxiomAudit,
    `PolymathAtlas.FrobeniusPair,
    `PolymathAtlas.AxiologicalSpec,
    `PolymathAtlas.Embodiment,
    `PolymathAtlas.EmbodimentModel,
    `PolymathAtlas.Divergence,
    `PolymathAtlas.Phenomenal,
    `PolymathAtlas.Grounding,
    `PolymathAtlas.Language,
    `PolymathAtlas.Temporality,
    `PolymathAtlas.Pathology,
    `PolymathAtlas.Gaps,
    `PolymathAtlas.Synthesis
  ]

-- Справка по целям:
--   lake build PolymathAtlas.Core        — только Core
--   lake build PolymathAtlas             — все 14 модулей
--   lake exe cache get                   — кэш Mathlib
