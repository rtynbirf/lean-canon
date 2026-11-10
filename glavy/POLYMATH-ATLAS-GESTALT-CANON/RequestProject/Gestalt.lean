/-
# POLYMATH_ATLAS_GESTALT

Aggregator for the six parts of the gestalt skeleton:

1. `RequestProject/Gestalt/UCC.lean` — the Universal Cognition Cycle, T1–T5;
2. `RequestProject/Gestalt/GenesisEngine.lean` — the Genesis Engine layers L1–L7;
3. `RequestProject/Gestalt/SelfReference.lean` — Urobouros closure, 'идеал = смерть', 'щель';
4. `RequestProject/Gestalt/MetaSkills.lean` — the meta-skills impossibility;
5. `RequestProject/Gestalt/ToolInventory.lean` — the tool inventory and `idiotes_tools`;
6. `RequestProject/Gestalt/AristotleCanon.lean` — Aristotle self-reference and the horizon Canon.

Every statement is stated with its informal source in its docstring, and every
proof is complete: no `sorry` remains.  No new axiom is introduced: every
postulate of the informal sources appears as a field of a `structure`.
-/
import RequestProject.Gestalt.UCC
import RequestProject.Gestalt.GenesisEngine
import RequestProject.Gestalt.SelfReference
import RequestProject.Gestalt.MetaSkills
import RequestProject.Gestalt.ToolInventory
import RequestProject.Gestalt.AristotleCanon
import RequestProject.Gestalt.CoreBridge
import RequestProject.Gestalt.HolographicScanner
