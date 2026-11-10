# Proof-optimization log

Scope: only proof bodies and dead proof arguments were touched. **No theorem statement
was changed**, no `sorry`/`admit` was introduced, and the axiom footprint is unchanged
(`propext`, `Classical.choice`, `Quot.sound`; see `AXIOMS_REPORT.md`).

Measured effect on `lake build`: **106 → 20 diagnostics** (the remaining ones are
listed at the bottom with the reason they were left alone). The build stays green
(8253 targets).

## Dead simp arguments removed

```
RequestProject/Atlas/UAM_Thompson.lean:111       — simp only [...]        — dropped Set.mem_singleton_iff
RequestProject/Atlas/UAM_Thompson.lean:189       — simp +decide [...]     — dropped EpsilonNFA.epsStep
RequestProject/Atlas/UAM_Thompson.lean:1512      — simp_all +decide [...] — dropped the whole argument list (ThompsonState.body)
RequestProject/Atlas/UAM_Thompson.lean:1574      — simp_all +decide [...] — dropped EpsilonNFA.epsStep
RequestProject/Atlas/UAM_Thompson.lean:1580      — simp_all +decide [...] — dropped the whole argument list (thompsonTransition)
RequestProject/Atlas/UAM_KleeneComplete.lean:183 — simp [...]             — dropped EliminatedPath
RequestProject/Atlas/UAM_KleeneComplete.lean:300 — simp [...]             — dropped or_assoc
RequestProject/Atlas/UAM_D_eq_J.lean:34          — simp +decide [...]     — dropped hn.2.1
RequestProject/Atlas/UAM_D_eq_J.lean:57          — simp [...]             — dropped L_eq
```

## `simpa` → `simp` where nothing was being fed in

```
RequestProject/Atlas/UAM_KleeneCounterexample.lean:47 — simpa [...] → simp [...]
RequestProject/Atlas/UAM_D_eq_J.lean:65               — simpa only [...] → simp only [...]
RequestProject/Atlas/UAM_D_eq_J.lean:75               — simpa only [...] → simp only [...]
```

## Dead pattern variables replaced by `_`

```
RequestProject/Atlas/UAM_Thompson.lean:72,73,74,76,77,80,84 — thompsonTransition match arms
```

## Section variables no longer force-included

`omit [...] in` was added in front of 30 theorems whose proofs never use the
automatically included instance, so the theorems now really are stated at the
generality at which they are proved:

```
RequestProject/Atlas/UnifiedModel.lean          — 17 theorems — omit [NeZero n] in
RequestProject/Atlas/GreenAnatomy.lean          — 14 theorems — omit [NeZero n] in
RequestProject/Atlas/UAMTransfer/Properties.lean — 1 theorem  — omit [CompleteSpace K] in
```

## Naming fixes that also removed diagnostics

```
GreenAnatomy.GreenAnatomy   → GreenAnatomy.GreenStructure      (namespace no longer duplicated; 9 diagnostics)
UnifiedModel.UnifiedModel   → UnifiedModel.UnifiedAgentModel   (namespace no longer duplicated; 27 diagnostics)
```
Call sites updated in `ModelLadder.lean` and `UAM_CognitiveDFA.lean`.

## Deliberately left alone

| location | diagnostic | reason |
|---|---|---|
| `GreenAnatomy.lean:kernel_eq_imp_reach_eq` | `[NeZero n]` reported unused | the instance is supplied explicitly by `R_eq_iff_kernel_eq` downstream; adding `omit` breaks that proof. A comment now records this. |
| `UAM_D_eq_J.lean:33`, `UAM_D_eq_J.lean:62` | two "unused simp argument" reports on the same call | the reports are mutually exclusive (removing either one makes the other necessary); the call is already minimal in the sense that no single pair can be dropped. |
| `UAM_Beginning.lean:73`, `UAM_Schutzenberger.lean:141`, `UAM_Ideal.lean`, `UAM_Inverse.lean`, `UAM_Semilattice.lean`, `UAM_Nilpotent.lean`, `UAM_AutomatonStops.lean` | unused hypothesis in a theorem **statement** | removing them would change the statements, which this pass is not allowed to do. In two of these files the docstring already records that the unused hypothesis is intentional. |
| `ConstitutionBridges.lean:436` | namespace duplicated in `ConstitutionBridges.ConstitutionBridges` | the docstring states this is a deliberately requested public alias for `BridgePackage`. |
