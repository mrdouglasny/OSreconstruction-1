# Systematic Development Plan (OS Reconstruction Critical Path)

Last updated: 2026-03-05

This is the active execution plan for closing `sorry`s on the OS reconstruction path.
It supersedes the earlier BHW-first ordering.

## 1. Proof-Quality Policy (Hard Constraints)

1. No wrappers, no useless lemmas, no code bloat.
2. Every new lemma must either:
   - close a blocker directly, or
   - carry nontrivial reusable mathematical content needed downstream.
3. Do not add forwarding/repackaging lemmas that only rename existing statements.
4. Close `sorry`s with substantial proofs (not assumption padding or existential hiding).
5. Numerical checks are optional diagnostics; they are not required workflow gates.

## 2. Live Sorry Census

Counts verified with:
`rg -n '^\s*sorry\b' OSReconstruction --glob '*.lean'`

| Scope | Sorrys |
|---|---:|
| `OSReconstruction/Wightman` | 40 |
| `OSReconstruction/SCV` | 13 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 40 |
| **Total** | **95** |

## 3. Primary Priority Stack

### A) E -> R direction (`OSToWightman.lean`, 12 sorrys)

Clusters:
1. Analytic continuation infrastructure (4 core obligations):
   - `inductive_analytic_continuation`
   - `schwinger_holomorphic_on_base_region`
   - `extend_to_forward_tube_via_bochner`
   - `full_analytic_continuation` (rotation-invariance step)
2. Boundary-value existence (1):
   - `forward_tube_bv_tempered` / `boundary_values_tempered` chain
3. Axiom transfer chain (7):
   - transfer of W0-W5-style properties through holomorphic extension + boundary values
4. Cluster property (2):
   - `bvt_cluster` and companion transport lemma

### B) R -> E wick-rotation submodules (13 sorrys total)

1. `SchwingerAxioms.lean` (5)
2. `BHWTranslation.lean` (5)
3. `BHWExtension.lean` (2)
4. `ForwardTubeLorentz.lean` (1)

### C) Shared SCV infrastructure (13 sorrys total, deepest dependency)

1. `PaleyWiener.lean` (5)
2. `LaplaceSchwartz.lean` (6)
3. `BochnerTubeTheorem.lean` (2)

These SCV blockers are root dependencies for both E -> R and R -> E analytic continuation chains.

## 4. Secondary / Standalone Blockers

1. `Wightman/Reconstruction/Main.lean`: `wightman_uniqueness` (1)
2. `Wightman/Reconstruction/GNSHilbertSpace.lean`: vacuum-uniqueness chain (1)
3. `Wightman/WightmanAxioms.lean`: 4 infrastructural sorrys
4. `Wightman/NuclearSpaces/*`: 7 sorrys (important but not critical-path)
5. `ComplexLieGroups/*`: 2 remaining BHW-permutation blockers (maintained, not current top lane)

## 5. Execution Order

1. Close SCV load-bearing lemmas (`LaplaceSchwartz` -> `PaleyWiener` -> `Bochner`).
2. Close `OSToWightman.lean` analytic continuation + BV existence core.
3. Close axiom-transfer and cluster-transfer chain in `OSToWightman.lean`.
4. Close R -> E wick-rotation plumbing (`ForwardTubeLorentz`, `BHWExtension`, `BHWTranslation`, `SchwingerAxioms`).
5. Finish final wiring (`wightman_uniqueness`, remaining `GNSHilbertSpace`, residual `WightmanAxioms` blockers).

## 6. Deprioritized Work (Unless It Unblocks the Above)

1. Most of `vNA/*`
2. Non-critical NuclearSpaces side development
3. Additional CLG refactors not required by active OS reconstruction blockers

## 7. Verification Commands

```bash
# module builds
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman

# blocker census
rg -n '^\s*sorry\b' OSReconstruction --glob '*.lean'
rg -n '^axiom\\s+' OSReconstruction --glob '*.lean'
```
