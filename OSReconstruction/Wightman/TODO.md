# Wightman TODO: OS Reconstruction Priority Queue

Last updated: 2026-03-05 (rev 2)

This file tracks blockers on the active OS reconstruction path with current priority order.
Policy lock: no wrappers, no useless lemmas, no code bloat; close `sorry`s with substantial mathematical proofs.

## Live Sorry Census

Count convention: direct tactic holes only (`^\s*sorry\b`).

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 34 |
| `OSReconstruction/SCV` | 13 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 40 |
| **Whole project** | **89** |

_Count cross-checked 2026-03-05 by `rg '^\s*sorry\b' --glob '*.lean'` (awk sum = 89)._
_BHWTranslation.lean was incorrectly listed with 5 sorrys; actual count is 1._
_BHWExtension.lean: W_analytic_swap_distributional_agree and analytic_boundary_local_commutativity are NOW PROVED (0 sorrys)._
_GNSHilbertSpace.lean: covariance_preHilbert was proved; 1 sorry remains (vacuum_unique part 2, spectral theory)._

## Root Blocker Layers

### 1) E -> R: `WickRotation/OSToWightman.lean` (12)

Analytic continuation infrastructure:
- `inductive_analytic_continuation`
- `schwinger_holomorphic_on_base_region`
- `extend_to_forward_tube_via_bochner`
- `full_analytic_continuation` (two remaining holes)

Boundary value existence:
- `forward_tube_bv_tempered`

Axiom transfer chain:
- `bv_translation_invariance_transfer`
- `bv_lorentz_covariance_transfer`
- `bv_local_commutativity_transfer`
- `bv_positive_definiteness_transfer`
- `bv_hermiticity_transfer`

Cluster transfer:
- `bvt_cluster`

### 2) R -> E Wick Rotation Plumbing (7 total, down from 13)

`ForwardTubeLorentz.lean` (1):
- `wickRotation_not_in_PET_null`

`BHWExtension.lean` (0): **COMPLETE** — both sorrys proved as of 2026-03-05.

`BHWTranslation.lean` (1):
- `isConnected_permutedExtendedTube_inter_translate`

`SchwingerAxioms.lean` (5):
- `polynomial_growth_forwardTube_full`
- `polynomial_growth_on_PET`
- `schwinger_os_term_eq_wightman_term`
- `bhw_pointwise_cluster_euclidean`
- `W_analytic_cluster_integral`

### 3) Shared SCV Infrastructure (13 total, load-bearing)

`SCV/PaleyWiener.lean` (5):
- `paley_wiener_half_line`
- `paley_wiener_cone`
- `paley_wiener_converse`
- `paley_wiener_one_step`
- `paley_wiener_one_step_simple`

`SCV/LaplaceSchwartz.lean` (6):
- `fourierLaplace_continuousWithinAt`
- `fourierLaplace_uniform_bound_near_boundary`
- `fourierLaplace_polynomial_growth`
- `polynomial_growth_of_continuous_bv`
- `fourierLaplace_boundary_continuous`
- `fourierLaplace_boundary_integral_convergence`

`SCV/BochnerTubeTheorem.lean` (2):
- `bochner_local_extension`
- `holomorphic_extension_from_local`

## Secondary Blockers (Not First Execution Lane)

1. `Wightman/Reconstruction/Main.lean`: `wightman_uniqueness`
2. `Wightman/Reconstruction/GNSHilbertSpace.lean`: `vacuum_unique` part 2 (spectral theory; covariance_preHilbert PROVED)
3. `Wightman/WightmanAxioms.lean`: 4 infrastructural sorrys
4. `Wightman/NuclearSpaces/*`: side development, not on shortest reconstruction path
5. `ComplexLieGroups` remaining blocker status: see
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/BLOCKER_STATUS.md`

## Execution Order

1. SCV core (`LaplaceSchwartz` + `PaleyWiener` + `Bochner`) to unblock continuation machinery.
2. `OSToWightman` analytic continuation + BV existence.
3. `OSToWightman` axiom transfer and cluster chain.
4. Wick-rotation plumbing (`ForwardTubeLorentz` -> ~~`BHWExtension`~~ [complete] -> `BHWTranslation` -> `SchwingerAxioms`).
5. Final uniqueness and residual wiring.

## Commands

```bash
rg -n '^\s*sorry\b' OSReconstruction --glob '*.lean'
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman
```
