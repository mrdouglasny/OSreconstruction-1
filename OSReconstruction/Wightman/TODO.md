# Wightman TODO: OS Reconstruction Priority Queue

Last updated: 2026-03-08

This file tracks the active blocker picture on the OS reconstruction path.
Policy lock: no wrappers, no useless lemmas, no code bloat; close `sorry`s with substantial mathematical proofs.

## Live Sorry Census

Count convention: direct tactic holes only (`^[[:space:]]*sorry([[:space:]]|$)`).

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 33 |
| `OSReconstruction/SCV` | 2 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 39 |
| **Whole project** | **76** |

Count cross-checked on 2026-03-08 with:
```bash
rg -c '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
```

## Current Root Blockers

## Priority Split In `Main.lean`

There are two different lanes and they should not be conflated:

1. Analyticity / Wick-rotation lane:
   - `wightman_to_os`
   - `os_to_wightman`
   - critical file: `WickRotation/OSToWightman.lean`
   - shared dependencies: `SCV/*`, `BHWExtension`, `BHWTranslation`, `ForwardTubeLorentz`, `SchwingerAxioms`

2. Operator / GNS lane:
   - `wightman_reconstruction`
   - `wightman_uniqueness`
   - critical files: `Reconstruction/GNSHilbertSpace.lean`, `Reconstruction/Main.lean`, `vNA/Unbounded/StoneTheorem.lean`

Policy:
- while the active target is OS analyticity, do not drift into Stone/self-adjoint-generator work unless it directly unblocks `OSToWightman`
- `StoneTheorem` is not needed for the analyticity chain
- Stone is needed later for the reconstructed `spectrum_condition` / `vacuum_unique` operator-theoretic branches

### 1. `WickRotation/OSToWightman.lean` (8)

Active upstream blockers:
- `schwinger_continuation_base_step`
- `boundary_values_tempered`
- `bv_translation_invariance_transfer`
- `bv_lorentz_covariance_transfer`
- `bv_local_commutativity_transfer`
- `bv_positive_definiteness_transfer`
- `bv_hermiticity_transfer`
- `bvt_cluster`

Current status:
- the fake intermediate Bochner path is off the active chain
- the active continuation chain now goes through the base-step witness and then the forward-tube analytic continuation already constructed
- the real remaining work is base-step construction plus boundary-value existence, then the six transfer theorems

### 2. `SCV` load-bearing infrastructure (4)

`SCV/PaleyWiener.lean`:
- sorry-free
- no fake multidimensional Fourier-support interface remains
- only the 1D and slice-wise theorems are active

`SCV/LaplaceSchwartz.lean` (0):

Status:
- the interface split is now honest:
  - weak `HasFourierLaplaceRepr`
  - regular `HasFourierLaplaceReprRegular`
- the fake weak-to-regular upgrade theorem has been removed
- the real missing theorem is now explicit: construct `HasFourierLaplaceReprRegular`
  from actual Fourier-Laplace input with the right dual-cone support

`SCV/TubeDistributions.lean` (0):

Status:
- the weak bare-BV theorem fronts were removed instead of being carried as public placeholders
- only the rigorous regular variants remain, built from explicit regular input data

`SCV/BochnerTubeTheorem.lean` (2):
- `bochner_local_extension`
- `bochner_tube_extension`

Status:
- the old generic gluing theorem was too strong and has been replaced by the honest compatible-family theorem

### 3. `Reconstruction/ForwardTubeDistributions.lean` (1)

Current direct blockers:
- `distributional_uniqueness_forwardTube` — BLOCKED: needs distributional EOW infrastructure

**DELETED** (overstrong as stated — conclusions referenced F at boundary points unconstrained
by hypotheses):
- `continuous_boundary_forwardTube`
- `boundary_value_recovery_forwardTube`
- `boundary_function_continuous_forwardTube`

These are replaced by proved `_of_flatRegular` variants that take `HasFourierLaplaceReprRegular`.

**ROOT BLOCKER**: Distributional EOW variant (codex building) or Banach-Steinhaus chain.

New infrastructure (sorry-free, in `SCV/DistributionalUniqueness.lean`):
- `SCV.uniqueness_of_boundary_zero`: factored 1D EOW slicing argument; takes
  boundary=0 + ContinuousWithinAt directly (no `HasFourierLaplaceReprRegular`)
- `SCV.translateSchwartz`: translate Schwartz function by fixed vector

Status:
- proved regular flattened-input transport theorems exist for:
  - boundary continuity of the real trace
  - boundary-value recovery
  - distributional uniqueness for a difference with zero flat boundary functional
  - polynomial growth on compact forward-cone slices
- see `Proofideas/distributional_uniqueness_strategy.lean` for detailed gap analysis

### 4. Wick rotation downstream

`WickRotation/SchwingerAxioms.lean` (5):
- `polynomial_growth_forwardTube_full`
- `polynomial_growth_on_PET`
- `schwinger_os_term_eq_wightman_term`
- `bhw_pointwise_cluster_euclidean`
- `W_analytic_cluster_integral`

`WickRotation/ForwardTubeLorentz.lean` (2):
- `polynomial_growth_on_slice`
- `wickRotation_not_in_PET_null`

`WickRotation/BHWTranslation.lean` (1):
- `isConnected_permutedExtendedTube_inter_translate`

`WickRotation/BHWExtension.lean`:
- sorry-free

## Secondary Blockers

Not on the shortest OS reconstruction lane:
- `Wightman/Reconstruction/Main.lean`: `wightman_uniqueness`
- `Wightman/Reconstruction/GNSHilbertSpace.lean`: one remaining spectral-theory blocker
- `Wightman/WightmanAxioms.lean`: 4 infrastructural sorrys
- `Wightman/NuclearSpaces/*`: side development, not first execution lane
- `ComplexLieGroups` residual blockers: see the CLG status files

## Execution Order

1. Use the explicit regular flattened-input theorems in the seven forward-tube boundary theorems in `ForwardTubeDistributions.lean`.
2. Formalize the real strong-to-regular upgrade theorem in `SCV/LaplaceSchwartz.lean`.
3. Use the repaired forward-tube boundary infrastructure to attack `boundary_values_tempered` in `OSToWightman.lean`.
4. Then finish the six downstream transfer theorems in `OSToWightman.lean`.
5. Only after that, return to `SchwingerAxioms`, `ForwardTubeLorentz`, and the remaining Wick-rotation plumbing.
6. Defer `StoneTheorem` / GNS operator-theoretic work until the analyticity lane is materially settled.

## Commands

```bash
rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman
```
