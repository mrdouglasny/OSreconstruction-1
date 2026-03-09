# SCV TODO: OS-Critical Analytic Continuation Chain

Last updated: 2026-03-08

This TODO tracks the remaining `SCV` blockers on the OS reconstruction path.

Count convention in this file: direct tactic holes only,
`rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction/SCV --glob '*.lean'`.

## Live Sorry Census

| Scope | Direct `sorry` lines |
|---|---:|
| `OSReconstruction/SCV` | 4 |

Breakdown:
- `SCV/LaplaceSchwartz.lean`: 2
- `SCV/TubeDistributions.lean`: 0
- `SCV/BochnerTubeTheorem.lean`: 2
- `SCV/PaleyWiener.lean`: 0

## Session Summary

- The fake multidimensional support scaffolding was removed from `PaleyWiener.lean`.
- `LaplaceSchwartz.lean` now has the correct weak/regular split:
  - `HasFourierLaplaceRepr`
  - `HasFourierLaplaceReprRegular`
- `TubeDistributions.lean` now keeps only the proved regular variants; the unused weak
  placeholder fronts were removed.
- The unproved weak-to-regular upgrade theorem was removed.
  Rationale: the singularity-free bound `‖F(x+iεη)‖ ≤ C(1+‖x‖)^N` is not
  derivable from `poly_growth` alone (Phragmén-Lindelöf only gives
  `C(1+‖x‖)^N/ε^k`), and the remaining Vladimirov §26.2 continuity upgrade
  should not be hidden behind a fake interface.

## Load-Bearing Items

### `SCV/LaplaceSchwartz.lean` (0)

Meaning:
- the weak/regular split is now honest
- no fake upgrade theorem from weak BV data remains

### `SCV/TubeDistributions.lean` (0)

Meaning:
- only the rigorous regular variants remain
- the unused weak placeholder fronts were removed instead of being carried as public `sorry`s

### `SCV/BochnerTubeTheorem.lean` (2)

Remaining blockers:
- `bochner_local_extension`
- `bochner_tube_extension`

Meaning:
- the old generic gluing theorem was too strong and has been removed
- current work should build on the compatible-family gluing theorem instead

### `SCV/PaleyWiener.lean` (0)

Status:
- sorry-free
- `paley_wiener_half_line` and the slice-wise `paley_wiener_one_step` are proved
- no fake multidimensional Fourier-support notion remains in the public API

## Execution Order

1. Use the explicit regular package directly in downstream flattened-tube transport.
2. Return to the real missing theorem: construct `HasFourierLaplaceReprRegular`
   from actual Fourier-Laplace input with the right dual-cone support.
3. Return to `BochnerTubeTheorem.lean`.

### `SCV/DistributionalUniqueness.lean` (0) — NEW

New file with 0 sorrys providing:
- `translateSchwartz`: translate a Schwartz function by a fixed vector (PROVED)
- `uniqueness_of_boundary_zero`: if G is holomorphic on T(C), vanishes pointwise
  on the real boundary, and has ContinuousWithinAt at all boundary points,
  then G = 0 on T(C). This is the 1D EOW slicing argument factored out from
  `distributional_uniqueness_tube_of_regular`. (PROVED)

## ROOT BLOCKER: Distributional EOW / Banach-Steinhaus

The main blocker for closing `distributional_uniqueness_forwardTube`
(in `Wightman/Reconstruction/ForwardTubeDistributions.lean`) is:

**Bare distributional BV → equality on the tube**

Two approaches under development:
1. **Distributional EOW** (codex building): edge-of-the-wedge with S'-convergence
   instead of ContinuousWithinAt. Proof route: mollify boundary distributions →
   honest smooth boundary data → classical identity theorem → pass to limit.
   This directly feeds `distributional_uniqueness_forwardTube`.
2. **Banach-Steinhaus** (on hold): if distributional EOW shows it's needed,
   build minimal Schwartz-family uniform-boundedness. Chain:
   CompleteSpace(SchwartzMap) → BaireSpace → BarrelledSpace → WithSeminorms.banach_steinhaus.

The 3 overstrong theorems (`continuous_boundary_forwardTube`,
`boundary_value_recovery_forwardTube`, `boundary_function_continuous_forwardTube`)
were DELETED — their conclusions referenced F at boundary points unconstrained by
hypotheses. Proved `_of_flatRegular` variants exist.

Documented in: `Proofideas/distributional_uniqueness_strategy.lean`

## Stable Completed Core

- `Polydisc.lean`
- `IteratedCauchyIntegral.lean`
- `Osgood.lean`
- `Analyticity.lean`
- `TubeDomainExtension.lean`
- `IdentityTheorem.lean`
- `FourierLaplaceCore.lean`
- `PaleyWiener.lean`
- `DistributionalUniqueness.lean` — NEW

`edge_of_the_wedge_theorem` is proved and axiom-free.
