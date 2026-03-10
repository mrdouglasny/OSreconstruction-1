# SCV TODO: OS-Critical Analytic Continuation Chain

Last updated: 2026-03-10

This TODO tracks the remaining `SCV` blockers on the OS reconstruction path.

Count convention in this file: direct tactic holes only,
`rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction/SCV --glob '*.lean'`.

## Live Sorry Census

| Scope | Direct `sorry` lines |
|---|---:|
| `OSReconstruction/SCV` | 2 |

Breakdown:
- `SCV/LaplaceSchwartz.lean`: 0
- `SCV/TubeDistributions.lean`: 0
- `SCV/DistributionalUniqueness.lean`: 0
- `SCV/SchwartzComplete.lean`: 0
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

### `SCV/SchwartzComplete.lean` (0) — NEW, CODEX-OWNED

**Owner: Codex agent.** Sorry-free. Provides:
- `SchwartzMap.instCompleteSpace` — completeness of `𝓢(E, F)`
- `SchwartzMap.instBarrelledSpace` — barrelledness
- `SchwartzMap.tempered_equicontinuous` — Banach-Steinhaus for tempered distributions
- `SchwartzMap.tempered_uniform_schwartz_bound` — concrete finite seminorm bound
- `SchwartzMap.tempered_equicontinuous_of_tendsto` — convergent sequences are equicontinuous

### `SCV/DistributionalUniqueness.lean` (0) — NEW, CODEX-OWNED

**Owner: Codex agent.** New file with 0 sorrys providing:
- `translateSchwartz`: translate a Schwartz function by a fixed vector (PROVED)
- `uniqueness_of_boundary_zero`: if G is holomorphic on T(C), vanishes pointwise
  on the real boundary, and has ContinuousWithinAt at all boundary points,
  then G = 0 on T(C). This is the 1D EOW slicing argument factored out from
  `distributional_uniqueness_tube_of_regular`. (PROVED)
- Support transport lemmas for `translateSchwartz` (PROVED)
- `uniqueness_of_boundary_zero_on_interval` — local 1D uniqueness on (a,b) (PROVED)

## Distributional EOW — COMPLETE (2026-03-10)

**All distributional EOW infrastructure is proved with 0 sorrys.**

Full chain:
1. `SCV/SchwartzComplete.lean` (0 sorrys): `CompleteSpace`, `BarrelledSpace`, Banach-Steinhaus chain
2. `SCV/DistributionalUniqueness.lean` (0 sorrys):
   - `exists_integral_clm_of_continuous` — truncation → CLM via Banach-Steinhaus
   - `distributional_uniqueness_tube_of_zero_bv` — tube uniqueness from distributional BV = 0
   - `eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` — pointwise extraction
3. `Wightman/Reconstruction/ForwardTubeDistributions.lean` (0 sorrys):
   - `distributional_uniqueness_forwardTube` — PROVED (flattening + tube uniqueness)
4. `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean` (0 sorrys):
   - Distributional pairing → pointwise on real open → connected-overlap propagation
5. `Wightman/Reconstruction/WickRotation/BHWExtension.lean`:
   - `W_analytic_swap_boundary_pairing_eq` — PROVED via distributional chain
   - `analytic_extended_local_commutativity` — PROVED (extendF-level pointwise swap)
   - `analytic_boundary_local_commutativity_of_boundary_continuous` — PROVED
6. `PermutationFlow.lean` fully rewired to distributional hypotheses (0 sorrys)

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
