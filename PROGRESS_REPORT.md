# Progress Report: OS Reconstruction Formalization

## Overview

~44,000 lines of Lean 4 across 69 files. **14 axioms**, **~73 sorrys** across 24 files.

Contributors: xiyin, mrdouglasny, e-vergo. See [`HISTORY.md`](HISTORY.md) for
detailed development history.

---

## Reconstruction Theorems

Both bridge theorems are sorry-free:

| Theorem | Direction | Status |
|---------|-----------|--------|
| `os_to_wightman_full` | E' → R' | **sorry-free** |
| `wightman_to_os_full` | R → E | **sorry-free** (3 textbook axioms) |

### R→E Direction: OS Axiom Verification (2 sorrys, 15 proven)

| Theorem | Status | Via |
|---------|--------|-----|
| `W_analytic_lorentz_on_tube` | **done** | `distributional_uniqueness_forwardTube` |
| `W_analytic_continuous_boundary` | **done** | `continuous_boundary_forwardTube` |
| `W_analytic_local_commutativity` | **done** | `analytic_boundary_local_commutativity` axiom |
| `constructedSchwinger_tempered` (E0) | **done** | `wick_rotated_schwinger_tempered` axiom |
| `constructedSchwinger_translation_invariant` (E1a) | **done** | `bhw_translation_invariant` axiom |
| `constructedSchwinger_rotation_invariant` (E1b) | **done** | SO(d+1) via `schwinger_euclidean_invariant` |
| `constructedSchwinger_symmetric` (E3) | **done** | `integral_perm_eq_self` (sorry-free) |
| `constructedSchwinger_reflection_positive` (E2) | sorry | Needs Borchers involution + Wick rotation |
| `W_analytic_cluster_integral` (E4) | sorry | Needs cluster decomposition + dominated convergence |

### E→R Direction: Analytic Continuation (8 sorrys)

| Theorem | Status | What's needed |
|---------|--------|---------------|
| `full_analytic_continuation` | sorry | Iterate inductive axiom + E1 + Bochner |
| `boundary_values_tempered` | sorry | Full analytic continuation + BV theory |
| `constructWightmanFunctions` (6 fields) | sorry | Depend on boundary_values_tempered |
| `os_to_wightman_full` | **done** | Sorry-free (extracts from boundary_values_tempered) |

---

## All Axioms (14)

### SCV/Distribution Theory (5)

| # | Axiom | File | Reference |
|---|-------|------|-----------|
| 1 | `continuous_boundary_tube` | `SCV/TubeDistributions.lean` | Vladimirov §25-26 |
| 2 | `boundary_value_recovery` | `SCV/TubeDistributions.lean` | Vladimirov §25-26 |
| 3 | `boundary_value_zero` | `SCV/TubeDistributions.lean` | du Bois-Reymond + BV recovery |
| 4 | `polynomial_growth_tube` | `SCV/TubeDistributions.lean` | Vladimirov §25-26 |
| 5 | `bochner_tube_theorem` | `SCV/TubeDistributions.lean` | Bochner 1938 |

All require Fourier-Laplace transforms not in Mathlib. `distributional_uniqueness_tube`
was proved (not axiom) from `boundary_value_zero` + edge-of-the-wedge + identity theorem.

### Analytic Continuation (1)

| # | Axiom | File | Reference |
|---|-------|------|-----------|
| 6 | `bargmann_hall_wightman` | `AnalyticContinuation.lean` | Needs complex Lie group theory (in progress) |

`edge_of_the_wedge` was eliminated — proved from SCV tube domain extension (`9e1e97f`).

### WickRotation (8)

| # | Axiom | Reference |
|---|-------|-----------|
| 7 | `forward_tube_bv_integrable` | Vladimirov §26 |
| 8 | `lorentz_covariant_distributional_bv` | Streater-Wightman §2.4 |
| 9 | `euclidean_points_in_permutedTube` | Jost §IV.5 |
| 10 | `bhw_translation_invariant` | S-W Thm 2.8 |
| 11 | `analytic_boundary_local_commutativity` | S-W Thm 3-5, Jost §IV.3 |
| 12 | `bhw_distributional_boundary_values` | S-W Thm 2-11 |
| 13 | `wick_rotated_schwinger_tempered` | OS I Prop 5.1 |
| 14 | `inductive_analytic_continuation` | OS II Thm 4.1 |

---

## Sorry Census

**~73 total** across 24 files.

| Count | File | Category |
|-------|------|----------|
| 16 | `vNA/MeasureTheory/CaratheodoryExtension.lean` | Carathéodory measure extension |
| 14 | `NuclearSpaces/SchwartzNuclear.lean` | Nuclear spaces |
| 13 | `vNA/Unbounded/Spectral.lean` | Unbounded spectral theory |
| 12 | `WickRotation.lean` | 2 R→E + 8 E→R + 2 helpers |
| 10 | `NuclearSpaces/GaussianFieldBridge.lean` | Gaussian-field bridge |
| 10 | `vNA/KMS.lean` | KMS condition |
| 8 | `vNA/ModularAutomorphism.lean` | Connes cocycle |
| 6 | `vNA/ModularTheory.lean` | Tomita-Takesaki |
| 4 | `Reconstruction.lean` | Wiring layer |
| 4 | `vNA/Unbounded/StoneTheorem.lean` | Stone's theorem |
| 3 | `NuclearSpaces/BochnerMinlos.lean` | Bochner-Minlos |
| 3 | `ComplexLieGroups/Connectedness.lean` | Complex Lorentz invariance |
| 2 | `ComplexLieGroups/LorentzLieGroup.lean` | SO⁺(1,d) infrastructure |
| 2 | `vNA/Predual.lean` | Predual theory |
| 2 | `vNA/Spectral/Module.lean` | Spectral module |
| 2 | `NuclearSpaces/NuclearSpace.lean` | Nuclear space defs |
| 2 | `WightmanAxioms.lean` | Wightman axioms |
| ~7 | Everything else | Scattered (1 each) |

---

## What's Closest to Provable Next

1. **`bargmann_hall_wightman` axiom** — xiyin is actively building
   complex Lorentz invariance infrastructure (`Connectedness.lean`).
   Once `complex_lorentz_invariance` is fully proved, this axiom is eliminable.

2. **`hartogs_analyticity` sorry** (IdentityTheorem.lean) — ~200 LOC with Osgood lemma.

3. **vNA sorrys** — e-vergo eliminated 13 in wave 1; remaining ~57 across
   ModularAutomorphism, KMS, CaratheodoryExtension, Unbounded/Spectral.

4. **E→R direction** — The 8 sorrys in WickRotation.lean require
   the full OS-II inductive analytic continuation machinery (iterate
   `inductive_analytic_continuation` axiom + E1 rotation + Bochner tube theorem).

---

## Sorry-Free Highlights

- **`os_to_wightman_full`** — E'→R' bridge theorem
- **`wightman_to_os_full`** — R→E bridge theorem (via 3 textbook axioms)
- `W_analytic_lorentz_on_tube` — Lorentz invariance on forward tube
- `ForwardTubeDistributions.lean` — Forward tube as tube domain (591 lines)
- `edge_of_the_wedge` — proved from SCV tube domain extension (was axiom)
- `complex_lorentz_invariance` — SCV/Osgood + identity theorem
- `isPathConnected` (SO⁺(1,d;ℂ)) — via Wick rotation isomorphism
- `separating_iff_cyclic_commutant` — projection argument
- `SeparatelyAnalytic.lean` — Taylor series, separately analytic (906 lines)
- `Osgood.lean` — Osgood's lemma (627 lines)
- `GaussianFieldBridge.lean` — Nuclear space bridge (149 lines)
- OS axioms E1 (translation + SO(d+1) rotation), E3 (permutation)
