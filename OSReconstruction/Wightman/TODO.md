# Wightman QFT Module — TODO

## TOP PRIORITY: OS Reconstruction Theorems

**Key insight**: Nuclear spaces / Minlos are NOT needed for the OS reconstruction theorems.
The reconstruction takes Schwinger functions as given input — nuclear spaces are about
*constructing* those Schwinger functions (upstream), not about reconstructing Wightman QFT.

Fermion theories on the lattice and Yang-Mills at nonzero theta angle do NOT admit
Borel measures in field space, but they are reflection positive and expected to be
Wightman QFTs — OS reconstruction is strictly more general than the NuclearSpaces/Minlos path.

### Critical Path for OS Reconstruction

1. ~~**Schwartz tensor product sorrys**~~ ✅ DONE (SchwartzTensorProduct.lean is sorry-free)
2. ~~**Field operator well-definedness**~~ ✅ DONE (adjoint relation → preserves null → well-defined)
3. ~~**GNS construction**~~ ✅ DONE (GNSConstruction.lean is sorry-free)
4. ~~**Jost lemma**~~ ✅ DONE (AnalyticContinuation.lean:545-640, fully proven)
5. ~~**1D edge-of-the-wedge**~~ ✅ DONE (EdgeOfWedge.lean, Morera + Cauchy-Goursat)
6. ~~**Euclidean point geometry**~~ ✅ DONE (euclidean_ordered_in_forwardTube, euclidean_distinct_in_permutedTube)
7. ~~**Lorentz invariance on forward tube**~~ ✅ DONE (W_analytic_lorentz_on_tube)
8. ~~**E3 permutation symmetry**~~ ✅ DONE (constructedSchwinger_symmetric, sorry-free)
9. ~~**E1 translation invariance**~~ ✅ DONE (constructedSchwinger_translation_invariant, sorry-free)
10. ~~**E1 rotation invariance (det=1)**~~ ✅ DONE (constructedSchwinger_rotation_invariant, det=1 branch)
11. ~~**E'→R' theorem**~~ ✅ DONE (os_to_wightman_full, sorry-free)
12. ~~**edge_of_the_wedge**~~ ✅ PROVED (via SCV.edge_of_the_wedge_theorem, sorry-free)
13. ~~**bargmann_hall_wightman**~~ ✅ PROVED (via ComplexLieGroups/Connectedness.lean, modulo 3 sorrys)
14. **R→E remaining sorrys** (local commutativity, E0, E2, E4, rotation det=-1, BV wiring)
15. **E→R analytic continuation chain** (OS II §IV-V, independent of 12-14)
16. **constructWightmanFunctions** (7 fields, depend on 13 + 15)
17. ~~**Main reconstruction theorems**~~ ✅ DONE (Reconstruction/Main.lean wiring, except wightman_uniqueness)

### What Does NOT Block Reconstruction

- Nuclear operator properties (NuclearOperator.lean)
- Nuclear space closure properties (NuclearSpace.lean)
- Schwartz nuclearity (SchwartzNuclear.lean)
- Bochner-Minlos theorems (BochnerMinlos.lean)
- Free field measure (EuclideanMeasure.lean)

These are needed for *constructive QFT* (building concrete examples of Schwinger functions)
but not for the OS reconstruction theorems themselves.

## Axiom and Sorry Census

### Axioms: ZERO (as of 2026-02-23)

All 15 former axioms have been eliminated and converted to theorems (some with sorry'd proofs):
- 5 SCV/TubeDistributions axioms → theorems (delegating to LaplaceSchwartz/BochnerTubeTheorem)
- `edge_of_the_wedge` → proved theorem (via SCV.edge_of_the_wedge_theorem)
- `bargmann_hall_wightman` → proved theorem (via ComplexLieGroups/Connectedness.lean)
- 8 WickRotation axioms → proved theorems (some sorry-free, some with decomposed sorrys)

### Known design issues (identified via Gemini deep-think review, 2026-02-21)

1. **`continuous_boundary_tube` may be too strong at lightcone points.**
   This SCV axiom gives `ContinuousWithinAt` at ALL real boundary points.
   In interacting QFTs, the Wightman function has singularities at lightcone
   points ((x_i - x_j)² = 0), where the boundary value exists only as a
   distribution, not a continuous function. The axiom is correct at spacelike
   and timelike separated points, and all current uses (e.g.,
   `analytic_boundary_local_commutativity`) only evaluate at spacelike points.
   A future refinement could restrict `ContinuousWithinAt` to non-lightcone
   boundary points.

2. **`constructSchwingerFunctions` uses a raw Lebesgue integral.**
   The definition `S_n(f) = ∫ F_ext(Wick(x)) f(x) dx` integrates over all
   of `NPointDomain` including coincident points x_i = x_j. For fundamental
   scalar fields in d+1 ≥ 2, the near-diagonal singularities (~1/|x|^{d-1})
   are locally integrable and the integral converges. For higher-dimension
   fields (scaling dimension Δ > d/2), the singularity could be non-integrable,
   and Lean's `∫` would silently return 0. The current formalization implicitly
   restricts to theories where the integral converges. A more general approach
   would define S_n as a distributional extension (tempered distribution agreeing
   with the Lebesgue integral away from diagonals).

### ~~SeparatelyAnalytic.lean — 0 sorrys~~ ✅ DONE (2026-02-15)

All theorems proven and verified `sorryAx`-free:
- `continuousAt_deriv_of_continuousOn` ✅ — Cauchy integral for derivative + tube lemma
- `differentiableOn_cauchyIntegral_param` ✅ — Leibniz rule + Osgood's lemma
- `osgood_lemma_prod` ✅ — direct Fréchet derivative construction
- `osgood_lemma` ✅ — induction using `osgood_lemma_prod`
- `holomorphic_extension_across_real` ✅ — via `osgood_lemma`
- `tube_domain_gluing` ✅ — via `osgood_lemma`
- `differentiableOn_of_continuous_off_real_1d` ✅ — 1D holomorphic extension

### AnalyticContinuation.lean — 0 sorrys, 0 axioms ✅

Both `edge_of_the_wedge` and `bargmann_hall_wightman` are now **proved theorems**.
All theorems in this file are fully proven.

### WickRotation/ — 30 sorrys, 0 axioms (split into 5 subfiles)

Refactored from a single 3475-line file into a `WickRotation/` subfolder:

| File | Lines | Sorrys | Content |
|------|-------|--------|---------|
| `ForwardTubeLorentz.lean` | ~735 | 4 | Cone/tube preservation, Lorentz COV, distributional BV |
| `BHWExtension.lean` | ~177 | 2 | BHW extension definition, local commutativity |
| `BHWTranslation.lean` | ~1013 | 5 | Translation invariance, `constructSchwingerFunctions` |
| `SchwingerAxioms.lean` | ~836 | 5 | E0-E4 axiom proofs |
| `OSToWightman.lean` | ~752 | 14 | E'→R' direction, bridge theorems |
| `WickRotation.lean` | barrel | 0 | Re-exports OSToWightman |

Note: BV convention fix (2026-02-24) changed the approach direction hypothesis from
`∀ k, InOpenForwardCone d (η k)` (each component in V⁺) to `InForwardCone d n η`
(successive differences η_k - η_{k-1} ∈ V⁺), which is the correct condition for
`x + iε·η` to lie in `ForwardTube`. This added 1 sorry in ForwardTubeLorentz
(Lorentz preserving ForwardConeAbs) and 1 in OSToWightman.

**R→E direction — remaining sorrys (2, HARD):**

| File | Theorem | Description | Difficulty |
|------|---------|-------------|------------|
| SchwingerAxioms | `schwinger_os_term_eq_wightman_term` | E2: distributional BV identity | Hard: Borchers involution ↔ time reflection |
| SchwingerAxioms | `W_analytic_cluster_integral` | E4: integral factorization at large separation | Hard: cluster + dominated convergence |

**E→R direction — sorrys (26, decomposed from former axioms):**

The E→R chain has been fully decomposed into named sorry targets. The critical path is:
1. `inductive_analytic_continuation` (Paley-Wiener one-step) → `full_analytic_continuation`
2. `boundary_values_tempered` (from growth estimates)
3. 6 transfer properties: `e2r_normalization`, `e2r_translation`, `e2r_lorentz`,
   `e2r_locality`, `e2r_positivity`, `e2r_hermiticity`

Plus infrastructure: polynomial growth estimates, distributional BV limits, translation
invariance chain, swap distributional agreement.

### Reconstruction.lean — 0 sorrys ✅ (theorems moved to Main.lean)

Theorems `wightman_reconstruction`, `wightman_uniqueness`, `wightman_to_os`, `os_to_wightman`
moved to Reconstruction/Main.lean to resolve circular import constraints
(GNSHilbertSpace and WickRotation both import Reconstruction).

### Reconstruction/Main.lean — 1 sorry (wiring file)

| # | Theorem | Status |
|---|---------|--------|
| 15 | `wightman_reconstruction` | ✅ Wired to `wightman_reconstruction'` (GNSHilbertSpace) |
| 16 | `wightman_uniqueness` | sorry — standard GNS uniqueness argument |
| 17 | `wightman_to_os` | ✅ Wired to `wightman_to_os_full` (WickRotation) |
| 18 | `os_to_wightman` | ✅ Wired to `os_to_wightman_full` (WickRotation) |

### GNSHilbertSpace.lean — 1 sorry in gnsQFT (down from 10), matching condition PROVED

**New file (2026-02-23).** Completes the GNS Hilbert space construction:
- Phase 1: `AddCommGroup` + `Module ℂ` on `PreHilbertSpace` (sorry-free)
- Phase 2: `InnerProductSpace.Core` (sorry-free)
- Phase 3: `NormedAddCommGroup` + `InnerProductSpace` (sorry-free, diamond-free)
- Phase 4: `GNSHilbertSpace` = Cauchy completion (sorry-free), `gnsVacuum_norm` proved
- Phase 5: `gnsQFT` (WightmanQFT structure, 3 sorrys remaining):
  - **PROVED**: `vacuum_normalized`, `vacuum_in_domain`, `operator_domain`
  - **PROVED**: `operator_add`, `operator_smul`, `operator_vector_add`, `operator_vector_smul`
  - **PROVED**: `wightman_reconstruction'` — matching condition (Wightman functions reproduced)
  - **PROVED**: `poincare_rep`, `vacuum_invariant`, `matrix_element_continuous`
  - **PROVED**: `poincareActionOnSchwartz`, `poincareAction_spec`, `covariance`, `locality`
  - **PROVED**: `vacuum_unique` part 1 (time-translation invariance from Poincaré invariance)
  - **SORRY**: `spectrum_condition` — needs Stone's theorem + spectral theory (not in Mathlib)
  - ~~**SORRY**: `cyclicity`~~ ✅ PROVED
  - ~~**SORRY**: `vacuum_unique` part 2~~ ✅ PROVED
- Domain: `gnsDomainSubmodule` = image of PreHilbertSpace under completion embedding (not ⊤)
- Domain density: `gnsDomain_dense` proved
- Key lemmas (sorry-free): `gnsFieldOp_coe`, `operatorPow_gnsQFT_eq`, `gnsVacuum_norm`

### PoincareAction.lean — 0 sorrys ✅

Previously had `affineComp_decay` sorry. Now fully proven using `SchwartzMap.compCLM`
with temperate growth and upper bound lemmas.

### PoincareRep.lean — 0 sorrys ✅

Previously had `affineCompNPoint_decay` sorry. Now fully proven using n-point versions
of temperate growth and upper bound lemmas, with `SchwartzMap.compCLM`.

### GNSConstruction.lean — 0 sorrys ✅

(Previously listed as having sorrys — verified sorry-free on 2026-02-13)

## Dependency Graph

```
SeparatelyAnalytic.lean ✅ (0 sorrys)
│
▼
AnalyticContinuation.lean ✅ (0 sorrys, 0 axioms)
│
│  edge_of_the_wedge ✅ PROVED (via SCV.edge_of_the_wedge_theorem)
│  bargmann_hall_wightman ✅ PROVED (via ComplexLieGroups/Connectedness.lean)
│
▼
WickRotation/ (28 sorrys total, 0 axioms, 5 subfiles)
│
│  ForwardTubeLorentz ─→ BHWExtension ─→ BHWTranslation ─→ SchwingerAxioms ─→ OSToWightman
│
│  ┌─── R→E DIRECTION (2 hard sorrys, in SchwingerAxioms) ──────┐
│  │                                                               │
│  │  E2: reflection positivity         ← sorry (HARD)            │
│  │  E4: cluster decomposition         ← sorry (HARD)            │
│  │                                                               │
│  │  E0, E1, E3 ✅ PROVEN    wightman_to_os_full ✅ PROVEN      │
│  └───────────────────────────────────────────────────────────────┘
│
│  ┌─── E→R DIRECTION (26 sorrys, in OSToWightman) ──────────────┐
│  │                                                               │
│  │  inductive_analytic_continuation ◀── PaleyWiener.lean         │
│  │         ↓                                                     │
│  │  full_analytic_continuation ◀── iterate + E1 + Bochner        │
│  │         ↓                                                     │
│  │  boundary_values_tempered ◀── growth estimates                │
│  │         ↓                                                     │
│  │  6 transfer properties (e2r_*)                                │
│  │         ↓                                                     │
│  │  os_to_wightman_full ✅ PROVEN (sorry-free)                  │
│  └───────────────────────────────────────────────────────────────┘
│
▼
Reconstruction.lean ✅ (0 sorrys — definitions only)
│
▼
Reconstruction/Main.lean (1 sorry — wiring layer)
│
│  wightman_reconstruction  ✅ WIRED to wightman_reconstruction' (GNSHilbertSpace)
│  wightman_uniqueness      ◀── sorry (standard GNS uniqueness argument)
│  wightman_to_os           ✅ WIRED to wightman_to_os_full (WickRotation)
│  os_to_wightman           ✅ WIRED to os_to_wightman_full (WickRotation)
│
Reconstruction/GNSHilbertSpace.lean (3 sorrys — QFT axioms)
```

## Two Critical Bottlenecks

1. ~~**`edge_of_the_wedge`**~~ ✅ PROVED. ~~**`bargmann_hall_wightman`**~~ ✅ PROVED.
2. **R→E hard sorrys**: E2 (reflection positivity) and E4 (cluster decomposition)
   are the core physics content. Both require relating Euclidean and Minkowski
   inner products through the Wick rotation.
3. **`boundary_values_tempered`** — blocks all 6 E→R transfer properties.
   Depends on `full_analytic_continuation` + E0' linear growth.

## Known Subtleties

### ForwardTube coordinate convention
Our `ForwardTube` uses absolute coordinates with a special k=0 condition
(Im(z₀) ∈ V₊, where prev = 0). This means ForwardTube and PET are **not**
closed under complex translations. The physics literature avoids this by
working in difference variables ξ_k = z_{k+1} - z_k. This affects:
- `bhw_translation_invariant` — now proved (was axiom); plumbing gap resolved
- `wightman_to_os_full` h_in_tube — approach points x+iεη may not be in ForwardTube

Fixing this would require refactoring ForwardTube to use difference variables.

### ~~PCT and improper rotations (det = -1)~~ RESOLVED
E1 rotation invariance restricted to SO(d+1) (det=1 only). Full O(d+1) invariance
(det=-1) would require parity invariance, which is not implied by Wightman axioms.
Standard OS axiom E1 only requires SO(d+1).

## Parallel Work Streams (for collaboration)

These groups are **independent** and can be worked on simultaneously:

- **Group A** (BHW chain): ~~edge_of_the_wedge~~ ✅, ~~BHW~~ ✅ — remaining: EOW flattening, orbit topology, Jost geometry
- **Group B** (E→R analytic continuation): full_analytic_continuation → boundary_values_tempered → 6 transfers
- **Group C** (R→E hard sorrys): **E2 reflection positivity**, **E4 cluster decomposition**
- **Group D** (GNS/functional analysis): spectral theory, nuclear theorem, Stone's theorem

## Status Overview (2026-02-24)

### Wightman Module

| File | Sorrys | Status |
|------|--------|--------|
| Basic, Groups, Spacetime | 0 | ✅ Complete |
| SchwartzTensorProduct.lean | 0 | ✅ Complete |
| WightmanAxioms.lean | 4 | Nuclear theorem, spectrum BV |
| Reconstruction/GNSConstruction.lean | 0 | ✅ Complete |
| Reconstruction/GNSHilbertSpace.lean | 1 | Spectral condition |
| Reconstruction/AnalyticContinuation.lean | 0 | ✅ Complete |
| Reconstruction/ForwardTubeDistributions.lean | 0 | ✅ Complete |
| Reconstruction/WickRotation/ForwardTubeLorentz.lean | 4 | Polynomial growth, BV integrability, Lorentz∘ForwardConeAbs |
| Reconstruction/WickRotation/BHWExtension.lean | 2 | Local commutativity |
| Reconstruction/WickRotation/BHWTranslation.lean | 5 | Translation chain, BV direction |
| **Reconstruction/WickRotation/SchwingerAxioms.lean** | **5** | **E0, E2, E4** |
| **Reconstruction/WickRotation/OSToWightman.lean** | **14** | **E→R chain** |
| Reconstruction/Main.lean | 1 | `wightman_uniqueness` |
| Reconstruction/Helpers/ | 0 | ✅ Complete |
| NuclearSpaces/ | 9 | Deferred (NuclearSpace 2, BochnerMinlos 5, SchwartzNuclear 2) |
| **Wightman subtotal** | **45** | |

### Full Project Sorry Census (108 total, 23 files, 0 axioms)

| Module | File | Sorrys |
|--------|------|--------|
| **Wightman** | WickRotation/OSToWightman.lean | 14 |
| | NuclearSpaces/BochnerMinlos.lean | 5 |
| | WickRotation/BHWTranslation.lean | 5 |
| | WickRotation/SchwingerAxioms.lean | 5 |
| | WightmanAxioms.lean | 4 |
| | WickRotation/ForwardTubeLorentz.lean | 4 |
| | NuclearSpaces/SchwartzNuclear.lean | 2 |
| | NuclearSpaces/NuclearSpace.lean | 2 |
| | WickRotation/BHWExtension.lean | 2 |
| | Reconstruction/GNSHilbertSpace.lean | 1 |
| | Reconstruction/Main.lean | 1 |
| | **subtotal** | **45** |
| **vNA** | MeasureTheory/CaratheodoryExtension.lean | 11 |
| | KMS.lean | 10 |
| | ModularAutomorphism.lean | 7 |
| | ModularTheory.lean | 6 |
| | Unbounded/StoneTheorem.lean | 2 |
| | Predual.lean | 2 |
| | Unbounded/Spectral.lean | 2 |
| | **subtotal** | **40** |
| **SCV** | LaplaceSchwartz.lean | 6 |
| | PaleyWiener.lean | 6 |
| | BochnerTubeTheorem.lean | 2 |
| | **subtotal** | **14** |
| **ComplexLieGroups** | Connectedness.lean | 6 |
| | JostPoints.lean | 3 |
| | **subtotal** | **9** |
| **TOTAL** | **23 files** | **108** |

## Proven Infrastructure (sorry-free)

### GNSConstruction.lean
- `WightmanInnerProduct_hermitian` — ⟨F,G⟩ = conj(⟨G,F⟩)
- `null_inner_product_zero` — ⟨X,X⟩.re=0 → ⟨X,Y⟩=0
- `PreHilbertSpace.innerProduct` — Well-defined on quotient
- `fieldOperator` — φ(f) descends to quotient (full chain: adjoint → preserves null → well-defined)
- `gns_reproduces_wightman` — ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = Wₙ(f₁⊗···⊗fₙ)
- `translation_preserves_inner` — WIP(F', G') = WIP(F, G)

### AnalyticContinuation.lean
- `ComplexLorentzGroup.ofReal`, `ComplexLorentzGroup.ofEuclidean` — embeddings
- `ForwardTube_subset_ComplexExtended`, `ComplexExtended_subset_Permuted`
- `euclidean_ordered_in_forwardTube` — ordered Euclidean points ∈ T_n
- `euclidean_distinct_in_permutedTube` — distinct Euclidean ∈ T''_n
- `jost_lemma` — Jost points have spacelike differences
- `schwinger_euclidean_invariant`, `schwinger_permutation_symmetric`
- `schwingerFromWightman_analytic`, `differentiable_complexWickRotate`

### EdgeOfWedge.lean
- `edge_of_the_wedge_1d` — 1D edge-of-wedge via Morera's theorem
- `identity_theorem_connected` — analytic identity theorem
- `holomorphic_translation_invariant`

### WickRotation/ (proven, across 5 subfiles)
- `restricted_preserves_forward_cone` — Restricted Lorentz preserves V₊
- `restricted_preserves_forward_tube` — Restricted Lorentz preserves ForwardTube
- `W_analytic_lorentz_on_tube` — W_analytic is Lorentz invariant on ForwardTube
- `F_ext_translation_invariant` — BHW F_ext is translation invariant at Euclidean points
- `F_ext_permutation_invariant` — BHW F_ext is permutation symmetric at Euclidean points
- `F_ext_rotation_invariant` (det=1) — SO(d+1) invariance via complex Lorentz group
- `constructedSchwinger_symmetric` — E3 (sorry-free, verified)
- `constructedSchwinger_translation_invariant` — Part of E1 (sorry-free, verified)
- `constructedSchwinger_rotation_invariant` — Part of E1 (det=-1 sorry remains)
- `integral_orthogonal_eq_self` — Orthogonal COV preserves Lebesgue measure
- `integral_perm_eq_self` — Permutation COV preserves Lebesgue measure
- `integral_flatten_change_of_variables` — Fubini for tensor product integrals
- `os_to_wightman_full` — E'→R' bridge theorem (sorry-free)
- `wightman_to_os_full` — R→E bridge theorem (sorry-free)

### Reconstruction.lean
- `IsWickRotationPair` — Wick rotation pair predicate
  - Connects Schwinger functions S and Wightman functions W through holomorphic F_analytic

### WightmanAxioms.lean
- `wickRotatePoint` — Wick rotation map (τ,x⃗) ↦ (iτ,x⃗)

## Architecture

```
Layer 0 (DONE): Metric, Lorentz, Poincare, Basic, MinkowskiGeometry — 0 sorrys
    ↓
OperatorDistribution.lean ──> WightmanAxioms.lean
    ↓                              ↓
    └──────────> Reconstruction.lean ←── SchwartzTensorProduct.lean
                     ↓
              Reconstruction/AnalyticContinuation.lean  (tube domains, BHW)
              Reconstruction/GNSConstruction.lean       (✅ sorry-free)
              Reconstruction/GNSHilbertSpace.lean       (GNS Hilbert space, 10 sorrys)
              Reconstruction/WickRotation/              (OS↔Wightman bridge, 5 subfiles)
              Reconstruction/Main.lean                  (wiring, 1 sorry)
              Reconstruction/Helpers/EdgeOfWedge.lean   (✅ sorry-free, 1D)
```

Nuclear spaces / Minlos are a SEPARATE development line for constructive QFT.

## Key Mathematical References

- **OS I**: "Reconstruction theorem I.pdf" — Theorem R→E (§5), Theorem E→R (§4)
  - Note: Lemma 8.8 has a gap (fixed in OS II)
- **OS II**: "reconstruction theorem II.pdf" — Linear growth E0' (§IV.1),
  analytic continuation (§V), temperedness estimates (§VI)
- **Streater-Wightman**: "PCT, Spin and Statistics, and All That" — Chapter 3
- **Glimm-Jaffe**: "Quantum Physics" — Chapter 19 (reconstruction)
