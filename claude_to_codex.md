# Development Recommendations for Codex Agent — OS Reconstruction Project

Last updated: 2026-02-27 (Blocker B analysis added below)

## 0. Critical Findings (Read First)

### BHW Axiom Has Been Eliminated

The `bargmann_hall_wightman` in `AnalyticContinuation.lean` is **no longer an axiom** — it is a proved theorem that delegates to `BHW.bargmann_hall_wightman_theorem` in `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean` via the `Bridge/AxiomBridge.lean` type conversion layer. The bridge is complete and sorry-free.

**There are zero `axiom` declarations and zero `sorryAx` in the entire project.** All remaining proof gaps are explicit `sorry` tactics.

**UPDATE (2026-02-27):** Blocker A (`orbitSet_isPreconnected`) is now **RESOLVED** —
`Core.lean` has 0 sorrys. Only **1 sorry** remains in ComplexLieGroups
(`PermutationFlow.lean:1490`). Closing this single sorry makes the BHW theorem
fully constructive.

### Outdated Documentation

Several existing docs are outdated and should not be fully trusted:
- `docs/PROOF_OUTLINE.md` — still describes BHW as a "named axiom" (line 309). It's now a theorem.
- `docs/bargmann_hall_wightman_gap_analysis.md` — describes BHW as "promoted to a named axiom." This has been resolved; the gap analysis documents historical context only.
- `docs/sorry_analysis.md` — last updated 2026-02-20, stale sorry counts.
- The existing `claude_for_codex.md` — only covers `orbitSet_isPreconnected`; superceded by this file.

### Corrected Sorry Census (verified via `grep '^\s*sorry\b'`)

**Total: 99 sorrys across 23 files** (not 100 as some TODOs state).

| Scope | Sorrys | Notes |
|-------|--------|-------|
| Wightman (critical path) | 34 | OSToWightman 14, SchwingerAxioms 5, BHWTranslation 5, WightmanAxioms 4, BHWExtension 2, ForwardTubeLorentz 2, GNSHilbertSpace 1, Main 1 |
| Wightman (non-critical) | 9 | NuclearSpaces: BochnerMinlos 5, NuclearSpace 2, SchwartzNuclear 2 |
| SCV | 14 | LaplaceSchwartz 6, PaleyWiener 6, BochnerTubeTheorem 2 |
| ComplexLieGroups | **1** | ~~Core.lean 1~~, PermutationFlow.lean 1 (Blocker A RESOLVED) |
| vNA (OFF CRITICAL PATH) | 40 | Do not work on |
| **Critical path total** | **50** | |

Key count corrections from earlier docs:
- `GNSHilbertSpace.lean`: **1 sorry** (not 3-4 as older docs claim — `spectrum_condition` and `cyclicity` were apparently closed or consolidated)
- `LorentzLieGroup.lean`: **0 sorrys** (grep false positive from comments)
- `GeodesicConvexity.lean`: **0 sorrys** (grep false positive from comments)
- `Analyticity.lean`: **0 sorrys** (grep false positive from comments)
- `IdentityTheorem.lean`: **0 sorrys** (fully proved)
- `AnalyticContinuation.lean`: **0 sorrys, 0 axioms** (BHW is now a theorem)

### The `[NeZero d]` Convention

The BHW theorem and all tube domain definitions require `[NeZero d]` (i.e., `d ≥ 1`, so spacetime is at least 1+1 dimensional). This is correct physics — the forward light cone is trivial in 0+1 dimensions. The bridge (`AxiomBridge.lean`) also carries this constraint. All downstream Wightman theorems inherit it via `variable {d : ℕ} [NeZero d]`.

### Bridge Architecture

`Bridge/AxiomBridge.lean` (252 lines, 0 sorrys) provides the type conversion layer between:
- `ComplexLieGroups/` types (uses `LorentzLieGroup.minkowskiSignature`, no `[NeZero d]` on internal types)
- `Wightman/` types (uses `MinkowskiSpace.metricSignature`, `[NeZero d]`)

Key bridge lemmas (all proved):
- `minkowskiSignature_eq_metricSignature` — signatures agree definitionally
- `lorentzGroupEquiv` — `LorentzLieGroup.LorentzGroup d ≃ LorentzGroup d`
- `restrictedLorentzGroupToWightman` / `wightmanToRestrictedLorentzGroup` — restricted group conversions
- `inOpenForwardCone_iff` — forward cone conditions agree
- `spacelike_condition_iff` — spacelike conditions agree
- `BHW_forwardTube_eq` / `BHW_permutedExtendedTube_eq` — tube domain set equalities

This bridge is **critical infrastructure**. If any definitions in either module change, the bridge must be updated.

---

## 1. Project Overview

This is a Lean 4 formalization of the **Osterwalder-Schrader reconstruction theorem**, establishing mathematical equivalence between Wightman QFT (Lorentzian) and Euclidean QFT (Schwinger functions). The codebase has ~65,000 lines across ~100 `.lean` files in four modules:

| Module | Lines | Sorrys | Role |
|--------|-------|--------|------|
| `Wightman/` | ~20k | 43 (34 critical + 9 nuclear) | QFT axioms, GNS construction, Wick rotation bridge |
| `SCV/` | ~10k | 14 | Several complex variables (edge-of-wedge, Paley-Wiener) |
| `ComplexLieGroups/` | ~15k | 2 | Complex Lie group theory for BHW theorem |
| `vNA/` | ~13k | 40 | Von Neumann algebras (NOT on critical path, deprioritize) |

**Critical path sorry count: 50** (out of 99 total). The vNA module (40 sorrys) is off the critical path entirely. The 9 NuclearSpaces sorrys in Wightman are also non-critical.

---

## 2. Architecture & Dependency Flow

```
Layer 0: Foundations (0 sorrys) ✓
  Spacetime, Lorentz/Poincare groups, Schwartz tensor products

Layer 1: Axiom Systems (4 sorrys, non-blocking)
  WightmanAxioms.lean — nuclear theorem placeholders

Layer 2: GNS Construction (0 sorrys) ✓
  GNSConstruction.lean — complete

Layer 3: Complex Analysis (0 sorrys) ✓
  1D edge-of-wedge, Osgood's lemma, Cauchy integral parameter

Layer 4: Analytic Continuation (0 sorrys, 0 axioms) ✓
  edge_of_the_wedge — PROVED (delegates to SCV/TubeDomainExtension)
  bargmann_hall_wightman — PROVED (delegates to ComplexLieGroups via Bridge/AxiomBridge)
  NOTE: Both former axioms are now theorems. BHW propagates 2 sorrys from ComplexLieGroups.

Layer 5: Wick Rotation Bridge (~34 sorrys)
  R→E direction: SchwingerAxioms (5), BHWTranslation (5), BHWExtension (2), ForwardTubeLorentz (2)
  E'→R' direction: OSToWightman (14)
  SCV support: PaleyWiener (6), LaplaceSchwartz (6), BochnerTubeTheorem (2)

Layer 6: Main Theorems (6 sorrys)
  GNSHilbertSpace (3), Main (1), WightmanAxioms non-blocking (4)
```

**The two main theorem targets:**
- `wightman_to_os` (R→E): Wightman functions → OS axioms via Wick rotation
- `os_to_wightman` (E'→R'): OS axioms → Wightman functions via analytic continuation

---

## 3. Root Blockers (Highest Priority)

### Blocker A: `orbitSet_isPreconnected` — **RESOLVED** ✓

**File:** `ComplexLieGroups/Connectedness/ComplexInvariance/Core.lean`
**Status:** FULLY RESOLVED — 0 sorrys in Core.lean.
The full orbit connectivity chain is complete through `orbitSet_onePoint_isPreconnected`.
This was confirmed by grep: zero `sorry` occurrences in Core.lean.

Key proved results:
- `nonemptyDomain_isPreconnected` (Core.lean:1388): {Λ|∃w∈FT,Λ·w∈FT} preconnected
- `orbitSet_onePoint_isPreconnected` (Core.lean:1207): n=1 orbit sets preconnected
- `complex_lorentz_invariance` (Extend.lean:115): fully proved

### Blocker B: `iterated_eow_permutation_extension` — **1 SORRY REMAINING**

**File:** `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean:1490`
**Goal:** For `d > 0, n ≥ 2, σ ≠ 1`, prove:
```lean
∀ z, z ∈ ExtendedTube d n →
  (fun k => z (σ k)) ∈ ExtendedTube d n →
  extendF F (fun k => z (σ k)) = extendF F z
```
**Why it matters:** Blocks `F_permutation_invariance` → blocks BHW Property 4.

**Current state:**
- `n ≤ 1`: proved (trivial permutation)
- `σ = 1`: proved (identity)
- `d = 0`: proved (`coreExtendedTube_perm_overlap_d0_forces_perm_one_general` forces σ=1)
- `d ≥ 1, n ≥ 2, σ ≠ 1`: **OPEN** — the remaining sorry

**Architectural issue discovered:** `eow_chain_adj_swap` (line 1574) does NOT use
its induction hypothesis `_ih_σ`. The adj-swap induction in `F_permutation_invariance`
is vacuous — each step calls `iterated_eow_permutation_extension` for the full
composed permutation τ = swap * σ₀. So the sorry must be filled for arbitrary σ.

**Available infrastructure (all 0 sorrys):**

| File | Key results |
|------|-------------|
| `Adjacency.lean` | `adjSwapForwardOverlap_nonempty`, `extendF_adjSwap_eq_of_connected_forwardOverlap_hd2`, `isConnected_adjSwapForwardOverlapSet_of_indexConnected` |
| `PermutedTubeConnected.lean` | `permutedExtendedTube_isPreconnected`, `adjacent_sectors_overlap_right` |
| `AdjacentOverlapWitness.lean` | `adjacent_overlap_witness_exists`, `adjacent_overlap_real_spacelike_witness_exists`, `spatialRotCLG12` |
| `PermutationFlow.lean` | `hExtPerm_of_geometric`, `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`, `permInvariance_forwardTube_iff_extendF_overlap` |

**Root sub-blocker: adjSwapForwardOverlapSet connectivity.** All proof routes
ultimately need `IsConnected (adjSwapForwardOverlapSet n i hi)`:
```lean
{w ∈ ForwardTube d n | (fun k => w (swap(i, i+1) k)) ∈ ExtendedTube d n}
```

**Four approaches to connectivity (in order of preference):**

1. **AFOS = FT for d ≥ 2** (strongest, simplest if true):
   Prove `∀ w ∈ ForwardTube, swap·w ∈ ExtendedTube` when d ≥ 2.
   Then AFOS = FT is convex hence connected. The geometric argument:
   swap·w has Im(w_i - w_{i+1}) ∈ -V+ at the swapped position. For d ≥ 2,
   a complex rotation in the (1,2) spatial plane (`spatialRotCLG12` in
   `AdjacentOverlapWitness.lean`) can flip this into V+. This is the same
   rotation used in the witness construction.

2. **Adapt `nonemptyDomain_isPreconnected` pattern**:
   Express `adjSwapForwardOverlapIndexSet = ⋃_{w∈FT} orbitSet(swap·w)` and
   use `isPreconnected_sUnion` with orbit set preconnectedness. Needs
   all orbit sets to share a common point (e.g., identity).

3. **Double-coset generation** (existing reduction):
   Prove `∀ Λ ∈ indexSet, ∃ R₁ R₂, Λ = R₁·Λ₀·R₂` using polar decomposition.
   Plugs into `isConnected_adjSwapForwardOverlapSet_of_real_double_coset_generation`.

4. **PET connectivity + sheaf patching** (avoids overlap connectivity):
   Use `isConnected_permutedExtendedTube` and the fact that adj-swap F_π functions
   agree on pairwise overlaps. Requires careful identity theorem argument on sectors.

**For d = 1:** Separate handling needed (JostSet ⊄ ET counterexample exists).
The adj-swap overlap is nonempty (`adjSwapForwardOverlap_nonempty` proved for d=1
using `wickPlus1` Wick rotation). Connectivity needs a direct argument for
SO(1,1;ℂ) ≅ ℂ*.

**Composition step (general σ from adjacent swaps):**
Given adj-swap extendF invariance, compose via identity theorem:
- D_full = {z ∈ ET | all partial products σ_j·z ∈ ET} (open, nonempty for d≥2)
- On D_full: chain adj-swap equalities
- D_σ = {z ∈ ET | σ·z ∈ ET} connected (from forward overlap connectivity)
- Identity theorem: f = g on connected D_σ

**BREAKTHROUGH: Jost witness construction for d ≥ 2 (bypasses counterexample)**

The counterexample shows JostSet ⊄ ET for all d ≥ 1. But we only need ONE Jost point
in ET ∩ σ⁻¹·ET per permutation σ. For d ≥ 2, here's how:

**Construction:** For any σ ∈ S_n and d ≥ 2, define:
```
x_k = (0, (k+1)·a, (σ⁻¹(k)+1)·b, 0, ..., 0)  for a, b > 0
```
This uses TWO spatial dimensions to simultaneously encode two orderings:
- Coordinate 1 encodes the natural order: (k+1)·a increases with k
- Coordinate 2 encodes the σ-order: (σ⁻¹(k)+1)·b increases when reindexed by σ

**Verification (all conditions met):**
1. **x ∈ JostSet**: All differences x_i - x_j = (0, (i-j)a, (σ⁻¹(i)-σ⁻¹(j))b, 0,...) are purely spatial, so Minkowski norm = (i-j)²a² + (σ⁻¹(i)-σ⁻¹(j))²b² > 0 for i ≠ j. ✓
2. **x ∈ ForwardJostSet** (existing def in JostPoints.lean): |consecutiveDiff(x,k)₀| = 0 < consecutiveDiff(x,k)₁ = a. So `forwardJostSet_subset_extendedTube` gives realEmbed(x) ∈ ET. ✓
3. **realEmbed(x∘σ) ∈ ET**: Use a Wick rotation in the **(0,2) plane** (NOT the standard (0,1)).
   (x∘σ)_k = x_{σ(k)} = (0, (σ(k)+1)a, (k+1)b, 0,...).
   Consecutive differences in coordinate 2: (k+1)b - kb = b > 0.
   The (0,2) Wick rotation maps Im of this to ((k+1)b, 0, ...) ∈ V⁺. ✓

**Implementation needs:**
- A generalized `wickMatrix_j` for the (0,j) Wick rotation (currently only (0,1) exists)
- A generalized `forwardJostSet_j` requiring |ζ₀| < ζ_j (currently only j=1)
- Corresponding `forwardJostSet_j_subset_extendedTube` theorem
- Construction of x_k and verification of JostSet membership

This provides obligation (1) of `hExtPerm_of_geometric` for d ≥ 2.

**Remaining for the sorry closure:**
- Obligation (2): `permForwardOverlapSet` connectivity (or double-coset generation)
- d = 1 case: needs separate handling (only 1 spatial dimension, can't use two-axis trick)

**Alternative route using `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`:**
With the Jost witness in hand, the sorry reduces to proving:
```lean
IsConnected (permForwardOverlapSet (d := d) n σ)
```
The existing reduction chain is: index set connected → forward overlap set connected.
Index set connectivity can potentially use the KAK decomposition of SO(1,d;ℂ) w.r.t.
SO⁺(1,d;ℝ), which has rank 1 for d ≥ 1. This means every element factors as
R₁·exp(iθL₀₁)·R₂, giving a 1-parameter family connecting any two elements.

**Key no-go results (do NOT pursue):**
- Midpoint-implication route — FALSE (`test/midpoint_condition_counterexample_test.lean`)
- Global `JostSet ⊆ ExtendedTube` — FALSE for ALL d ≥ 1 (`test/jostset_et_counterexample_test.lean:248`)
- ForwardJostSet witness for d=1 — provably impossible (Section 7 of `test/proofideas_blockerB_permutation.lean`)
- Direct ForwardTube perm invariance — FALSE (swap·FT ⊄ FT for nontrivial swaps)
- AFOS = FT — FALSE (purely imaginary time-aligned FT points have no Λ fixing swap, shown by contradiction on Re(Λ₀₀) sign)

**Estimated effort:** 300-500 lines (Jost witness + generalized Wick + connectivity argument).

---

## 4. Priority Execution Order

### Tier 1: Root Blockers

| Priority | Task | File(s) | Sorrys | Effort |
|----------|------|---------|--------|--------|
| ~~**1a**~~ | ~~Close `orbitSet_isPreconnected` (d≥2)~~ | ~~`Core.lean`~~ | ~~1~~ | **RESOLVED** ✓ |
| **1b** | Close `iterated_eow_permutation_extension` | `PermutationFlow.lean` | 1 | 300-500 LOC |

**Blocker 1b is now the SOLE remaining BHW sorry.** See Blocker B analysis above.

### Tier 2: SCV Continuation Chain (parallelizable with Tier 1)

| Priority | Task | File(s) | Sorrys | Notes |
|----------|------|---------|--------|-------|
| **2a** | Fourier-Laplace boundary theory | `SCV/LaplaceSchwartz.lean` | 6 | Vladimirov §25-26 estimates |
| **2b** | Paley-Wiener theorems | `SCV/PaleyWiener.lean` | 6 | Depends on 2a partially |
| **2c** | Bochner tube theorem | `SCV/BochnerTubeTheorem.lean` | 2 | Cauchy integral + monodromy |

**Key dependency:** `paley_wiener_half_line` (P1) is the load-bearing sorry — it blocks 5 other PW sorrys. `fourierLaplace_continuousWithinAt` (L1) is the load-bearing sorry in LaplaceSchwartz — blocks 4 others.

### Tier 3: R→E Wick Rotation Chain

| Priority | Task | File(s) | Sorrys | Dependencies |
|----------|------|---------|--------|--------------|
| **3a** | Forward tube polynomial growth | `ForwardTubeLorentz.lean` | 2 | SCV polydisc Cauchy |
| **3b** | BHW extension infrastructure | `BHWExtension.lean` | 2 | EOW theorem, BV theory |
| **3c** | BHW translation chain | `BHWTranslation.lean` | 5 | 3a, difference coordinates |
| **3d** | Schwinger axiom verification | `SchwingerAxioms.lean` | 5 | 3a, 3b, 3c, BHW axiom |

### Tier 4: E'→R' Transfer Chain

| Priority | Task | File(s) | Sorrys | Dependencies |
|----------|------|---------|--------|--------------|
| **4a** | Inductive analytic continuation | `OSToWightman.lean:154` | 1 | PW one-step (2b) |
| **4b** | Iterated continuation | `OSToWightman.lean:176` | 1 | 4a |
| **4c** | Schwinger holomorphic extraction | `OSToWightman.lean:189` | 1 | Distribution theory |
| **4d** | Forward tube via Bochner | `OSToWightman.lean:204` | 1 | BochnerTubeTheorem (2c) |
| **4e** | BV tempered distributions | `OSToWightman.lean:273` | 1 | PW + FL theory (2a, 2b) |
| **4f** | Property transfers (8 sorrys) | `OSToWightman.lean:409-650` | 8 | 4e, BHW, EOW |

### Tier 5: Wiring & Cleanup

| Priority | Task | File(s) | Sorrys |
|----------|------|---------|--------|
| **5a** | `wightman_uniqueness` | `Main.lean:80` | 1 |
| **5b** | `vacuum_unique` part 2 (Stone's thm) | `GNSHilbertSpace.lean:912` | 1 |

Note: `spectrum_condition` and `cyclicity` (previously listed as sorrys) have been closed.

---

## 5. Load-Bearing Sorrys (Impact Analysis)

These sorrys, if proved, would unblock the most downstream progress:

| Sorry | File:Line | Downstream Unblocks |
|-------|-----------|---------------------|
| `paley_wiener_half_line` | `PaleyWiener.lean:215` | 5 PW sorrys + `inductive_analytic_continuation` + `forward_tube_bv_tempered` |
| `fourierLaplace_continuousWithinAt` | `LaplaceSchwartz.lean:109` | 4 FL sorrys + `spectrum_implies_distributional_bv` |
| `polynomial_growth_on_slice` | `ForwardTubeLorentz.lean:332` | BV integrability, direction independence, PET growth, Schwinger E0 |
| `forward_tube_bv_tempered` | `OSToWightman.lean:273` | All 8 property transfers in OSToWightman |
| `bochner_local_extension` | `BochnerTubeTheorem.lean:111` | `extend_to_forward_tube_via_bochner` + full analytic continuation |
| `hjoin` (orbitSet) | `Core.lean:1277` | `complex_lorentz_invariance` → BHW axiom elimination |
| `hExtPerm` (perm extension) | `PermutationFlow.lean:1428` | `F_permutation_invariance` → BHW Property 4 |

---

## 6. Sorry-by-Sorry Technical Notes

### SCV/LaplaceSchwartz.lean (6 sorrys)

All 6 sorrys concern Fourier-Laplace representation theory (Vladimirov §25-26). The core challenge is formalizing the connection between tempered distributions and their Fourier-Laplace transforms on tube domains.

- **L1** `fourierLaplace_continuousWithinAt` (line 109): DCT with the Laplace integrand converging as Im(z) → 0. Needs dominated convergence for distribution pairings.
- **L2** `fourierLaplace_uniform_bound_near_boundary` (line 232): Polynomial growth from the Laplace integral + compactness argument. Uses L1.
- **L3** `fourierLaplace_polynomial_growth` (line 360): Compact subset growth bound. Streater-Wightman Theorem 2-6.
- **L4** `polynomial_growth_of_continuous_bv` (line 389): Growth from continuous BV. Derives from FL representation.
- **L5** `fourierLaplace_boundary_continuous` (line 440): Boundary continuity. Uses L1.
- **L6** `fourierLaplace_boundary_integral_convergence` (line 535): Weighted L¹ integrability. Technical but straightforward if L2 is available.

**Recommended attack:** Prove L1 first (the foundation), then L2 and L3 in parallel, then L4-L6 follow.

### SCV/PaleyWiener.lean (6 sorrys)

The Paley-Wiener theorem chain for one-sided Fourier support → holomorphic extension to half-planes/tube domains.

- **P1** `paley_wiener_half_line` (line 215): Core 1D PW theorem. If T ∈ S'(ℝ) has Fourier support in [0,∞), its FL transform extends to upper half-plane. Reed-Simon II Theorem IX.16.
- **P2** `paley_wiener_cone` (line 251): Multi-D generalization to cones. Vladimirov Theorem 25.1.
- **P3** `paley_wiener_converse` (line 290): Converse: holomorphic on tube + growth → support in dual cone.
- **P4** `paley_wiener_one_step` (line 351): OS II inductive step. Uses P1 + Osgood's lemma.
- **P5** `paley_wiener_one_step_simple` (line 382): 1D slice variant of P4. Directly uses P1.
- **P6** `paley_wiener_unique` (line 412): Uniqueness. Bridges 1D into general tube framework.

**Recommended attack:** Prove P1 first (load-bearing), then P2 and P5 can proceed in parallel. P4 needs P1 + Osgood (already proved). P3 and P6 are independent.

### SCV/BochnerTubeTheorem.lean (2 sorrys)

- **B1** `bochner_local_extension` (line 111): Cauchy integral on polydisc with distinguished boundary in T(C). Core construction. Needs `SCV.IteratedCauchyIntegral` (proved) + convex hull geometry.
- **B2** `h_consistency` inside `holomorphic_extension_from_local` (line 206): Monodromy/sheaf-gluing. Path-connect through overlapping local extensions, identity theorem at each overlap. Needs path-connectedness of open connected sets in ℂᵐ.

**Recommended attack:** B1 first (the hard analytic content), then B2 (more topological, uses identity theorem which is proved).

### WickRotation/ForwardTubeLorentz.lean (2 sorrys)

- **polynomial_growth_on_slice** (line 332): Cauchy formula on polydiscs centered at x + iεη. The ε margin places the polydisc inside the tube. Available: `SCV.IteratedCauchyIntegral`, `SCV.Polydisc`. Just needs the bridge to apply Cauchy estimates in the tube domain setting.
- **wickRotation_not_in_PET_null** (line 719): Complement of PET under Wick rotation has measure zero. Needs Jost characterization + algebraic subvariety measure zero. Lower priority.

### WickRotation/BHWExtension.lean (2 sorrys)

- **W_analytic_swap_distributional_agree** (line 89): BVs of W_analytic and W_analytic∘swap agree on spacelike supports. Needs backward-cone analysis.
- **analytic_boundary_local_commutativity** (line 120): g(z) = W_analytic(swap(z)) - W_analytic(z) has zero distributional BV → g = 0 by identity theorem. Needs multi-tube EOW application.

**Note:** These are only needed for eliminating the BHW axiom constructively. If BHW remains an axiom, these are not on the critical path.

### WickRotation/BHWTranslation.lean (5 sorrys)

- **forwardTube_lorentz_translate_aux_core** (line 216): PET translation closure. Needs difference-coordinate bridge.
- **W_analytic_translated_bv_eq** (line 316): BV of translated function. Needs COV + direction independence.
- **forward_tube_bv_integrable_translated** (line 339): Integrability of translated Schwartz integral. Needs `polynomial_growth_on_slice`.
- **distributional_uniqueness_forwardTube_inter** (line 478): Distributional uniqueness on tube intersection. Routine transfer from `distributional_uniqueness_tube`.
- **bv_limit_constant_along_convex_path** (line 825): Direction independence of BV limits. Vladimirov Ch. 12. Hard analysis.

### WickRotation/SchwingerAxioms.lean (5 sorrys)

- **polynomial_growth_forwardTube_full** (line 58): Full Vladimirov growth estimate. Needs FL representation.
- **polynomial_growth_on_PET** (line 81): PET growth. Combines above with BHW invariance.
- **schwinger_os_term_eq_wightman_term** (line 648): OS inner product = Wightman inner product. Deep BV correspondence.
- **bhw_pointwise_cluster_euclidean** (line 777): Pointwise cluster at Euclidean points.
- **W_analytic_cluster_integral** (line 813): Integral cluster. DCT with polynomial growth.

### WickRotation/OSToWightman.lean (14 sorrys)

The E'→R' transfer chain. The 14 sorrys decompose into:
- **Analytic continuation chain** (4 sorrys): `inductive_analytic_continuation`, `iterated_analytic_continuation`, `schwinger_holomorphic_on_base_region`, `extend_to_forward_tube_via_bochner` + 2 integration sorrys
- **BV extraction** (1 sorry): `forward_tube_bv_tempered` — THE load-bearing sorry
- **Property transfers** (8 sorrys): Each transfers one Wightman axiom from the Euclidean side. All blocked by `forward_tube_bv_tempered`.
- **Cluster** (1 sorry): `bvt_cluster`

### GNSHilbertSpace.lean (1 sorry — reduced from 3-4 in earlier docs)

Previously documented as having 3-4 sorrys (`spectrum_condition`, `cyclicity`, `vacuum_unique`), but `spectrum_condition` and `cyclicity` have been closed. Only one remains:

- **`vacuum_unique` part 2** (line 912): Any time-translation-invariant vector is proportional to Omega. Needs Stone's theorem (H = P₀ as self-adjoint generator) + spectral theory (σ(H) ⊆ [0,∞) → ker(H) = ℂ·Ω). Blocked by missing Mathlib infrastructure.

This is lower priority — the reconstruction theorems can be stated without it.

---

## 7. Parallelization Strategy

Three independent workstreams can proceed simultaneously:

```
Stream A: ComplexLieGroups blockers
  orbitSet_isPreconnected (Blocker A)
  iterated_eow_permutation_extension (Blocker B)

Stream B: SCV/Fourier-Laplace chain
  LaplaceSchwartz L1→L2→L3→L4→L5→L6
  PaleyWiener P1→P2,P5→P4→P3,P6
  BochnerTubeTheorem B1→B2

Stream C: WickRotation (depends on A and B)
  ForwardTubeLorentz → BHWExtension → BHWTranslation → SchwingerAxioms
  Then: OSToWightman property transfers
  Then: Main.lean wiring
```

Stream A and Stream B are fully independent. Stream C depends on both.

---

## 8. Import Architecture & Risks

### Module Dependency Graph (no circular imports)

```
SCV/ ──────────────────────────────────────┐
  (pure math, Mathlib only)                │
                                           ▼
ComplexLieGroups/ ──────────────┐     Bridge/AxiomBridge.lean
  (pure math, Mathlib only)     │          │
                                ▼          ▼
                        Wightman/Reconstruction/AnalyticContinuation.lean
                                │
                                ▼
                        Wightman/Reconstruction/WickRotation/*
                                │
                                ▼
                        Wightman/Reconstruction/Main.lean
```

**Bridge imports** (AxiomBridge.lean):
- `ComplexLieGroups.Connectedness` — the BHW theorem
- `SCV.TubeDomainExtension` — the EOW theorem
- `Wightman.Spacetime.Metric` — lightweight metric defs
- `Wightman.Groups.Lorentz` — lightweight Lorentz group defs

**Critical constraint:** AxiomBridge does NOT import `AnalyticContinuation.lean` or any heavy Wightman file, avoiding circular imports. Any new infrastructure should respect this.

### Potential Risks

1. **Definition drift:** The `ComplexLieGroups` module defines its own `LorentzGroup`, `ComplexLorentzGroup`, `ForwardTube`, etc. independently of `Wightman/`. The bridge lemmas establish equivalence. If definitions change on either side, the bridge must be updated and reverified.

2. **Type universe issues:** The `ComplexLorentzGroup` is a `Subtype` of matrices. Lean auto-derives some instances but not all. If you need new typeclass instances (e.g., `CompactSpace`, `LocallyCompactSpace`), they must be proved explicitly.

3. **`[NeZero d]` propagation:** Most theorems require `d ≥ 1`. If you write a lemma without `[NeZero d]`, it won't have access to BHW or tube domain infrastructure. Always include this constraint when working on Wightman-level theorems.

4. **Large file risk:** `PermutationFlow.lean` (1856 lines) and `Core.lean` (1466 lines) are getting large. Consider factoring helper lemmas into new files in the `Connectedness/` subdirectory if adding substantial new infrastructure.

---

## 9. Key Codebase Conventions & Rules (IMPORTANT)

### Absolute Rules (from CLAUDE.md)
1. **No axioms.** Never use `axiom` keyword. The one named axiom (`bargmann_hall_wightman`) is being actively eliminated.
2. **No axiom smuggling.** Do not bundle computational results into structures/definitions.
3. **No simplified definitions.** A "simplified" definition is a wrong definition.
4. **No placeholders.** Avoid `.choose`, `True := trivial`, or arbitrary choices.
5. **No `sorry` regression.** Never revert to sorry when facing complexity. Develop infrastructure instead.
6. **No `lake build` alone.** Use `lake build OSReconstruction.Wightman` or `lake build OSReconstruction.SCV` etc. Never `lake clean`.

### Build Commands
```bash
lake build OSReconstruction.Wightman          # Wightman module
lake build OSReconstruction.SCV               # SCV module
lake build OSReconstruction.ComplexLieGroups   # Lie groups module
```

### Development Workflow
- **Search Mathlib first** before writing infrastructure. Use `#check`, `exact?`, `apply?`.
- **Search local imports** in `OSReconstruction/` to avoid duplication.
- **Test in `test/` first.** Develop proofs in `test/*.lean`, compile there, port to working files only after stable.
- **Document proof ideas** in `test/proofideas_*.lean` when making partial progress.
- **Update TODO.md** files when closing sorrys.
- **Refactor large files** into subfolders when they exceed ~1500 lines.

### Mathlib API Gotchas
- `Complex.ofReal` is a plain function, NOT a ring hom — use `Complex.ofRealHom` for ring hom
- `abs_add` → `abs_add_le` (renamed)
- `differentiable_pi` is now an iff — use `differentiable_pi.mpr`
- `push_cast` needed before `ring` for ℝ→ℂ casts
- `inv_ne_zero` is forward-only — use `apply` not `rw`
- `contDiff_apply` needs explicit named args `(𝕜 := ℂ) (ι := Fin n) (E := ℂ)`

### Lean 4 Patterns
- `𝓘(ℂ, E)` notation requires `open scoped Manifold`
- `IsTopologicalGroup` not `TopologicalGroup` (renamed)
- `Matrix.diagonal_transpose` not `Matrix.transpose_diagonal`
- For structure equality: `cases a; simp [...]` instead of `ext i j`
- `set R := r (Fin.last m)` needs `simp only [R]` to unfold before `ring`

---

## 10. Key Mathematical References

| Reference | Used for | Sorrys it helps with |
|-----------|----------|----------------------|
| Vladimirov, *Methods of the Theory of Generalized Functions*, §25-26 | Fourier-Laplace theory, polynomial growth, BV limits | L1-L6, polynomial_growth_on_slice, bv_limit_constant, forward_tube_bv_tempered |
| Reed-Simon II, Theorem IX.16 | Paley-Wiener half-line | P1, P5 |
| Hormander, *Analysis of PDEs I*, Theorem 7.4.3 | PW for cones | P2, P3 |
| Hormander, *Intro to CV*, Theorem 2.5.10 | Bochner tube theorem | B1, B2 |
| Osterwalder-Schrader II (1975), §IV-V | Inductive analytic continuation | inductive/iterated_analytic_continuation |
| Streater-Wightman, *PCT, Spin and Statistics*, Ch. 2-3 | BHW theorem, Jost lemma | orbitSet_isPreconnected, complex_lorentz_invariance |
| Jost (1957) | Geodesic convexity | orbitSet_isPreconnected |
| Borchers-Epstein-Glaser (1967) | Fiber bundle approach to orbits | Alternative to geodesic convexity |

Reference PDFs are in `/references/`. Use `python3 tools/read_references.py <filename>` to read them.

---

## 11. What NOT to Work On

- **vNA module** — Not on the critical path. 40 sorrys but none block OS reconstruction.
- **NuclearSpaces/** — Not on the critical path. Schwartz nuclear theorem is a deep infrastructure gap.
- **Stone's theorem** — Needed for `spectrum_condition` and `vacuum_unique` in GNSHilbertSpace, but these don't block the main theorems.
- **Midpoint-implication route** for permutation extension — Proved FALSE.
- **Global `JostSet ⊆ ExtendedTube`** — Proved FALSE for n=3, d≥1.
- **Global geodesic convexity** (endpoint implies interior) — Counterexampled.

---

## 12. Quick Wins (Low-Hanging Fruit)

These sorrys are relatively straightforward and could be closed quickly:

1. **`distributional_uniqueness_forwardTube_inter`** (BHWTranslation.lean:478) — Routine transfer from existing `distributional_uniqueness_tube`. The intersection is a tube domain; just identify the cone.

2. **`bv_zero_point_is_evaluation`** (OSToWightman.lean:409) — For n=0, integral over trivial domain equals evaluation at 0.

3. **`paley_wiener_unique`** (PaleyWiener.lean:412) — Bridge 1D case into existing general tube framework via `distributional_uniqueness_tube`.

4. **`iterated_analytic_continuation`** (OSToWightman.lean:176) — Pure iteration plumbing once `inductive_analytic_continuation` is proved.

5. **`wightman_uniqueness`** (Main.lean:80) — Standard GNS uniqueness. Needs cyclicity (which is sorry'd) but the argument itself is mechanical.

---

## 13. File Map (Critical Path Only)

```
OSReconstruction/
├── SCV/
│   ├── LaplaceSchwartz.lean        ← 6 sorrys (FL theory, Tier 2a)
│   ├── PaleyWiener.lean            ← 6 sorrys (PW theorems, Tier 2b)
│   ├── BochnerTubeTheorem.lean     ← 2 sorrys (tube extension, Tier 2c)
│   ├── TubeDomainExtension.lean    ← 0 sorrys ✓ (EOW proved)
│   ├── IdentityTheorem.lean        ← 0 sorrys ✓
│   ├── Analyticity.lean            ← 0 sorrys ✓
│   └── [other files ✓]
│
├── ComplexLieGroups/
│   ├── Connectedness/
│   │   ├── ComplexInvariance/
│   │   │   ├── Core.lean           ← 1 sorry (orbitSet, Tier 1a)
│   │   │   ├── StabilizerI0.lean   ← 0 sorrys ✓ (stabilizer infra)
│   │   │   └── Extend.lean         ← 0 sorrys ✓
│   │   ├── BHWPermutation/
│   │   │   ├── PermutationFlow.lean ← 1 sorry (hExtPerm, Tier 1b)
│   │   │   └── Adjacency.lean      ← 0 sorrys ✓
│   │   └── [other subfiles ✓]
│   ├── D1OrbitSet.lean             ← 0 sorrys ✓ (d=1 model)
│   ├── Complexification.lean       ← 0 sorrys ✓
│   ├── SOConnected.lean            ← 0 sorrys ✓
│   └── [other files ✓]
│
├── Wightman/
│   ├── Reconstruction/
│   │   ├── WickRotation/
│   │   │   ├── ForwardTubeLorentz.lean  ← 2 sorrys (Tier 3a)
│   │   │   ├── BHWExtension.lean        ← 2 sorrys (Tier 3b)
│   │   │   ├── BHWTranslation.lean      ← 5 sorrys (Tier 3c)
│   │   │   ├── SchwingerAxioms.lean     ← 5 sorrys (Tier 3d)
│   │   │   └── OSToWightman.lean        ← 14 sorrys (Tier 4)
│   │   ├── GNSHilbertSpace.lean         ← 3 sorrys (Tier 5)
│   │   ├── Main.lean                    ← 1 sorry (Tier 5)
│   │   ├── AnalyticContinuation.lean    ← 0 sorrys ✓ (+ 1 axiom)
│   │   └── GNSConstruction.lean         ← 0 sorrys ✓
│   └── WightmanAxioms.lean              ← 4 sorrys (non-blocking)
│
└── test/                               ← 123 scratch/proofidea files
    ├── proofideas_orbit_preconnected.lean
    ├── proofideas_bhw_chain.lean
    ├── proofideas_connectedness_blockers_2026_02_26.lean
    └── [counterexample files]
```

---

## 14. Verification Checklist

After closing sorrys, verify with:

```bash
# Module-level builds
lake build OSReconstruction.SCV
lake build OSReconstruction.ComplexLieGroups
lake build OSReconstruction.Wightman

# Check no axiom leakage
grep -rn "^axiom " OSReconstruction/ --include="*.lean"
grep -rn "sorry" OSReconstruction/ --include="*.lean" | grep -v "^.*test/" | grep -v "^.*--"

# Update documentation
# - OSReconstruction/ComplexLieGroups/TODO.md
# - OSReconstruction/Wightman/TODO.md
# - OSReconstruction/SCV/TODO.md
```

---

## 15. Summary: Recommended Next Steps

1. **Start with Stream B** (SCV/Fourier-Laplace) — this is the most tractable and unblocks the most downstream work. Focus on `paley_wiener_half_line` and `fourierLaplace_continuousWithinAt` first.

2. **Work Stream A in parallel** (ComplexLieGroups blockers) — these are mathematically harder but have excellent infrastructure scaffolding already.

3. **Stream C** (WickRotation) becomes actionable once Stream B provides the SCV results. Within Stream C, `polynomial_growth_on_slice` → `forward_tube_bv_tempered` is the critical sub-chain.

4. **Quick wins** (`distributional_uniqueness_forwardTube_inter`, `bv_zero_point_is_evaluation`, `paley_wiener_unique`) can be knocked off early to build momentum.

5. **Do not touch vNA** unless explicitly asked. It's not on the critical path.

---

## 16. Deep Dive: Blocker A — `orbitSet_isPreconnected` (d ≥ 2)

**File:** `ComplexLieGroups/Connectedness/ComplexInvariance/Core.lean:1277`

### Exact Goal State

```
d n : ℕ
w : Fin n → Fin (d + 1) → ℂ
hw : w ∈ ForwardTube d n
hn : ¬n = 0, hd : ¬d = 1, h0 : ¬d = 0
hd2 : 2 ≤ d, hnz : n ≠ 0
⊢ ∀ Λ ∈ orbitSet w, JoinedIn (orbitSet w) 1 Λ
```

The target `orbitSet_isPreconnected_of_joinedIn_one` at line 1168 converts this `JoinedIn` goal into `IsPreconnected (orbitSet w)`.

### Critical n → 1 Reduction

`nonemptyDomain_eq_n1` (Core.lean:1332) proves that the union `U = {Λ | ∃w∈FT, Λw∈FT}` is the SAME for any `n > 0` as for `n = 1`. Then `nonemptyDomain_isPreconnected` decomposes `U` as a union of orbit sets sharing the identity, applying `isPreconnected_sUnion`. **So the sorry only blocks through `n = 1` orbit sets.**

For `n = 1`, the orbit set simplifies to:
```
O_w = {Λ ∈ SO⁺(1,d;ℂ) | InOpenForwardCone d (fun μ => (Λ·w 0 μ).im)}
```
i.e., Λ maps the single vector w into the forward light cone.

Furthermore, `exists_action_wScalarE0_of_forwardTube_one` (StabilizerI0.lean:77) shows every one-point FT config is a Lorentz image of `c·e₀` for some `c ≠ 0`. So the orbit set for generic `w` is conjugate to the orbit set of a canonical point.

### Three Proof Routes

#### Route 1: Quotient/Fiber (OrbitSetQuotient.lean)

Use `orbitSet_isPreconnected_of_stabilizer_connected_quotTube` (line 265):
```lean
-- Hypotheses:
-- (a) IsConnected (stabilizer w) — PROVED (StabilizerI0.lean:395)
-- (b) PreconnectedSpace (orbitQuotTube w) — UNPROVED
```

The stabilizer is fully proved connected for all one-point FT configurations. The missing piece is proving the quotient tube `orbitQuotTube w = {q ∈ G/Stab(w) | q·w ∈ FT}` is preconnected.

The quotient `G/Stab(w)` is the "mass shell" (complex quadric `{v : v·v = w·w}`). The tube intersection with this mass shell should be connected because:
- The mass shell is an irreducible algebraic variety
- The forward tube is a tube domain (convex imaginary part)
- Irreducible variety ∩ tube domain → connected (by a theorem on Stein manifolds)

**Gap:** Formalizing the algebraic geometry (irreducibility + Stein intersection).

#### Route 2: Double Coset (Core.lean:1187)

Use `orbitSet_isPreconnected_of_doubleCoset_generation_with_stabilizerPath`:
```lean
-- Hypotheses:
-- (a) ∃ Λ0 ∈ O_w with JoinedIn O_w 1 Λ0
-- (b) ∀ Λ ∈ O_w, ∃ R1 R2 : RestrictedLorentzGroup,
--     JoinedIn {S | S·w = w} 1 R2 ∧ Λ = ofReal R1 * Λ0 * ofReal R2
```

This is the KAK approach: every orbit element is R1·Λ0·R2 with real R1, R2 and R2 connected to identity in the stabilizer.

#### Route 3: Polar Decomposition + Geodesic Convexity (RECOMMENDED)

**Step 1: Polar decomposition** `Λ = R · exp(iY)` with `R ∈ SO↑₊(1,d;ℝ)` and `Y ∈ so(1,d;ℝ)`.
- This is the Cartan decomposition of the symmetric space `G_ℂ/G_ℝ`.
- Infrastructure: Use the Wick rotation (`toSOComplex`/`fromSOComplex` in Complexification.lean) to transfer from the known decomposition in `SO(d+1;ℂ) = SO(d+1;ℝ) · exp(i·so(d+1;ℝ))`.

**Step 2: Block diagonalization** of `Y` via spatial rotation conjugation:
```
Y' = Ad(S)(Y) = α·L₀₁ + Σⱼ βⱼ·L_{2j,2j+1}
```
These generators commute (disjoint coordinate pairs).

**Step 3: Geodesic convexity** for `exp(itY')·w`, `t ∈ [0,1]`:
- The ODE: `d²η/dt² = -Y'² η(t)`, where `η(t) = Im(exp(itY')·w)`.
- Block-diagonal `Y'²`: boost coords oscillatory (freq `α`), spatial coords hyperbolic (rate `βⱼ`).
- **Spatial rotation trick:** Choose `S` to put `Im(w)` in the `(0,1)`-plane, so `η_{2j}(0) = 0`.
- Then `η_{2j}(t) = B·sinh(βⱼt)` and **sinh convexity** gives `sinh(βt) ≤ t·sinh(β)`.
- Boost: `η₀(t) ± η₁(t) = C·sin(αt + φ)` with `α ∈ (-π, π)`. Endpoint positivity + half-period bound → positive throughout.
- **Result:** `η₀(t)² > η₁(t)² + Σ η_spatial(t)²` for `t ∈ [0,1]`.

**Step 4: Two-phase path construction**
- Phase 1: `t ↦ R(t)` from `I` to `R` in `SO↑₊(1,d;ℝ)` (preserves FT, path-connected).
- Phase 2: `t ↦ R·exp(itY)` from `R` to `Λ` (geodesic convexity + real R preserves V₊).

**Estimated size:** ~600-800 lines in 2-3 new files.

### Infrastructure Already Available

| Lemma | File | Status |
|-------|------|--------|
| `ComplexLorentzGroup.isPathConnected` | Complexification.lean | ✓ |
| `RestrictedLorentzGroup.isPathConnected` | LorentzLieGroup.lean | ✓ |
| `isConnected_stabilizer_of_forwardTube_one` | StabilizerI0.lean:395 | ✓ |
| `fromSOComplex`/`toSOComplex` | Complexification.lean | ✓ |
| `SOComplex.isConnected` | SOConnected.lean | ✓ |
| `orbitSet_isPreconnected_of_joinedIn_one` | Core.lean:1168 | ✓ |
| `nonemptyDomain_eq_n1` | Core.lean:1332 | ✓ |

### Infrastructure Needed (not in Mathlib)

1. **Polar decomposition** for `ComplexLorentzGroup`: `∀ Λ, ∃ R Y, Λ = ofReal(R) * exp(iY)`
2. **Block diagonalization** of `Y ∈ so(1,d;ℝ)` via spatial rotation
3. **Matrix exponential** `exp(iY) ∈ ComplexLorentzGroup` and continuity of `t ↦ exp(itY)`
4. **Geodesic convexity** theorem (ODE + sinh convexity + sine positivity)

### Dead Ends (DO NOT RETRY)

- Global geodesic endpoint implication (`t=0,1 ⟹ all t`) — FALSE, counterexample exists
- "Neighborhood generates group" (T is not a subgroup) — GAP
- `U = G` (total inversion `-I ∉ U`) — FALSE
- Streater-Wightman polar decomp without KAK (exp not surjective) — FLAWED for general d

### Detailed Proof Ideas

See `test/proofideas_blockerA_orbitSet.lean` and `test/proofideas_orbit_preconnected.lean` for full ODE derivation, sinh convexity argument, and all the detailed calculations.

---

## 17. Deep Dive: Blocker B — `iterated_eow_permutation_extension` (d>0, n≥2, σ≠1)

**File:** `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean:1428`

### Exact Goal State

```
hExtPerm_of_geometric :
  (∀ x ∈ JostSet d n, realEmbed x ∈ ExtendedTube d n) →
    (∃ Λ0 ∈ permForwardOverlapIndexSet n σ, ...) →
      ∀ z ∈ ExtendedTube d n, permAct σ z ∈ ExtendedTube d n →
        extendF F (permAct σ z) = extendF F z
⊢ ∀ z ∈ ExtendedTube d n, (fun k => z (σ k)) ∈ ExtendedTube d n →
    (extendF F fun k => z (σ k)) = extendF F z
```

The goal is definitionally equal to the conclusion of `hExtPerm_of_geometric`. So we need to supply its two hypotheses.

### CRITICAL FINDING: d=1 Obstruction

**The Jost-witness approach via ForwardJostSet is PROVABLY IMPOSSIBLE for d=1.**

In d=1 (1+1 Minkowski space), CLG(1) ≅ {exp(αK) : α ∈ ℂ} where K is the boost generator. For Λ = exp((a+ib)K) acting on a real spacelike vector v = (T, S):

```
η₀² − η₁² = sin²(b) · (S² − T²)
```

This identity shows the forward cone norm condition is automatic for spacelike vectors, reducing everything to a sign condition: for each consecutive diff (T_k, S_k), define f_k(u) = T_k·u − S_k where u = tanh(a) ∈ (−1,1). All f_k must have the same sign.

**For n=2, σ=swap(0,1), any x ∈ ForwardJostSet(1,2):**
- Permuted diff 0: f'₀(u) = t₁·u − s₁, always negative (root |s₁/t₁| > 1 since |t₁| < s₁)
- Permuted diff 1: f'₁(u) = (t₀−t₁)·u − (s₀−s₁) = (t₀−t₁)·u + (s₁−s₀), always positive (root |(s₁−s₀)/(t₁−t₀)| > 1)

**No u ∈ (−1,1) makes f'₀ and f'₁ same-signed.** The permuted configuration cannot be in ET.

This also extends to non-ForwardJostSet witnesses: for any JostSet witness x where both x and x∘σ need to be in ET, at least one will have a backward consecutive diff that no CLG(1) element can fix (since the second spatial dimension needed for the "rotation trick" doesn't exist).

**This means: for d=1, the proof MUST use a different approach (adjacent-swap induction).**

Full mathematical details: `test/proofideas_blockerB_permutation.lean`, Sections 3 and 7.

### Sorry Decomposition (Clean Sub-Lemmas)

The sorry reduces to three independent sub-obligations:

**SORRY B1 (d ≥ 2 only): Jost's theorem — `JostSet ⊆ ExtendedTube` for d ≥ 2**
```lean
theorem jostSet_subset_extendedTube_d_ge_2 (hd : 2 ≤ d) :
    ∀ x ∈ JostSet d n, realEmbed x ∈ ExtendedTube d n
```
- Classical result (Jost 1957). For d ≥ 2, there are enough spatial dimensions to find complex Lorentz transforms for any pairwise-spacelike configuration.
- The counterexample (`test/jostset_et_counterexample_test.lean`) only applies to d=1.
- Estimated: ~200-300 lines. No dependency on Blocker A.

**SORRY B2: Overlap set connectivity**
```lean
theorem permForwardOverlapSet_isConnected (hd : 1 ≤ d) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin n)) : IsConnected (permForwardOverlapSet n σ)
```
- Follows from orbit-set connectivity (Blocker A) via existing infrastructure.
- Route: orbit sets connected → `permForwardOverlapIndexSet` connected → `permForwardOverlapSet` connected.
- Estimated: ~50-100 lines AFTER Blocker A is resolved.
- **Depends on Blocker A.**

**SORRY B3 (d=1 only): Restructure to adjacent-swap induction**
- Rewrite `iterated_eow_permutation_extension` to use `Fin.Perm.adjSwap_induction_right`.
- Each step extends F across one adjacent swap using edge-of-wedge.
- Requires per-swap overlap connectivity (weaker than general-σ, still needs Blocker A).
- Estimated: ~200-400 lines.
- **Depends on B2.**

### Recommended Proof Structure

```lean
-- At PermutationFlow.lean:1428, replace the sorry:
by_cases hd2 : 2 ≤ d
· -- d ≥ 2: Use Approach A (local witness + overlap connectivity)
  intro z hz hσz
  have hJostWitness := jost_witness_from_d_ge_2 hd2 hn1 σ  -- uses B1
  have hConn := permForwardOverlapSet_isConnected hd1 hn1 σ  -- uses B2
  exact extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected
    n F hF_holo hF_lorentz hF_bv hF_local σ hJostWitness hConn z hz hσz
· -- d = 1: Use Approach B (adjacent-swap induction)
  have hd1_eq : d = 1 := by omega
  -- Restructure as induction on adjacent-swap decomposition of σ
  sorry -- B3: requires restructuring the proof
```

### Obligation 1: Jost → ExtendedTube Bridge (d ≥ 2)

**Needed:** `∀ x ∈ JostSet d n, realEmbed x ∈ ExtendedTube d n` (for d ≥ 2 only)

For d ≥ 2, this is Jost's theorem — a classical result that holds because the (1,2)-spatial plane provides enough room to construct complex Lorentz transforms mapping any pairwise-spacelike config into the forward tube.

**The FALSE global bridge (`test/jostset_et_counterexample_test.lean`) is only a counterexample for d=1.** For d ≥ 2, the global bridge IS true.

### Obligation 2: Overlap Connectivity (via Blocker A)

**Needed:** `IsConnected (permForwardOverlapSet n σ)`

**Best route: Derive from Blocker A.** Once orbit sets are connected:
1. `permForwardOverlapIndexSet` = union of orbit sets sharing the identity → connected
2. `permForwardOverlapSet` = union of convex slices indexed by connected set → connected
3. Chain through existing `isConnected_permForwardOverlapSet_of_indexConnected`

**Proved infrastructure:**

| Lemma | Line | Status |
|-------|------|--------|
| `isOpen_permForwardOverlapIndexSet` | 238 | ✓ |
| `permIndexSet_left_mul_ofReal` | 260 | ✓ |
| `permIndexSet_right_mul_ofReal` | 295 | ✓ |
| `permIndexSet_joined_left/right_ofReal` | 327/347 | ✓ |
| `isConnected_...of_real_double_coset_generation` | 371 | ✓ |
| `permForwardOverlapSlice_convex` | 402 | ✓ |

### Key Definitions

| Definition | Location | Description |
|---|---|---|
| `JostSet d n` | JostPoints.lean:61 | `{x \| ∀ i≠j, isSpacelike(xᵢ-xⱼ)}` |
| `ForwardJostSet d n` | JostPoints.lean:177 | `{x \| ∀ k, \|ζₖ(0)\| < ζₖ(1)}` |
| `realEmbed x` | JostPoints.lean:66 | `fun k μ => ↑(x k μ)` |
| `ExtendedTube d n` | PermutedTube.lean:13 | `⋃ Λ, Λ '' ForwardTube` |
| `permForwardOverlapIndexSet n σ` | PermutationFlow.lean:232 | `{Λ \| ∃w∈FT, Λ·(σ·w) ∈ FT}` |

### Dead Ends (DO NOT RETRY)

- Global `JostSet ⊆ ExtendedTube` **for d=1** — FALSE (`test/jostset_et_counterexample_test.lean`)
- ForwardJostSet witness approach **for d=1** — PROVABLY IMPOSSIBLE (see d=1 obstruction above)
- Midpoint condition `permAct(σ*swap) ∈ ET ⟹ permAct(σ) ∈ ET` — FALSE (`test/midpoint_condition_counterexample_test.lean`)
- "ET is globally permutation-invariant" — FALSE (that's PET, strictly larger)
- Using the same complex boost for both x and x∘σ in d=1 — impossible (sign obstruction)

### Priority Order

1. **Resolve Blocker A first** (orbitSet_isPreconnected) — this is the ROOT BLOCKER
2. Derive B2 (overlap connectivity) from Blocker A
3. For d ≥ 2: prove B1 (Jost's theorem), then fill sorry
4. For d = 1: implement B3 (adjacent-swap restructuring), using B2

**Estimated total: ~450-800 lines, AFTER Blocker A is resolved.**

### Detailed Proof Ideas

See `test/proofideas_blockerB_permutation.lean` (10-section analysis with full d=1 computation) and `test/proofideas_connectedness_blockers_2026_02_26.lean`.

---

## 18. Blocker Interdependency

Blocker A is the **root blocker**. Blocker B depends on Blocker A for overlap connectivity:

```
Blocker A (orbitSet_isPreconnected)  ←── ROOT BLOCKER
  ↓                           ↓
  nonemptyDomain              permForwardOverlapSet connectivity (B2)
  _isPreconnected               ↓
  ↓                           Blocker B (iterated_eow_permutation_extension)
  ↓                             ↓
  complex_lorentz_invariance  F_permutation_invariance
  ↓                             ↓
  BHW Properties 1-3, 5      BHW Property 4 (perm symmetry)
  ↓_____________________________↓
                ↓
    Full BHW Theorem (0 sorrys)
                ↓
    AxiomBridge → AnalyticContinuation
```

**Key findings:**
- Blocker B's overlap connectivity (B2) derives from Blocker A's orbit-set connectivity
- For d ≥ 2, Blocker B also needs Jost's theorem (B1, independent of Blocker A)
- For d = 1, the standard Jost-witness approach is PROVABLY IMPOSSIBLE — the proof must use adjacent-swap induction (B3), which still needs B2
- **Recommended order: Blocker A → B2 → B1 + B3 → Blocker B closed**

Only B1 (Jost's theorem for d ≥ 2, ~200-300 lines) can be worked on independently of Blocker A.
