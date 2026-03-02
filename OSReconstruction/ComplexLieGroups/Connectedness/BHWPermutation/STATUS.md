# BHW Permutation Invariance — Status & Axiom Elimination Plan

Last updated: 2026-03-02

## Current State

**`bargmann_hall_wightman_theorem` compiles with zero sorrys.**

```
#print axioms BHW.bargmann_hall_wightman_theorem
```
```
propext, Classical.choice, Quot.sound          -- standard Lean
BHW.raw_KAK_decomposition                     -- Lie group KAK factorization (d ≥ 2)
BHW.hExtPerm_of_d1                             -- dimension reduction (d = 1)
```

All previous axioms (`isConnected_principalBoostOverlap`, `sliceIndexSet_KAK_principal`)
are now **theorems**. Only the raw KAK decomposition and the d=1 case remain axiomatized.

### Files (zero sorrys across all 6)

| File | Lines | Role |
|------|-------|------|
| `SeedSlices.lean` | ~140 | Seed/slice decomposition, `permForwardOverlapSet`, `permForwardOverlapIndexSet` |
| `JostWitnessGeneralSigma.lean` | ~620 | Jost witness for general σ when d ≥ 2 |
| `Adjacency.lean` | ~1250 | Adjacent-swap overlap witnesses, EOW chain infrastructure |
| `IndexSetD1.lean` | ~200 | d=1 orbit set preconnectedness |
| `OverlapConnected.lean` | ~2815 | **Route B core**: identity theorem, slice gluing, boost exp, Weyl reflection, 2 axioms |
| `PermutationFlow.lean` | ~2450 | Master proof: EOW iteration, case split d=0/d=1/d≥2 |

---

## The Two Axioms

### Axiom 1: `raw_KAK_decomposition` (line 2182, private)

```lean
private axiom raw_KAK_decomposition {d : ℕ}
    (Λ : ComplexLorentzGroup d) :
    ∃ (k₁ k₂ : RestrictedLorentzGroup d) (t : ℂ),
      Λ = ComplexLorentzGroup.ofReal k₁ * expBoost t * ComplexLorentzGroup.ofReal k₂
```

**Mathematical content**: Every `Λ ∈ SO₊(1,d;ℂ)` factors as
`k₁ · exp(tK) · k₂` with `k₁, k₂ ∈ SO↑(1,d;ℝ)` and `t ∈ ℂ`.

**Why it's true**: This is the complexified Cartan KAK decomposition.
For the real Lorentz group, every proper orthochronous transformation factors
as (spatial rotation) · (boost in direction 1) · (spatial rotation). The complex
version extends this via polar decomposition + spectral theory for the indefinite
metric.

**No QFT dependencies**: Pure Lie group algebra.

**Proof approaches**:
- **Eigenvalue analysis**: `Λ` preserves the Minkowski form, so eigenvalues come
  in pairs `(eᵗ, e⁻ᵗ)`. Extract `t` from eigenvalues, `k₁, k₂` from the
  change of basis.
- **Polar decomposition**: Factor `Λ = P · O` with `P` positive (w.r.t. Minkowski),
  `O` orthogonal. Then diagonalize `P` via real spatial rotations.

### Derived theorems (proved from raw_KAK + existing infrastructure)

- **`sliceIndexSet_KAK_principal`** — proved by combining:
  1. `raw_KAK_decomposition` (axiom): gives `Λ = k₁ · exp(tK) · k₂` with `t ∈ ℂ`
  2. **Weyl reflection** (theorem): 180° spatial rotation `R` satisfies
     `R · exp(tK) · R⁻¹ = exp(-tK)`, mapping `Im(t) < 0` to `Im(-t) > 0`
  3. **Periodicity** (theorem): `exp((t + 2πi)K) = exp(tK)`
  4. **Meridian exclusion** (theorem): nonempty slice condition excludes
     `Im(t) = 0` (real boosts) and `Im(t) = π` (PT reversal)

- **`isConnected_principalBoostOverlap`** — proved via:
  1. `principalStrip_slice_nonempty` (large spatial shift trick)
  2. `principalBoostOverlap_eq_strip` (overlap = full principal strip)
  3. `convex_principalBoostStrip` (convexity → connectedness)

- **`isConnected_sliceIndexSet`** — proved from KAK + connectedness by mapping
  `K × P × K → I` via group multiplication

### Axiom 2: `hExtPerm_of_d1` (line 2794)

```lean
axiom hExtPerm_of_d1
    (n : ℕ) (F : (Fin n → Fin 2 → ℂ) → ℂ) ...
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin 2 → ℂ)
    (hz : z ∈ ExtendedTube 1 n)
    (hσz : (fun k => z (σ k)) ∈ ExtendedTube 1 n) :
    extendF F (fun k => z (σ k)) = extendF F z
```

**Mathematical content**: `extendF F` is permutation-invariant on `ET ∩ σ⁻¹(ET)`
for spacetime dimension 1+1.

**Why it can't use the d ≥ 2 proof path**: Real Jost witnesses do not exist for
d=1 (the spacelike region in 1+1D is disconnected — proved in
`d1_no_real_witness_swap_n2_probe.lean`). The identity theorem needs a nonempty
vanishing locus, so the d ≥ 2 proof breaks down.

**Circularity warning**: The naive dimensional reduction (embed d=1 into d=2,
apply `hExtPerm_of_d2`, project back) requires expressing F in terms of
Lorentz-invariant scalar products. This is a consequence of the BHW representation
theorem. If BHW itself depends on `hExtPerm_of_d1`, this creates a cycle.

**The non-circular proof path** (three phases):

#### Phase 1: Prove `isConnected_sliceIndexSet` (pure Lie geometry, no QFT)

#### Phase 2: Prove BHW for d ≥ 2 (already done via `hExtPerm_of_d2`)

#### Phase 3: Prove BHW for d = 1 without `hExtPerm_of_d1`

The key insight: for d=1, the complex Lorentz group SO₊(1,1;ℂ) ≅ ℂˣ is abelian.
In lightcone coordinates (u,v), Lorentz boosts act as (u,v) ↦ (λu, λ⁻¹v).
The Lorentz-invariant polynomials of this scaling action are exactly the
products uᵢvⱼ, i.e., the scalar dot products zᵢ · zⱼ.

So for d=1, the BHW representation theorem (F = H(zᵢ·zⱼ)) can be proved by
**pure algebra** — no permutation invariance needed. Then:
1. Express F(z) = H(zᵢ·zⱼ) algebraically (d=1 invariant theory)
2. Define F₂D(W) = H(Wᵢ·Wⱼ) — automatically SO₊(1,2;ℂ)-invariant
3. Apply `hExtPerm_of_d2` to F₂D
4. Restrict spatial W₂ = 0 to recover `hExtPerm_of_d1`

**Dependencies for Phase 3**:
- Lightcone coordinate infrastructure for d=1
- Algebraic invariant theory: F Lorentz-invariant ⟹ F = H(zᵢ·zⱼ)
- Dimensional embedding: Fin 2 ↪ Fin 3 with forward cone compatibility
- `hExtPerm_of_d2` (proved, no axioms beyond `raw_KAK_decomposition`)

**Estimated difficulty**: Hard. The algebraic invariant theory is the main
challenge. The dimensional embedding has Fin arithmetic difficulties (previously
attempted and abandoned).

---

## Dependency DAG (acyclic)

```
Phase 1: Pure Lie Geometry
    isConnected_sliceIndexSet ✓ (theorem)
    ├── isConnected_principalBoostOverlap ✓ (theorem)
    │   ├── principalStrip_slice_nonempty ✓ (large spatial shift trick)
    │   ├── exp_boostGen_eq ✓ (projection decomposition)
    │   └── convex_principalBoostStrip ✓
    ├── sliceIndexSet_KAK_principal ✓ (theorem)
    │   ├── raw_KAK_decomposition [AXIOM 1]
    │   ├── weyl_reflection ✓ (R·exp(tK)·R⁻¹ = exp(-tK))
    │   ├── expBoost_periodic ✓ (exp((t+2πi)K) = exp(tK))
    │   └── meridian exclusion ✓ (Im(t) ∉ {0, π})
    ├── sliceIndexSet_bi_invariant ✓
    ├── sliceIndexSet_bi_invariant_rev ✓
    └── RestrictedLorentzGroup.isPathConnected ✓

Phase 2: BHW for d ≥ 2 (DONE)
    hExtPerm_of_d2 ✓
    ├── isConnected_sliceIndexSet ✓ (Phase 1)
    ├── isConnected_permForwardOverlapSet ✓ (slice gluing)
    ├── isConnected_etOverlap ✓
    ├── identity_theorem_totally_real_product ✓
    ├── permJostSet_nonempty ✓ (Jost witnesses, d ≥ 2)
    └── extendF_diff_zero_on_permJostSet ✓

Phase 3: BHW for d = 1 (bypasses hExtPerm_of_d1)
    hExtPerm_of_d1 [AXIOM 2]
    ├── d=1 algebraic invariant theory [TODO]
    │   └── SO₊(1,1;ℂ) ≅ ℂˣ, lightcone coordinates
    ├── dimensional embedding Fin 2 ↪ Fin 3 [TODO]
    └── hExtPerm_of_d2 ✓ (Phase 2, no circularity)
```

**Critical invariant**: Phase 3 depends on Phase 2 (which is proved),
NOT on the BHW theorem itself. So there is no circularity.

---

## Proof Architecture (what's proved vs axiomatized)

```
bargmann_hall_wightman_theorem [NeZero d]
├── d = 0: vacuous (ET overlap forces σ = 1) ✓
├── d = 1: hExtPerm_of_d1 [AXIOM 2]
│   └── iterated_eow_permutation_extension ✓
└── d ≥ 2: hExtPerm_of_d2 ✓
    ├── isConnected_etOverlap ✓
    │   ├── isConnected_permForwardOverlapSet ✓ (slice gluing)
    │   │   ├── permForwardOverlapSet_eq_iUnion_slice ✓
    │   │   ├── permForwardOverlapSlice_isPreconnected ✓ (convexity)
    │   │   ├── permForwardOverlapSlice_openMembership ✓
    │   │   ├── isConnected_iUnion_of_open_membership ✓
    │   │   └── isConnected_sliceIndexSet ✓ (theorem)
    │   │       ├── isConnected_principalBoostOverlap ✓ (theorem)
    │   │       ├── sliceIndexSet_KAK_principal ✓ (theorem)
    │   │       │   └── raw_KAK_decomposition [AXIOM 1]
    │   │       ├── sliceIndexSet_bi_invariant ✓
    │   │       └── sliceIndexSet_bi_invariant_rev ✓
    │   └── ComplexLorentzGroup.isPathConnected ✓
    ├── identity_theorem_totally_real_product ✓
    ├── permJostSet_nonempty (d ≥ 2) ✓
    └── extendF_diff_zero_on_permJostSet ✓
```

---

## Progress Over Upstream (xiyin/OSreconstruction)

Starting from xiyin's repo, our fork accomplished the following:

### Sorry elimination

- **Upstream state**: 1 sorry in `PermutationFlow.lean:2262` (the core BHW
  permutation extension for `d ≥ 2`), 0 axioms in `OverlapConnected.lean`
  (file did not exist).
- **Current state**: 0 sorrys, 2 axioms (raw KAK decomposition + d=1 reduction).

### New file: `OverlapConnected.lean` (~2815 lines)

This file contains the mathematical core of the BHW permutation proof:

1. **Slice infrastructure (Route A)**:
   - `permForwardOverlapSlice` — fixed-Λ slice of the forward-overlap set
   - `permForwardOverlapSlice_convex` — each slice is convex (hence preconnected)
   - `permForwardOverlapSlice_openMembership` — slice membership is open in Λ
   - `permForwardOverlapSet_eq_iUnion_slice` — FOS = ⋃_Λ Slice(Λ)

2. **Bi-invariance**:
   - `sliceIndexSet_bi_invariant` / `_rev` — K-conjugation preserves slice
     nonemptiness (both directions)

3. **Principal boost strip infrastructure**:
   - `expBoost` — the boost exponential map `t ↦ exp(tK)`
   - `principalBoostStrip` — `{t ∈ ℂ | 0 < Im(t) < π}`
   - `principalBoostOverlap` — principal strip ∩ {t | slice nonempty}
   - `boostGen_isInLieAlgebra` — K is in the Lorentz Lie algebra

4. **Matrix exponential of boost generator**:
   - `boostGen_sq`, `boostGen_cubed` — K² = projection, K³ = K
   - `exp_smul_idempotent` — for E²=E: exp(αE) = 1 + (exp(α)-1)·E
   - `exp_boostGen_eq` — exp(tK) = I + sinh(t)·K + (cosh(t)-1)·K²
   - `expBoost_val_entry` — cosh/sinh entry formula
   - `principalStrip_slice_nonempty` — large spatial shift witness
   - `isConnected_principalBoostOverlap` — **theorem** (was axiom)

5. **Weyl reflection and principal strip KAK**:
   - `weylReflection` — 180° spatial rotation R with R·K·R⁻¹ = -K
   - `expBoost_weyl_neg` — R·exp(tK)·R⁻¹ = exp(-tK)
   - `expBoost_periodic` — exp((t+2πi)K) = exp(tK)
   - `expBoost_nonempty_excludes_even_meridian` — Im(t) ≠ 2mπ for nonempty slices
   - `expBoost_nonempty_excludes_odd_meridian` — Im(t) ≠ (2m+1)π for nonempty slices
   - `sliceIndexSet_KAK_principal` — **theorem** (was axiom)

6. **Connectedness chain**:
   - `isConnected_sliceIndexSet` — **theorem**
   - `isConnected_permForwardOverlapSet` — via `isConnected_iUnion_of_open_membership`
   - `isConnected_etOverlap` — ET overlap is connected for d ≥ 2

7. **Identity theorem (Route B)**:
   - `identity_theorem_totally_real_product` — holomorphic function vanishing on
     open subset of connected domain is identically zero
   - `permJostSet` / `permJostSet_nonempty` — real Jost witnesses for d ≥ 2
   - `extendF_diff_zero_on_permJostSet` — the difference h = extendF∘σ - extendF
     vanishes on the Jost set
   - `hExtPerm_of_d2` — **the d ≥ 2 permutation extension theorem**

8. **Two axioms**:
   - `raw_KAK_decomposition` — pure Lie group KAK factorization
   - `hExtPerm_of_d1` — d=1 dimension reduction

### Key mathematical discovery: `extendedTube_convex` is FALSE

An intermediate version used `axiom extendedTube_convex` (the extended tube is
geometrically convex). This is **mathematically false** — the extended tube is
only holomorphically convex (a domain of holomorphy), per Borchers 1961.

**Counterexample**: For n=2, d≥2, configurations with differences (0,1,0,...) and
(0,-1,0,...) are both spacelike (in ET), but midpoint (0,0,...) is lightlike (NOT
in ET). This was identified and the false axiom replaced with the correct
slice-gluing approach.

### Refactoring of `PermutationFlow.lean`

- Moved `permForwardOverlapSlice`, convexity, and preconnectedness from
  `PermutationFlow.lean` to `OverlapConnected.lean` (eliminating duplication)
- Wired the d=0/d=1/d≥2 case split: d=0 vacuous, d=1 via `hExtPerm_of_d1`,
  d≥2 via `hExtPerm_of_d2`

### Principal strip analysis

The boost strip B = {exp(tK) | t ∈ ℂ} has topology ℂ/2πiℤ (a cylinder),
because exp(tK) has eigenvalues e^{±t} and is periodic with period 2πi.

For n ≥ 3 with non-trivial permutations, TWO meridians have empty slices:

- **Im(t) = 0** (real boosts): preserve V⁺, cannot perform V⁻ → V⁺ mapping.
- **Im(t) = π** (PT reversal): exp(iπK) acts as -I on the (time, boost-spatial)
  2×2 block. For n ≥ 3, this negates the time component of unflipped differences,
  making the slice empty.

Two meridians disconnect the cylinder into two strips:
- Upper: {0 < Im(t) < π} (the **principal strip**)
- Lower: {-π < Im(t) < 0} ≅ {π < Im(t) < 2π}

For d ≥ 2, the **Weyl reflection** (180° spatial rotation R satisfying
R·exp(tK)·R⁻¹ = exp(-tK)) identifies the two strips: any KAK factorization
with Im(t) < 0 can be rewritten with Im(-t) > 0 by absorbing R into the
K factors. This is why restricting to the principal strip suffices.

Within the principal strip, for any t with 0 < Im(t) < π, witnesses exist
using large real spatial components. The overlap is a dense open subset of
a convex strip, hence connected.

---

## Historical Notes

### Axiom eliminated (2026-03-02): `sliceIndexSet_KAK_principal`

Replaced by a **theorem** derived from the weaker `raw_KAK_decomposition` axiom
plus proved Weyl reflection, periodicity, and meridian exclusion lemmas. The
principal strip reduction is now fully formalized.

### Axiom eliminated (2026-03-02): `isConnected_principalBoostOverlap`

Proved as a theorem via matrix exponential entry formulas and the "large spatial
shift trick" witness construction (~400 lines of infrastructure).

### False axiom removed (2026-03-02): `isConnected_boostParameterOverlap`

The previous axiom `isConnected_boostParameterOverlap` stated that
`{t ∈ ℂ | slice at exp(tK) nonempty}` is connected on the full cylinder ℂ/2πiℤ.
This is **mathematically false** for n ≥ 3: both Im(t) = 0 (real boosts) AND
Im(t) = π (PT reversal) give empty slices, and two meridians disconnect a cylinder
into two strips.

The fix restricts to the **principal strip** `{0 < Im(t) < π}` and combines
standard KAK with the Weyl reflection to cover both strips.

### False axiom removed (2026-03-01): `extendedTube_convex`

The extended tube ET is NOT geometrically convex. It is only holomorphically
convex (a domain of holomorphy), per Borchers 1961.

**Counterexample**: For n=2, d≥2, take configurations A with difference (0,1,0,...)
(spacelike, hence a Jost point in ET) and B with difference (0,-1,0,...)
(also spacelike, in ET). The midpoint has difference (0,0,...) — the zero vector,
which is lightlike, NOT in ET.

### Route A vs Route B

- **Route A** (slice gluing): FOS = ⋃_Λ Slice(Λ), each slice convex, glue via
  connected index set. This is the current approach for `isConnected_permForwardOverlapSet`.
- **Route B** (identity theorem on ET overlap): h = extendF∘σ - extendF vanishes
  on open nonempty V ⊂ W (Jost witnesses), W connected, identity theorem gives
  h = 0. This is the approach for `hExtPerm_of_d2`.

The proof uses BOTH routes: Route A gives FOS connected → ET overlap connected,
then Route B uses the connected overlap domain for the identity theorem.

---

## Recommended Execution Order

1. ~~**`isConnected_principalBoostOverlap`**~~ — **DONE** (proved as theorem).

2. ~~**`sliceIndexSet_KAK_principal`**~~ — **DONE** (proved as theorem from
   `raw_KAK_decomposition` + Weyl reflection + periodicity + meridian exclusion).

3. **`raw_KAK_decomposition`** — Pure Lie group KAK factorization. Needs
   eigenvalue analysis or polar decomposition for the indefinite metric.
   Estimated ~300-500 lines.

4. **`hExtPerm_of_d1`** — Depends on `hExtPerm_of_d2` (proved).
   New files: `ComplexLieGroups/LightconeInvariantTheory.lean` (d=1 algebraic
   invariant theory), `ComplexLieGroups/DimensionalEmbedding.lean` (Fin 2 ↪ Fin 3).

5. **Restrict BHW to d ≥ 2** (alternative to step 4) — If d=1 infrastructure
   proves too costly, change `bargmann_hall_wightman_theorem` to require
   `(hd2 : 2 ≤ d)` instead of `[NeZero d]`, eliminating axiom 2 entirely.
   The physical case (d=3, i.e., 3+1D spacetime) would be fully proved.
