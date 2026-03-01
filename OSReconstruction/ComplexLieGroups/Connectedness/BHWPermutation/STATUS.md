# BHW Permutation Invariance — Status & Axiom Elimination Plan

Last updated: 2026-03-01

## Current State

**`bargmann_hall_wightman_theorem` compiles with zero sorrys.**

```
#print axioms BHW.bargmann_hall_wightman_theorem
```
```
propext, Classical.choice, Quot.sound     -- standard Lean
BHW.isConnected_sliceIndexSet             -- Lie group topology (d ≥ 2)
BHW.hExtPerm_of_d1                        -- dimension reduction (d = 1)
```

### Files (zero sorrys across all 6)

| File | Lines | Role |
|------|-------|------|
| `SeedSlices.lean` | ~140 | Seed/slice decomposition, `permForwardOverlapSet`, `permForwardOverlapIndexSet` |
| `JostWitnessGeneralSigma.lean` | ~620 | Jost witness for general σ when d ≥ 2 |
| `Adjacency.lean` | ~1250 | Adjacent-swap overlap witnesses, EOW chain infrastructure |
| `IndexSetD1.lean` | ~200 | d=1 orbit set preconnectedness |
| `OverlapConnected.lean` | ~960 | **Route B core**: identity theorem, slice gluing, 2 axioms |
| `PermutationFlow.lean` | ~2450 | Master proof: EOW iteration, case split d=0/d=1/d≥2 |

---

## The Two Axioms

### Axiom 1: `isConnected_sliceIndexSet` (Lie group topology)

```lean
axiom isConnected_sliceIndexSet {d : ℕ}
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hd2 : 2 ≤ d) :
    IsConnected {Λ : ComplexLorentzGroup d |
      (permForwardOverlapSlice (d := d) n σ Λ).Nonempty}
```

**Mathematical content**: The set of complex Lorentz transforms yielding a nonempty
forward-overlap slice is connected.

**Why it's true**: By the Cartan KAK decomposition, L₊(ℂ) = K · A · K where
K = L₊↑(ℝ) and A is the complex boost strip. Slice nonemptiness is bi-K-invariant
(`sliceIndexSet_bi_invariant`, proved), so the index set is a union of K-double
cosets. Since K is connected for d ≥ 2 (`RestrictedLorentzGroup.isPathConnected`,
proved) and A is connected (`isConnected_complexBoostStrip`, proved), the index
set is connected.

**What's needed to prove it**: The polar/Cartan decomposition itself:
every Λ ∈ L₊(ℂ) factors as Λ = k₁ · a · k₂ with k₁,k₂ ∈ K, a ∈ A.
This requires matrix logarithm on the symmetric space L₊(ℂ)/L₊↑(ℝ).

**Existing infrastructure** (all proved, in `OverlapConnected.lean`):
- `sliceIndexSet_bi_invariant` — K-conjugation preserves slice nonemptiness
- `sliceIndexSet_bi_invariant_rev` — converse direction
- `isConnected_complexBoostStrip` — A = {exp(tK) | t ∈ ℂ} is connected
- `boostGen_isInLieAlgebra` — boost generator is in the Lie algebra

**Missing infrastructure**:
- Matrix logarithm / polar decomposition for L₊(ℂ)
- OR: direct proof that every element of the index set is in some K·A·K coset
  (weaker than full polar decomposition — only need it for the index set)

**Estimated difficulty**: Medium. The KAK decomposition for SO₊(1,d;ℂ) is
well-established. Previous attempt in `GeodesicConvexity.lean` was removed
because it had sorrys, but the approach was mathematically sound.

**No QFT dependencies**: This is pure Lie group geometry.

### Axiom 2: `hExtPerm_of_d1` (dimension reduction)

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
- `hExtPerm_of_d2` (proved, no axioms beyond `isConnected_sliceIndexSet`)

**Estimated difficulty**: Hard. The algebraic invariant theory is the main
challenge. The dimensional embedding has Fin arithmetic difficulties (previously
attempted and abandoned).

---

## Dependency DAG (acyclic)

```
Phase 1: Pure Lie Geometry
    isConnected_sliceIndexSet
    ├── sliceIndexSet_bi_invariant ✓
    ├── isConnected_complexBoostStrip ✓
    └── KAK polar decomposition [TODO]

Phase 2: BHW for d ≥ 2 (DONE)
    hExtPerm_of_d2 ✓
    ├── isConnected_sliceIndexSet (Phase 1)
    ├── isConnected_permForwardOverlapSet ✓ (slice gluing)
    ├── isConnected_etOverlap ✓
    ├── identity_theorem_totally_real_product ✓
    ├── permJostSet_nonempty ✓ (Jost witnesses, d ≥ 2)
    └── extendF_diff_zero_on_permJostSet ✓

Phase 3: BHW for d = 1 (bypasses hExtPerm_of_d1)
    hExtPerm_of_d1
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
    │   │   └── isConnected_sliceIndexSet [AXIOM 1]
    │   └── ComplexLorentzGroup.isPathConnected ✓
    ├── identity_theorem_totally_real_product ✓
    ├── permJostSet_nonempty (d ≥ 2) ✓
    └── extendF_diff_zero_on_permJostSet ✓
```

---

## Historical Notes

### False axiom removed (2026-03-01)

The extended tube ET is NOT geometrically convex. It is only holomorphically
convex (a domain of holomorphy), per Borchers 1961. A previous version of this
file contained `axiom extendedTube_convex`, which was mathematically false and
could be used to derive `False` in Lean.

**Counterexample**: For n=2, d≥2, take configurations A with difference (0,1,0,...)
(spacelike, hence a Jost point in ET) and B with difference (0,-1,0,...)
(also spacelike, in ET). The midpoint has difference (0,0,...) — the zero vector,
which is lightlike. Since z₁ = z₂ implies w₁ = w₂ for any Λ⁻¹, contradicting
Im(w₂-w₁) ∈ V⁺, the midpoint is NOT in ET.

The fix replaced `extendedTube_convex` with `isConnected_sliceIndexSet` and
rewired `isConnected_permForwardOverlapSet` to use the (already proved) slice
gluing infrastructure.

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

1. **`isConnected_sliceIndexSet`** — Pure Lie group geometry. No QFT.
   New file: `ComplexLieGroups/PolarDecomposition.lean` or extend
   `GeodesicConvexity.lean`. Needs matrix logarithm on L₊(ℂ)/L₊↑(ℝ).

2. **`hExtPerm_of_d1`** — Depends on (1) being done first (via `hExtPerm_of_d2`).
   New files: `ComplexLieGroups/LightconeInvariantTheory.lean` (d=1 algebraic
   invariant theory), `ComplexLieGroups/DimensionalEmbedding.lean` (Fin 2 ↪ Fin 3).

3. **Restrict BHW to d ≥ 2** (alternative to step 2) — If d=1 infrastructure
   proves too costly, change `bargmann_hall_wightman_theorem` to require
   `(hd2 : 2 ≤ d)` instead of `[NeZero d]`, eliminating axiom 2 entirely.
   The physical case (d=3, i.e., 3+1D spacetime) would be fully proved.
