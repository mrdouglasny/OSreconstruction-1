# BHW Permutation Invariance — Status

Last updated: 2026-03-02

## Current Status

`BHW.bargmann_hall_wightman_theorem` compiles with zero `sorry`s.

Top-level axiom dependencies (via `#print axioms`):

- `BHW.hExtPerm_of_d1` — permutation invariance for d = 1
- `BHW.isConnected_sliceIndexSet_general` — slice index set connectedness for d ≠ 3
- 8 axioms in `SL2CDoubleCover.lean` — SL(2,ℂ) double cover infrastructure
- 2 axioms in `SliceIndexSetD3.lean` — diagonal Lorentz continuity and parameter connectedness
- 2 `sorry` in `SL2CDoubleCover.lean` — SU(2) group instance (mul/inv closure)

Plus core Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Architecture

The slice index set connectedness was previously a single axiom for all d.
It is now split:

- **d = 3 (4D spacetime)**: proved via SL(2,ℂ)×SL(2,ℂ) double cover and KAK
  decomposition, modulo sub-axioms listed below.
- **d ≠ 3**: remains a single axiom (`isConnected_sliceIndexSet_general`).

The d = 3 proof lives in two new files:

| File | Role |
|------|------|
| `SL2CDoubleCover.lean` | SL(2,ℂ) double cover Φ, SU(2), KAK decomposition |
| `SliceIndexSetD3.lean` | Bi-invariance, KAK for SO₊(1,3;ℂ), assembly |

The assembly proof in `SliceIndexSetD3.lean` is fully proved (no sorry/axiom):
bi-invariance strips the SU(2) factors via KAK, reducing to a diagonal parameter
set, then the index set = continuous image of (K × P × K) with K, P connected.

## Axiom Inventory

### SL2CDoubleCover.lean — 8 axioms + 2 sorry

These axiomatize the double cover Φ: SL(2,ℂ)×SL(2,ℂ) → SO₊(1,3;ℂ).

| Axiom | Statement | Reference | Difficulty |
|-------|-----------|-----------|------------|
| `sl2cDoubleCoverMap` | The map Φ(A,B) itself | Standard; Streater-Wightman §1-4 | Medium — explicit Pauli matrix construction |
| `sl2cDoubleCoverMap_mul` | Φ is a group homomorphism | Follows from definition of Φ | Easy once Φ is defined |
| `sl2cDoubleCoverMap_one` | Φ(1,1) = 1 | Follows from definition | Easy |
| `sl2cDoubleCoverMap_continuous` | Φ is continuous | Polynomial in matrix entries | Easy |
| `sl2cDoubleCoverMap_surjective` | Φ is surjective | dΦ is Lie algebra iso ⟹ image open+closed in connected group | Medium — needs Lie algebra computation |
| `sl2cDoubleCover_unitary_maps_to_real` | SU(2)×SU(2) ↦ real Lorentz | Unitaries preserve Hermitian matrices | Medium |
| `sl2c_kak` | A = U·diag(a,a⁻¹)·V for A ∈ SL(2,ℂ) | Singular value decomposition for 2×2 det-1 matrices | Provable — Mathlib spectral theory |
| `SU2_isPathConnected` | SU(2) is path-connected | SU(2) ≅ S³ | Provable — Mathlib? |

The 2 `sorry` are in the `Group SU2` instance (closure of IsSU2 under mul and inv).
These follow from (AB)†(AB) = B†A†AB = B†IB = I. Low priority.

### SliceIndexSetD3.lean — 2 axioms

| Axiom | Statement | Reference | Difficulty |
|-------|-----------|-----------|------------|
| `continuous_diagonalLorentz` | (a,b) ↦ Φ(diag(a,a⁻¹), diag(b,b⁻¹)) is continuous | Composition of continuous maps | Easy once Φ is defined |
| `isConnected_diagonalParamSet` | {(a,b) ∈ (ℂ\*)² \| D(a,b) ∈ I} is connected | BLT Ch. 9 Lemma 9.7 (core step) | **Hard** — forward-cone geometry |

`isConnected_diagonalParamSet` is the mathematical heart of the argument. It
requires computing the explicit action of diagonal Lorentz elements on forward-tube
points and showing the resulting parameter locus in (ℂ\*)² is connected. This is
where BLT's proof does genuine complex-geometric work.

### OverlapConnected.lean — 2 axioms

| Axiom | Statement | Reference | Difficulty |
|-------|-----------|-----------|------------|
| `isConnected_sliceIndexSet_general` | Slice index set connected for d ≠ 3, d ≥ 2 | BLT Lemma 9.7 (general d) | Hard — no SL(2,ℂ) trick available |
| `hExtPerm_of_d1` | Permutation invariance for d = 1 | Embedding 1+1D → 2+1D | Medium |

## What Is Proved (no axiom needed)

- Bi-invariance of the index set under real Lorentz (`indexSet_left/right_invariant_d3`)
- KAK decomposition for SO₊(1,3;ℂ) from SL(2,ℂ) KAK (`complexLorentz3_kak_decomposition`)
- Index set = image of K × P × K (`indexSet_eq_image_kak`)
- Connected image assembly (`isConnected_sliceIndexSet_d3`)
- Slice index set is open (`isOpen_sliceIndexSet`)
- Forward-overlap set connectedness (`isConnected_permForwardOverlapSet`)
- ET overlap connectedness (`isConnected_etOverlap`)
- d ≥ 2 permutation invariance (`hExtPerm_of_d2`)
- KAK for pairs (`sl2c_pair_kak`, from `sl2c_kak`)

## Gaps by Priority

1. **`isConnected_diagonalParamSet`** — the one axiom that encodes real mathematical
   content specific to the BHW proof. Everything else is either standard Lie theory
   infrastructure or the general-d case.

2. **`sl2cDoubleCoverMap` + derived properties** (5 axioms) — constructing Φ explicitly
   from Pauli matrices would discharge `_mul`, `_one`, `_continuous` automatically.
   `_surjective` needs a separate Lie algebra argument.

3. **`sl2c_kak`** — most likely provable from existing Mathlib (spectral theorem for
   positive definite Hermitian matrices + polar decomposition).

4. **`isConnected_sliceIndexSet_general`** — the general-d case. BLT's argument is
   specific to d = 3. For general d, one needs either a different parametrization
   of SO₊(1,d;ℂ) or a codimension argument for the complement of I.

5. **`hExtPerm_of_d1`** — deferred; standard embedding argument.

## Build Verification

```
lake build OSReconstruction.ComplexLieGroups.SL2CDoubleCover
lake build OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SliceIndexSetD3
lake build OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.OverlapConnected
lake build OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlow
```
