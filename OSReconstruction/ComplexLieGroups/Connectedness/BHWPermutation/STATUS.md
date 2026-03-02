# BHW Permutation Invariance - Status

Last updated: 2026-03-02

## Current Status

`BHW.bargmann_hall_wightman_theorem` compiles with:
- zero `sorry`s
- two project axioms

Lean check:

```lean
#print axioms BHW.bargmann_hall_wightman_theorem
```

Current non-core dependencies:
- `BHW.isConnected_sliceIndexSet`
- `BHW.hExtPerm_of_d1`

Core Lean axioms also appear (`propext`, `Classical.choice`, `Quot.sound`).

## Axiom: `isConnected_sliceIndexSet` (Bogolyubov Lemma 9.7)

The slice index set `{Λ ∈ SO₊(1,d;ℂ) | ∃ w ∈ FT, Λ(σw) ∈ FT}` is connected
for `d ≥ 2` and non-trivial `σ`.

This is Lemma 9.7 in Bogolyubov, Logunov, Oksak & Todorov,
*General Principles of Quantum Field Theory* (1990), Ch. 9.

In the textbook (4D, SL(2,ℂ)×SL(2,ℂ) parametrization), every element of the
index set is continuously deformed to a canonical form parametrized by a
connected parameter space. For general `d ≥ 2`, `SO₊(1,d;ℂ)` is path-connected
and the index set is a non-empty open subset whose complement has positive
codimension, hence connected.

**Previous approach (removed)**: `kakSet_dense` axiom + ~1900 lines of boost
exponential / Weyl conjugation / principal strip infrastructure. The `kakSet_dense`
axiom was FALSE (KAK decomposition is not globally surjective for non-semisimple
elements), so all that infrastructure was dead weight.

## Axiom: `hExtPerm_of_d1` (Dimension reduction)

Permutation invariance of `extendF` on `ET ∩ σ⁻¹(ET)` for `d = 1`. The standard
approach embeds 1+1D into 2+1D via BHW invariant representation theory.

## Key Proven Pieces (No Axiom)

- slice index set is open:
  `isOpen_sliceIndexSet` in OverlapConnected.lean
- forward-overlap set connectedness (gluing lemma over connected slices):
  `isConnected_permForwardOverlapSet` in OverlapConnected.lean
- ET overlap connectedness (Lorentz orbit image):
  `isConnected_etOverlap` in OverlapConnected.lean
- d ≥ 2 permutation invariance (identity theorem on connected ET overlap):
  `hExtPerm_of_d2` in OverlapConnected.lean

## Build Check

Verified after the refactor:
- `lake build OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.OverlapConnected`
- `lake build OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlow`
