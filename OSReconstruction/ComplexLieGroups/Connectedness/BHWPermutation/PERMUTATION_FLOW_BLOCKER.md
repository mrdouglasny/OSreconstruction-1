# PermutationFlow Sorry Blocker (2026-02-28)

This note documents the remaining blocker in
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`.

## Location

- Remaining `sorry` is in `iterated_eow_permutation_extension`:
  - `PermutationFlow.lean:~2342`

Goal in that branch:

```lean
hExtPerm :
  forall z,
    z in ExtendedTube d n ->
    permAct sigma z in ExtendedTube d n ->
    extendF F (permAct sigma z) = extendF F z
```

Context there: `n >= 2`, `sigma != 1`, `d >= 1` (after ruling out `d = 0`).

## What is already proved and usable

### Local witness and transport machinery

- `JostWitnessGeneralSigma.jostWitness_exists` (for `d >= 2`) gives:
  - `exists x in JostSet`, with
  - `realEmbed x in ET` and `realEmbed (x ∘ sigma) in ET`.

- `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`
  reduces `hExtPerm` to connectedness of `permForwardOverlapSet`.

### Connectivity reduction chain (already in file)

- `isConnected_permForwardOverlapSet_of_indexConnected`
- `isConnected_permForwardOverlapIndexSet_of_seedConnected_and_seedOrbitPreconnected`
- `isConnected_permForwardOverlapIndexSet_d1_of_seedConnected`
- `isConnected_permOrbitSeedSet_iff_permForwardOverlapSet`

### New packaging helpers (already in file)

- `extendF_perm_overlap_of_jostWitness_and_seedConnected`
- `extendF_perm_overlap_dge2_of_seedConnected`
- `isConnected_permForwardOverlapSet_d1_of_seedConnected_and_nonempty`

These keep the final branch modular, but they still require the same missing geometric inputs.

### New open-anchor infrastructure (new production module)

- `Connectedness/BHWPermutation/OverlapAnchor.lean` now provides:
  - `extendF_perm_overlap_of_forward_base`
  - `forward_base_eq_of_open_anchor`
  - `extendF_perm_overlap_of_forward_open_anchor`

This gives a second rigorous route:

- connectedness of `permForwardOverlapSet` + open anchor equality on a nonempty open subset
  -> base equality on all forward overlap
  -> full ET-overlap equality (`hExtPerm`).

It does **not** remove the core connectedness blocker, but it decouples
"anchor propagation" from "global overlap geometry" for future d=1 and d>=2 attacks.

## Why this blocker is hard

All currently sound routes collapse to one of two missing global ingredients:

1. `IsConnected (permOrbitSeedSet n sigma)`
2. A d=1-specific replacement for the real-anchor identity-theorem step

### Key negative facts (already established in tests)

- No real ET pair/Jost witness for `d=1`, `n=2`, adjacent swap:
  - `test/d1_no_real_witness_swap_n2_probe.lean`
    - `no_real_et_pair_swap_n2`
    - `no_real_jost_witness_swap_n2`

- Midpoint-drop implication is false in `d=1`:
  - `test/midpoint_condition_d1_counterexample_test.lean`

- Some naive global-topology shortcuts are invalid:
  - `test/nonempty_domain_d1_counterexample.lean`
  - `test/nonempty_domain_complement_not_open_d1.lean`

So the stale proof attempts fail for structural reasons, not syntax gaps.

## Current minimal blocker decomposition

To close the `sorry` without adding assumptions, one of the following must be completed:

### Route A (d >= 2 + d=1 split)

- Prove seed/forward-overlap connectedness in `d >= 2`:
  - enough to feed `extendF_perm_overlap_dge2_of_seedConnected`
- Build a new d=1 complex-anchor mechanism (not real Jost-point based)

### Route B (uniform all d >= 1)

- Prove connectedness of `permForwardOverlapSet` directly for all `d >= 1`
- Apply `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`
  where witness exists, plus d=1 alternative witness mechanism

### Route C (new iterative extension infrastructure)

- Generalize adjacent EOW extension step to sector data
  (`PermExtensionData` step for `swap * sigma`) and avoid `hExtPerm`
  reduction entirely.

This is conceptually clean but requires substantial new domain-gluing machinery.

### Route D (open-anchor route, now formalized)

- Prove `IsConnected (permForwardOverlapSet n sigma)`
- Construct a nonempty open `W ⊆ permForwardOverlapSet` where
  `extendF F (sigma·w) = F w`
- Apply `extendF_perm_overlap_of_forward_open_anchor`

## Recommended next attack (most pragmatic)

1. **Prove a d>=2 theorem in `BHWPermutation`**:
   - `isConnected_permOrbitSeedSet_dge2` (or equivalent forward-overlap form)
2. Wire that into the existing helper:
   - `extendF_perm_overlap_dge2_of_seedConnected`
3. For d=1, introduce a dedicated complex-anchor theorem on
   `permExtendedOverlapSet` (no real-anchor assumptions).

This keeps the existing architecture and only fills the genuine geometric gap.

## Useful files

- Main blocker:
  - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`
- d>=2 Jost witness package:
  - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/JostWitnessGeneralSigma.lean`
- Adjacent overlap infrastructure:
  - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`
- d=1 orbit/slice tools:
  - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/IndexSetD1.lean`
  - `OSReconstruction/ComplexLieGroups/D1OrbitSet.lean`
- Probe notes/tests:
  - `test/iterated_eow_perm_ext_test.lean`
  - `test/proofideas_iterated_eow_perm_ext.lean`
  - `test/seed_connectedness_probe.lean`

## Quick check command

```bash
lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean
```

Expected currently: one warning for one declaration using `sorry`.
