# d=1 Attack Notes for `PermutationFlow` Blocker

This note targets the `d = 1` sub-branch of the remaining sorry in
`PermutationFlow.lean` (`iterated_eow_permutation_extension`).

## What fails (already formalized)

1. Real-anchor route via Jost witness is unavailable in general:
- no real ET pair / Jost witness for `n=2`, adjacent swap (probe theorem).

2. Midpoint-drop chain route is false in `d=1`:
- the implication
  `Γ·((σ*swap)·w) ∈ FT -> Γ·(σ·w) ∈ FT`
  fails (counterexample theorem in test).

So the `d>=2` strategy does not port.

## Existing strong d=1 infrastructure

From `D1OrbitSet.lean` and `IndexSetD1.lean`:

- `SO^+(1,1;C)` rapidity normal form (`a + i b`).
- principal imaginary strip control (`|b| < pi`) for orbit witnesses.
- orbit preconnectedness in d=1:
  - `orbitSet_isPreconnected_d1` / wrappers.
- fixed-slice connectedness for ET witnesses:
  - `permLambdaSlice_isConnected_d1_of_perm_mem_ET`.

This is enough to do serious geometric work without introducing assumptions.

## Likely viable theorem shape to add

A d=1 replacement for real-Jost anchoring should avoid real points and use
complex open anchoring in the ET-overlap domain.

Candidate target:

```lean
private theorem extendF_perm_overlap_d1_of_complex_anchor
  ... :
  forall z in ET,
    permAct sigma z in ET ->
    extendF F (permAct sigma z) = extendF F z
```

Proof outline candidate:

1. Set `D := permExtendedOverlapSet (d := 1) n sigma`.
2. Prove `IsConnected D` from connectedness of `permForwardOverlapSet`.
3. Build a complex-open nonempty `V ⊆ D` where equality is known.
4. Apply `extendF_perm_eq_on_connectedDomain_of_openSubset`.
   (or directly `extendF_perm_overlap_of_forward_open_anchor`
   from `OverlapAnchor.lean` after proving connectedness + anchor on
   `permForwardOverlapSet`).

The only hard part is step (3): constructing `V` without real Jost points.

## Concrete subgoals for step (3)

For a fixed permutation `sigma`:

1. Build an analytic family of overlap witnesses parameterized by d=1 rapidity.
2. Show the family stays inside `D` on an interval (pure-imag rapidity segment).
3. Prove `extendF` equality along that family by adjacent EOW + Lorentz transport.
4. Extract an open neighborhood `V` in complex coordinates.

The rapidity segment lemmas already exist in `D1OrbitSet.lean` and should be
reused directly.

## Why this is plausible

- d=1 group geometry is explicit (one complex rapidity parameter).
- Existing lemmas already control cone membership along rapidity segments.
- This removes dependence on non-existent real spacelike anchors.

## Immediate coding checklist

1. Add a d=1-specific lemma in `PermutationFlow.lean` that restates the needed
   rapidity-segment invariance in the `permExtendedOverlapSet` language.
2. Add a helper converting d=1 rapidity-strip witnesses to nonempty open anchor
   subsets `V`.
3. Use `extendF_perm_eq_on_connectedDomain_of_openSubset` to close the d=1 branch.
