# d>=2 Seed Connectedness Notes for `PermutationFlow`

This note targets the missing geometric input:

```lean
IsConnected (permOrbitSeedSet (d := d) n sigma)
```

in the `d >= 2` branch of the remaining sorry.

## Where it is used

`PermutationFlow.lean` already has:

- `extendF_perm_overlap_dge2_of_seedConnected`

So once seed connectedness is proved, ET-overlap invariance `hExtPerm` follows
immediately for `d>=2`.

Also available now in production:

- `OverlapAnchor.lean`:
  - `forward_base_eq_of_open_anchor`
  - `extendF_perm_overlap_of_forward_open_anchor`

So a successful connectedness proof can be paired with an open-anchor equality
instead of the Jost-witness chain, if that anchor is easier to construct.

## Existing reductions already available

1. `isConnected_permOrbitSeedSet_iff_permForwardOverlapSet`
2. `isConnected_permForwardOverlapSet_of_indexConnected`
3. `isConnected_permForwardOverlapIndexSet_of_seedConnected_and_seedOrbitPreconnected`

Current cycle:
- seed connectedness is both target and an input to index connectedness route.

Need a truly independent proof of seed or forward-overlap connectedness.

## Structural identity to exploit

- `permOrbitSeedSet = ET ∩ PermutedForwardTube sigma^{-1}`
- `PermutedForwardTube ...` is convex/open.
- `ET` is connected/open and Lorentz-saturated.

The challenge is connectedness of the intersection.

## Candidate independent strategy

Work on forward-overlap set directly:

```lean
W := permForwardOverlapSet (d := d) n sigma
   = { w in FT | sigma w in ET }
```

### Proposed plan

1. Show `W` is nonempty from `JostWitnessGeneralSigma.jostWitness_exists`.
2. Build explicit path from any `w in W` to a canonical witness `w0 in W` while
   staying inside `W`.
3. Conclude path-connectedness, hence connectedness.

### Technical ingredients likely needed

- Convexity of `FT` (already available).
- Lorentz action continuity on configuration space (available).
- A controllable witness map `w -> Λ_w` with `Λ_w (sigma w) in FT` that varies
  continuously along the path (this is the hard new lemma).

## Alternative (index-space) plan

Avoid seed-space path construction; prove connectedness of
`permForwardOverlapIndexSet` directly by a parameterization argument in `d>=2`
(rank-1 style decomposition), then use existing theorem:

- `isConnected_permForwardOverlapSet_of_indexConnected`.

This requires a new theorem stronger than current local orbit-preconnected
infrastructure but may be cleaner than constructing `w -> Λ_w` globally.

## Immediate coding checklist

1. Add a dedicated theorem skeleton in `PermutationFlow.lean`:
   - `isConnected_permForwardOverlapSet_dge2` (or seed equivalent).
2. Isolate all required auxiliary lemmas in a new local section so failures are
   localized to true geometric core only.
3. Once established, replace the `d>=2` part of the sorry with
   `extendF_perm_overlap_dge2_of_seedConnected`.
