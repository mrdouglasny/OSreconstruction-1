# Connectivity + EOW Insight (Detailed Discussion)

This note consolidates the precise mathematical conclusions from the recent
discussion and maps them to the current Lean architecture in
`BHWPermutation/PermutationFlow.lean`.

The main point is:

- EOW is the right local analytic bridge from boundary equality to interior
  holomorphic equality.
- Global permutation overlap equality needs more than local gluing: it needs
  a globalization mechanism (connectedness + uniqueness anchor in the target
  domain).

## 1. Precise target identity in the blocker

For fixed `σ : Equiv.Perm (Fin n)`, the overlap target is:

`hExtPerm`:
`forall z, z ∈ ExtendedTube d n -> permAct σ z ∈ ExtendedTube d n ->
  extendF F (permAct σ z) = extendF F z`.

Equivalently, if

`Dσ := { z | z ∈ ET and σ·z ∈ ET }`

and

`gσ(z) := extendF F (σ·z) - extendF F z`,

the target is `gσ = 0` on all of `Dσ`.

## 2. What is assumed about `F` initially

In the BHW setup, we assume:

1. Holomorphicity on forward tube:
   `hF_holo : DifferentiableOn ℂ F (ForwardTube d n)`.
2. Lorentz invariance on forward tube:
   `hF_lorentz`.
3. Boundary regularity at real points:
   `hF_bv : ContinuousWithinAt F (ForwardTube d n) (realEmbed x)`.
4. Local commutativity at real spacelike points:
   `hF_local`.

Important:

- We do not assume `F` is holomorphic on ET a priori.
- ET-holomorphicity comes from the extension construction (`extendF` and related
  theorems).

## 3. Why connectedness by itself is insufficient

Connectedness of `Dσ` does not imply `gσ = 0`.

It only gives uniqueness *if* we already know `gσ` vanishes on a uniqueness set
inside `Dσ` (for example:

1. nonempty open complex subset of `Dσ`, or
2. nonempty open subset of a totally real submanifold inside `Dσ` under the
   identity theorem infrastructure used in this project).

So propagation is:

`holomorphic on Dσ + uniqueness-set vanishing + Dσ connected -> global vanishing`.

Not just:

`holomorphic on Dσ + Dσ connected -> global vanishing`.

## 4. Why EOW is essential but still local

Boundary equality data from `hF_bv + hF_local` is on real spacelike points,
which are boundary/edge data relative to tube domains.

EOW gives the local bridge:

1. start with two holomorphic sides (e.g. `F` and `F∘swap` on adjacent tube
   domains),
2. assume matching boundary traces on a real edge set,
3. conclude a holomorphic glued function on a complex neighborhood crossing the
   edge.

This yields interior equality on that local glued neighborhood.

What EOW does not automatically give by itself:

- global equality on all of `Dσ` for arbitrary `σ` without additional cover/
  chain/connectedness arguments.

## 5. "Repeated analytic continuation" vs "connectedness + anchor"

These are two descriptions of the same globalization logic.

### Patchwise continuation view

You prove equality patch by patch:

1. equality on one patch,
2. overlap transfer to neighboring patch,
3. continue along a chain of overlapping patches.

To make this rigorous you still need:

1. enough patches to cover the target component,
2. nontrivial overlaps supplying transfer,
3. no path inconsistency (uniqueness handles this).

### Identity-theorem view

You package the same structure as:

1. connected domain `D`,
2. holomorphic difference `g`,
3. one uniqueness anchor set where `g=0`.

Then identity theorem gives `g=0` on all `D`.

So "repeat extension" is not weaker; it is equivalent proof content reorganized.

## 6. Open anchor is sufficient, not necessary

A complex-open anchor subset is convenient, but stronger than needed.

The codebase already supports a weaker and often more natural uniqueness route:

- `Adjacency.lean` has
  `extendF_perm_eq_on_connectedDomain_of_realOpen`,
  using identity theorem on totally real data.

Hence:

- We do not need a complex-open anchor in principle.
- We need *some* uniqueness-valid anchor set in the relevant connected domain.

Open-anchor wrappers in `OverlapAnchor.lean` are convenience interfaces, not a
logical necessity.

## 7. Explicit `d = 1, n = 2` framing

For two points `z1, z2` in complexified `1+1` Minkowski:

`z_i = (z_i^0, z_i^1) in C^2`.

Forward tube condition:

`Im(z2^0 - z1^0) > |Im(z2^1 - z1^1)|`.

For swap `σ(1)=2, σ(2)=1`, the overlap domain is:

`Dσ = { z in ET | σ·z in ET }`.

In this case, known probes indicate the naive real-anchor strategy used in
`d>=2` does not transfer uniformly. That is why the remaining `d=1` step is a
separate bridge theorem rather than just reusing the high-dimensional witness
package.

## 8. Existing formal infrastructure (already available)

### Local EOW / adjacency layer

- `eow_adj_swap_on_overlap` (`Adjacency.lean`)
- `extendF_adjSwap_eq_of_connected_overlap` (`Adjacency.lean`)
- `extendF_perm_eq_on_connectedDomain_of_realOpen` (`Adjacency.lean`)

### Open-anchor globalization wrappers

- `extendF_perm_overlap_of_open_anchor_and_forwardOverlapConnected`
  (`OverlapAnchor.lean`)
- `forward_base_eq_of_open_anchor` (`OverlapAnchor.lean`)
- `extendF_perm_overlap_of_forward_open_anchor` (`OverlapAnchor.lean`)

These wrappers can be used when complex-open anchors are easier to construct,
but they are not mandatory if a totally-real uniqueness route is cleaner.

## 9. Current blocker decomposition in `PermutationFlow`

The original single blocker was replaced by explicit deferred obligations:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_extendF_perm_overlap_d1_of_seedConnected`

Interpretation:

1. and 2. are geometric connectivity inputs (dimension split).
3. is the `d=1` analytic bridge:
   from `d=1` seed connectedness (plus BHW hypotheses) to full ET-overlap
   equality `hExtPerm`.

So the original monolithic difficulty is now exposed as:

1. connectivity theorems, plus
2. one explicit `d=1` globalization bridge theorem.

## 10. Why the third deferred lemma is not "just connectivity"

The third lemma includes full analytic hypotheses and concludes `hExtPerm`.
Connectivity is one hypothesis inside it, but it still must construct/obtain a
uniqueness anchor in the relevant overlap domain and run identity-theorem
propagation.

In short:

- first two deferred lemmas: pure geometry,
- third deferred lemma: geometry + analytic propagation packaging.

## 11. Suggested proof shape for the third deferred lemma

There are at least two viable routes.

### Route A: Totally-real anchor route

1. derive connectedness of forward-overlap set from seed connectedness in `d=1`,
2. produce a real-open anchor subset where equality holds (using local EOW and
   `hF_bv/hF_local`),
3. apply `extendF_perm_eq_on_connectedDomain_of_realOpen` style propagation to
   get global ET-overlap equality.

### Route B: Open-anchor route

1. derive forward-overlap connectedness,
2. build nonempty open complex anchor `W` with base equality
   `extendF(σ·w)=F(w)` on `W`,
3. apply `extendF_perm_overlap_of_forward_open_anchor`.

Both routes are valid; A uses weaker anchor assumptions and matches existing
totally-real uniqueness templates, while B offers a cleaner wrapper interface
once an open anchor is available.

## 12. Practical conclusion

The central conceptual confusion is resolved:

1. EOW is enough for local boundary-to-interior transfer.
2. Globalization still needs uniqueness propagation data (anchor + connectedness).
3. This is exactly what the deferred split now isolates.

Therefore, the remaining work is no longer "find the big mysterious analytic
step", but:

1. prove the two connectivity inputs, and
2. implement one concrete `d=1` globalization bridge theorem using existing
   identity-theorem infrastructure.

## 13. Concrete recipe for the third deferred lemma (`d = 1` bridge)

Target deferred lemma:

- `deferred_extendF_perm_overlap_d1_of_seedConnected`
  (`PermutationFlow.lean`)

Input:

1. `hseed_conn : IsConnected (permOrbitSeedSet (d := 1) n σ)`,
2. analytic hypotheses `hF_holo`, `hF_lorentz`, `hF_bv`, `hF_local`.

Output:

`forall z in ET, σ·z in ET -> extendF(σ·z)=extendF(z)`.

### 13.1 Preferred structure

Use existing wrapper theorem:

1. turn seed connectedness into forward-overlap connectedness:
   `isConnected_permOrbitSeedSet_iff_permForwardOverlapSet` (with `d := 1`),
2. prove base identity on `Ωσ := {w in FT | σ·w in ET}`,
3. apply:
   `extendF_perm_overlap_of_forward_base`.

This keeps the bridge proof short and isolates the hard part in step (2).

### 13.2 What exactly step (2) must prove

Need:

`hBase : forall w in FT, σ·w in ET -> extendF(σ·w)=F(w)`.

Equivalent form:

`g_base(w) := extendF(σ·w) - F(w)` vanishes on all of `Ωσ`.

### 13.3 Two implementation options for `hBase`

Option A (real/totally-real uniqueness):

1. pick connected domain `Ωσ`,
2. prove holomorphicity of `w ↦ extendF(σ·w)` on `Ωσ`,
3. use local EOW/locality to show equality on a nonempty real-open subset
   `V ⊆ Ωσ` (in real subspace),
4. apply identity theorem template (totally-real version) on `Ωσ`.

Option B (open complex anchor):

1. construct nonempty open complex `W ⊆ Ωσ`,
2. prove base equality on `W`,
3. apply `forward_base_eq_of_open_anchor`,
4. then apply `extendF_perm_overlap_of_forward_base`.

Both are valid. Option A requires less topological strength on the anchor set.

## 14. Lean-level proof skeleton (for direct coding)

```
have hFwd_conn : IsConnected (permForwardOverlapSet (d := 1) n σ) := by
  exact (isConnected_permOrbitSeedSet_iff_permForwardOverlapSet (d := 1) n σ).1 hseed_conn

have hBase :
  ∀ w, w ∈ ForwardTube 1 n ->
    permAct (d := 1) σ w ∈ ExtendedTube 1 n ->
    extendF F (permAct (d := 1) σ w) = F w := by
  -- prove by Option A or B

exact extendF_perm_overlap_of_forward_base (d := 1) (n := n)
  F hF_holo hF_lorentz σ hBase
```

This is the intended endpoint for the deferred bridge theorem.

## 15. Minimal sublemma checklist for Option A

If following the totally-real route, define these helper goals explicitly:

1. `hOmega_open` and `hOmega_conn` for `Ωσ`.
2. `hDiff_holo` for
   `w ↦ extendF(σ·w) - F(w)` on `Ωσ`.
3. `exists V` with:
   - `IsOpen V` (real topology),
   - `V.Nonempty`,
   - `realEmbed(V) ⊆ Ωσ`,
   - equality on `realEmbed(V)`.
4. one call to the project identity theorem helper.

Having these as named lemmas will make the third deferred theorem mostly
assembly, not monolithic proof search.

## 16. Common failure modes to avoid

1. Trying to deduce global equality from connectedness alone (missing anchor).
2. Using boundary-trace equality directly without first obtaining interior
   uniqueness data (EOW/locality bridge step skipped).
3. Mixing domains:
   proving equality on adjacent-swap overlap but concluding on full `σ`-overlap
   without a chain/globalization argument.
4. Implicitly assuming real Jost witness existence in `d=1`.

## 17. Suggested immediate coding order

1. In `PermutationFlow.lean`, inside the third deferred lemma, write the final
   3-line assembly skeleton first (`hFwd_conn`, `hBase`, final wrapper).
2. Create placeholder local helper lemmas for `hBase` components (open/conn/
   anchor/equality) right above it.
3. Fill helpers one by one, testing after each.
4. Keep connectivity lemmas deferred as planned; do not mix geometry closure
   with `hBase` construction.
