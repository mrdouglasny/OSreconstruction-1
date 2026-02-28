# Proof Notes: `PermutationFlow.lean` Blocker (`iterated_eow_permutation_extension`)

This note records the current single remaining `sorry` on the critical path to the BHW theorem,
why it is hard, what is *actually missing*, and the systematic plan to close it without axioms.

## 0. Where The Blocker Lives

* File: `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`
* Lemma: `iterated_eow_permutation_extension`
* Location: around line ~2317 (the `sorry` immediately after defining `hExtPerm_of_seedOrbit`)

At that point the proof has already reduced everything to a local statement:

> For fixed `σ : Equiv.Perm (Fin n)`, prove `extendF` is permutation-invariant on the ET overlap:
> `∀ z, z ∈ ExtendedTube d n → permAct σ z ∈ ExtendedTube d n →
>     extendF F (permAct σ z) = extendF F z`.

The trivial branches `σ = 1`, `n ≤ 1`, and `d = 0` are already handled.
The remaining branch is `σ ≠ 1`, `n ≥ 2`, `d ≠ 0` (hence `1 ≤ d`).

## 1. What Is Already Available At The Blocker Site

Inside the nontrivial branch the file already constructs:

1. A **d ≥ 2** real Jost witness package:
   ```
   hJostWitness_hd2 :
     2 ≤ d →
     ∃ x : Fin n → Fin (d+1) → ℝ,
       x ∈ JostSet d n ∧
       realEmbed x ∈ ExtendedTube d n ∧
       realEmbed (x ∘ σ) ∈ ExtendedTube d n
   ```
   This is proved by `JostWitnessGeneralSigma.jostWitness_exists`.

2. A **reduction lemma**:
   ```
   hExtPerm_of_seedOrbit :
     (∃ x, x ∈ JostSet ∧ realEmbed x ∈ ET ∧ realEmbed (x∘σ) ∈ ET) →
     IsConnected (permOrbitSeedSet n σ) →
     ... → extendF invariance on ET-overlap ...
   ```
   It uses the internal lemma
   `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`,
   plus the equivalence
   `IsConnected permOrbitSeedSet ↔ IsConnected permForwardOverlapSet`.

So the `sorry` is not a dependent-type mismatch: it is a *real geometric/mathematical gap*.

## 2. The Core Difficulty: d = 1 Is Not Compatible With The “Real Witness In ET-Overlap” Strategy

We have a compiled scratch negative result:

* `test/d1_no_real_witness_swap_n2_probe.lean` proves (for `d = 1`, `n = 2`, `σ = swap`)
  there is **no** real `x : Fin 2 → Fin 2 → ℝ` with:
  `x ∈ JostSet 1 2`, `realEmbed x ∈ ExtendedTube 1 2`,
  and `realEmbed (x∘σ) ∈ ExtendedTube 1 2`.

Consequences:

1. Any lemma of the form “for `d = 1` and arbitrary `σ`, there exists a *real* Jost witness
   in the ET overlap” is **false**.
2. Therefore, the `PermutationFlow.lean` `sorry` cannot be closed by simply “adding a d=1 witness”
   and wrapping `1 ≤ d` into `d = 1 ∨ 2 ≤ d`.

This is the main reason this `sorry` has been a long-term blocker: the natural proof template
(`identity_theorem_totally_real_product` + real-open subset) fundamentally relies on having a
nonempty totally-real slice of the overlap. In `d = 1` this slice can be empty.

## 3. What The `sorry` Must Do (Truthfully)

The `sorry` must supply a proof of `hExtPerm` in the branch:

* `σ ≠ 1`
* `n ≥ 2`
* `d ≠ 0` (so `1 ≤ d`)

Given §2, a correct proof must either:

1. Split into cases and prove:
   * `2 ≤ d` using the real-witness strategy (already partially set up), and
   * `d = 1` using a different strategy that does not require real witnesses in the ET overlap;
   **or**
2. Replace the entire approach to `iterated_eow_permutation_extension` so it no longer needs
   `extendF` permutation invariance on ET overlaps.

## 4. d ≥ 2 Plan: Close The Remaining “Connectedness Of Forward-Overlap/Seed” Gap

For `2 ≤ d`, the witness package exists.
So the remaining missing ingredient for the current `hExtPerm_of_seedOrbit` route is:

* `IsConnected (permOrbitSeedSet (d := d) n σ)`
  (equivalently `IsConnected (permForwardOverlapSet (d := d) n σ)`).

In `PermutationFlow.lean` there is significant infrastructure for proving connectedness of
`permForwardOverlapSet` by slicing:

* `permForwardOverlapSet = ⋃ Λ, permForwardOverlapSlice Λ`, where each slice is convex.
* If the **index set** `{Λ | slice Λ nonempty}` is connected and the union is nonempty, then
  the union is connected (`isConnected_permForwardOverlapSet_of_indexConnected`).

There are also reductions:

* Seed-connected + seed-orbit-preconnected ⇒ index connected
  (`isConnected_permForwardOverlapIndexSet_of_seedConnected_and_seedOrbitPreconnected`).

But right now there is no theorem finishing “seed set connected” for general `σ`.

### Concrete next steps for d ≥ 2

1. Prove a new lemma (in a test file first) of the form:
   ```
   theorem isConnected_permOrbitSeedSet_hd2
     (hd2 : 2 ≤ d) (hn : 2 ≤ n) (σ : Perm (Fin n)) :
     IsConnected (permOrbitSeedSet (d := d) n σ)
   ```
   or equivalently for `permForwardOverlapSet`.

2. Once a test proof compiles, port it into `PermutationFlow.lean` to close the `d ≥ 2` branch
   of `hExtPerm`.

3. Keep the proof *structural*: lean on existing slice/index machinery rather than expanding
   low-level matrix computations.

## 5. d = 1 Plan: Abandon Real-Witness Propagation; Use A Different Analytic/Geometric Mechanism

Because real Jost witnesses in the ET overlap fail, the `d = 1` branch needs a different
argument. Options:

### Option A (likely correct): Prove `iterated_eow_permutation_extension` by actual iterated EOW gluing

This matches the standard BHW strategy:

* Use local commutativity on the **real spacelike edge** plus the SCV edge-of-the-wedge theorem
  (`OSReconstruction/SCV/TubeDomainExtension.lean`) transported through difference coordinates
  (`OSReconstruction/ComplexLieGroups/DifferenceCoordinatesSCV.lean`).
* Build extension data for permutations by adjacent transpositions.

Pros:
* Naturally handles `d = 1`.
* Avoids the “need a real-open subset inside ET overlaps” trap.

Cons:
* Requires implementing the “adjacent swap extension step” on *general extension domains*
  (the “Infrastructure gap” comment in `PermutationFlow.lean`).

### Option B: Prove the missing `hExtPerm` for `d = 1` directly using `SO(1,1;ℂ)` structure

Leverage `D1OrbitSet.lean` (explicit parametrization and preconnectedness results) to show
`extendF` invariance on the ET overlap without a real witness, likely via:

* group-parameter fiber connectedness + identity theorem on a complex-open subset,
  rather than a totally-real slice.

This is plausible but needs careful design: we must produce a set inside the overlap where
the difference `extendF(σz) - extendF(z)` is known to vanish with an accumulation point.

## 6. Why This Is Hard (and Why It’s Not “Just Lean”)

The blocker persists because:

1. The proof template currently in the file is tuned to *totally-real identity theorem*
   propagation, which requires a real open subset of the overlap.
2. For `d = 1`, that real subset can be empty for nontrivial permutations (rigorously).
3. The alternative “connectedness of the overlap” is not enough on its own; one still needs a
   non-discrete zero set for the holomorphic difference.

So the situation is:

* Not a statement typo (the target BHW theorem is true for `d = 1`).
* Not a Lean dependent-type issue.
* A genuine strategy mismatch: the real-witness propagation method has a true obstruction in `d = 1`.

## 7. Immediate Deliverables Checklist

* [ ] Close `d ≥ 2` branch in a test file by proving the required connectedness lemma.
* [ ] Decide/implement the `d = 1` proof route (Option A or B), in test files first.
* [ ] Only after test success: port into working file `PermutationFlow.lean` to remove the `sorry`.

## 8. Exact Lean Shape At The Blocker

Current `sorry` is exactly after the following local setup (abridged):

```lean
have hExtPerm :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (σ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (σ k)) = extendF F z := by
  by_cases hd0 : d = 0
  · ...
  · have hd1 : 1 ≤ d := ...
    have hJostWitness_hd2 :
        2 ≤ d →
        (∃ x : Fin n → Fin (d + 1) → ℝ,
          x ∈ JostSet d n ∧
          realEmbed x ∈ ExtendedTube d n ∧
          realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n) := by
      ...
    have hExtPerm_of_seedOrbit :
        (∃ x : Fin n → Fin (d + 1) → ℝ,
          x ∈ JostSet d n ∧
          realEmbed x ∈ ExtendedTube d n ∧
          realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n) →
        IsConnected (permOrbitSeedSet (d := d) n σ) →
        ∀ z, z ∈ ExtendedTube d n →
          permAct (d := d) σ z ∈ ExtendedTube d n →
          extendF F (permAct (d := d) σ z) = extendF F z := by
      ...
    sorry
```

So the missing object is not “some large missing proof”, but the final branch glue:

* `1 ≤ d` split into `d = 1` and `2 ≤ d`.
* `2 ≤ d` branch should go through `hJostWitness_hd2` + a connectedness theorem for `permOrbitSeedSet`.
* `d = 1` branch must use a non-real-witness method.

## 9. Confirmed d=1 Obstruction (From Compiled Tests)

`test/d1_no_real_witness_swap_n2_probe.lean` proves:

* `no_real_et_pair_swap_n2`
* `no_real_jost_witness_swap_n2`

for `d = 1`, `n = 2`, `σ = swap`. This means:

* there is no real overlap pair with both configurations in `ExtendedTube 1 2` under swap;
* strengthening with `JostSet` remains impossible.

Therefore a proposed lemma schema
“for all `d ≥ 1` and all `σ`, there exists a real witness in ET-overlap”
is mathematically false.

## 10. d≥2 Closure Target (Most Direct)

To close the `d≥2` subbranch at the blocker, the minimal useful theorem shape is:

```lean
theorem isConnected_permOrbitSeedSet_hd2
    (hd2 : 2 ≤ d) (hn2 : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    IsConnected (permOrbitSeedSet (d := d) n σ)
```

Equivalent target:

```lean
IsConnected (permForwardOverlapSet (d := d) n σ)
```

since `isConnected_permOrbitSeedSet_iff_permForwardOverlapSet` already exists.

Once this is available, `hExtPerm_of_seedOrbit` should close the `d≥2` branch with no new analytic ideas.

## 11. d=1 Route That Does Not Contradict The Obstruction

Use an EOW-based route that avoids real ET-overlap witnesses:

1. build adjacent-transposition extension/equality on complex domains (not via real-overlap identity set);
2. iterate along permutation decomposition;

## 12. Additional Structural Diagnosis (2026-02-28)

Two concrete facts now explain why the remaining `sorry` is hard:

1. `eow_adj_swap_on_overlap` is vacuous in the current setup.
   For nontrivial adjacent swaps, `ForwardTube ∩ swap·ForwardTube = ∅`
   (already encoded in the project), so this theorem cannot provide a
   nontrivial seed for the permutation chain.

2. The current successful propagation template
   (`extendF_perm_eq_on_connectedDomain_of_realOpen`) needs a totally-real
   open subset inside the ET-overlap domain. In `d = 1`, this subset can be
   empty for nontrivial permutations (verified in compiled tests).

Practical consequence:
- The remaining proof cannot be closed by "more of the same" real-witness route.
- A non-vacuous adjacent EOW mechanism (or equivalent complex-anchor method) is
  needed for the `d = 1` branch.

Reference context (book check):
- Streater-Wightman discusses real Jost points inside the extended tube via a
  convex-cone criterion (Theorem 2-12, Jost). This supports the `d ≥ 2`
  geometric route, but does not remove the `d = 1` real-overlap obstruction.

## 12. New Reduction Layer (compiled 2026-02-28)

A new test file
`test/extendf_perm_overlap_base_reduction_test.lean`
adds a sharper decomposition of the blocker.

For fixed `σ`, define the FT-base condition:

```lean
hBase :
  ∀ w ∈ ForwardTube d n,
    (fun k => w (σ k)) ∈ ExtendedTube d n →
    extendF F (fun k => w (σ k)) = F w
```

Compiled reductions:

1. `hBase` ⇒ full ET-overlap `extendF` invariance for `σ`.
2. ET-overlap `extendF` invariance for `σ` ⇒ forward-tube permutation invariance for `σ`.
3. Therefore `hBase` already implies the full fixed-`σ` target used in the blocker.

There is also an open-anchor propagation theorem on the connected forward-overlap
base domain:

*If `hBase` holds on one nonempty open subset of
`Ωσ := {w ∈ FT | σ·w ∈ ET}` and `Ωσ` is connected, then `hBase` holds on all `Ωσ`.*

This reframes the remaining work:

* construct a nonempty open anchor subset inside `Ωσ` where base equality is provable;
* prove connectedness of `Ωσ` (or equivalent seed/overlap connectedness route).

This reduction does not solve the blocker yet, but it removes unnecessary duplication
and isolates the unresolved part to one concrete geometric-analytic input.
3. plug result into `iterated_eow_permutation_extension` packaging.

The existing candidates to wire together:

* `OSReconstruction/SCV/TubeDomainExtension.lean`
* `OSReconstruction/ComplexLieGroups/DifferenceCoordinatesSCV.lean`
* `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`

## 12. Current Thoughts

The blocker persisted because the code already did strong reduction work, but that reduction hid a real theorem split:

* `d≥2` is mostly an infrastructure/connectedness closure task;
* `d=1` is a genuine method shift, not a missing line.

So the next high-yield move is to finish the `d≥2` connectedness theorem in a `test/` file first, then return to a clean `d=1` EOW implementation without forcing false witness lemmas.

## 13. Dead Routes (Verified)

### 13.1 Midpoint-condition induction route is false

The route based on proving a midpoint implication of the form

* if `Γ · ((σ * swap i) · w) ∈ ForwardTube` then `Γ · (σ · w) ∈ ForwardTube`

is not viable.

Compiled tests show explicit counterexamples:

* `test/midpoint_condition_counterexample_test.lean`:
  `midpoint_condition_identity_false_hd2` and `midpoint_condition_left_identity_false_hd2`
  (for `d ≥ 2`, `n ≥ 2`)
* `test/midpoint_condition_d1_counterexample_test.lean`:
  `midpoint_condition_identity_false_d1` (for `d = 1`, `n ≥ 2`)

So the early `hmidCond`-based branch in `PermutationFlow.lean` is useful only as
conditional infrastructure, not as a route to close the remaining `sorry`.

### 13.2 “Add a d=1 real Jost witness” route is false

Already covered in Sections 2 and 9 via:

* `test/d1_no_real_witness_swap_n2_probe.lean`

Hence the only viable d=1 route is a non-real-witness argument.

## 14. Next Implementation Target (Test-First)

Given Sections 9 and 13, the next concrete proving task is:

1. In `test/`, isolate a theorem that provides `IsConnected (permOrbitSeedSet)` for `d ≥ 2`.
2. Feed it to the already-constructed `hExtPerm_of_seedOrbit` pattern.
3. Keep the d=1 branch separate and do not force it through real Jost witnesses or midpoint implications.

## 15. Seed-Set Geometry Attempt (New)

Potential route for the remaining `d ≥ 2` blocker:

Write

`permOrbitSeedSet (σ) = ExtendedTube ∩ PermutedForwardTube σ⁻¹`.

Using

`ExtendedTube = ⋃ Λ, complexLorentzAction Λ '' ForwardTube`,

this gives a slice union

`permOrbitSeedSet (σ) = ⋃ Λ, (PermutedForwardTube σ⁻¹ ∩ complexLorentzAction Λ '' ForwardTube)`.

Each fixed-`Λ` slice is an intersection of convex open sets (linear image of `ForwardTube`
and `PermutedForwardTube`), hence preconnected.

What is still missing (Lean obligations):

1. A clean lemma identifying the correct index set for nonempty slices and relating it to
   `permForwardOverlapIndexSet` (up to inversion).
2. A connectedness theorem for that index set without assuming the strong/false global
   real double-coset generation hypothesis.
3. A slice-overlap refl-transitivity lemma in this seed-slice model (analog of existing
   index/slice machinery already used for forward-overlap sets).

Conclusion:

This route is structurally compatible with existing architecture, but still reduces to an
index-connectedness theorem that is currently the real geometric gap.

## 16. Reference Check (PCT Book)

Quick check of `references/pct-spin-and-statistics-and-all-that-...pdf`:

- Around printed pp. 82-83 (PDF pages 82-83), Streater-Wightman explicitly state:
  adjacent transposed extended tubes have a common real environment (constructed
  via a concrete Jost-point configuration).
- This matches the adjacent-swap infrastructure already formalized in
  `Adjacency.lean` (local overlap + EOW gluing), but does not directly provide
  global connectedness of the permutation overlap domains used in the remaining
  `iterated_eow_permutation_extension` blocker.

So the current blocker remains a global connectedness/input issue, not the
local adjacent real-overlap step.

## 17. Refactor Update (2026-02-28)

Implemented a structural cleanup in
`Connectedness/BHWPermutation/PermutationFlow.lean`:

- switched local seed/overlap definitions to reuse shared `SeedSlices` infrastructure;
- kept `permOrbitSeedSet` as a local alias to shared `permSeedSet`;
- rewired image/connectedness equivalence lemmas to shared proofs from `SeedSlices`;
- rewrote `mem_permForwardOverlapIndexSet_iff_exists_seed` to match the shared seed-set shape.

Status after refactor:

- compile is clean except for the single existing blocker `sorry`;
- blocker location moved to
  `PermutationFlow.lean:2156` (`iterated_eow_permutation_extension`).

## 18. Session Update (2026-02-28, late)

### 18.1 Build baseline repair

I fixed a Lean API mismatch introduced during refactor work:

- in `Adjacency.lean`, `Equiv.swap_apply_left` was called with an extra
  non-equality argument; current mathlib signature takes only the two points.
- after correction, targeted builds are back to baseline:
  - `Adjacency` builds;
  - `PermutationFlow` builds with exactly one warning:
    `PermutationFlow.lean:2156:16 declaration uses sorry`.

No axioms were added.

### 18.2 What the remaining hole actually needs

At the exact `sorry` site, the proof already has:

- `hJostWitness_hd2 : 2 ≤ d → (∃ real Jost witness in ET overlap)` and
- `hExtPerm_of_seedOrbit` reducing the ET-overlap identity to:
  1. existence of such a witness, and
  2. `IsConnected (permOrbitSeedSet (d := d) n σ)`.

So for `d ≥ 2`, the remaining unresolved ingredient in this local route is
still seed/forward-overlap connectedness.

For `d = 1`, the real-witness route is still obstructed (as in Sections 2/9).
Nothing in the current local inventory converts this branch to a completed proof
without introducing a genuinely different mechanism.

### 18.3 Route check against current infrastructure

I re-checked all existing local wrappers in `PermutationFlow`:

- `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`
- `..._of_jostWitness_and_real_double_coset_generation`
- `isConnected_permForwardOverlapSet_of_indexConnected`
- `isConnected_permForwardOverlapIndexSet_d1_of_seedConnected`

Current state:

- there is no theorem in-tree that directly supplies
  `IsConnected (permOrbitSeedSet ...)` for arbitrary `σ`;
- there is no theorem in-tree that supplies the strong `hgenPack` needed by the
  double-coset wrapper for arbitrary `σ`.

Therefore the blocker is a genuine missing geometric theorem (or theorem split),
not a Lean plumbing error.

### 18.4 Literature sanity check

I re-read the extracted Streater-Wightman text around Theorem 2-11 / Jost-point
discussion (`/tmp/pct_sw.txt` slices around lines ~4068 and ~4405).
This confirms the local adjacent-overlap/Jost machinery already formalized in
`Adjacency.lean`, but does not by itself provide the global connectedness input
needed at `PermutationFlow.lean:2156`.

## 19. Session Update (2026-02-28, current)

### 19.1 Midpoint route re-check: definitively blocked

I re-checked the alternative `d >= 2` route already present in
`PermutationFlow.lean`:

- `extendF_perm_overlap_of_adjSwap_connected_and_midCond_hd2`
- `eow_chain_adj_swap_of_midCond`

These require a "midpoint implication" of the form:

`Gamma · ((sigma * swap) · w) in FT -> Gamma · (sigma · w) in FT`.

This implication is explicitly false (not just unproved): see
`test/midpoint_condition_counterexample_test.lean`, which compiles and proves
counterexamples for the identity permutation in `d >= 2`, `n >= 2`.

So this branch cannot close the remaining sorry.

### 19.2 Current viable proof skeleton at the sorry site

At `PermutationFlow.lean:2254`, the only currently viable branch remains:

- get a witness (`hJostWitness_hd2`) for `d >= 2`,
- reduce via `hExtPerm_of_seedOrbit`,
- supply `IsConnected (permOrbitSeedSet (d := d) n sigma)`.

No in-tree theorem currently supplies this connectedness for arbitrary
permutation `sigma`.

### 19.3 d = 1 status remains separate

As before, the "real Jost witness for arbitrary sigma" route is obstructed for
`d = 1`; this is not a Lean artifact.

In current code, there is useful `d = 1` infrastructure (`IndexSetD1`,
`orbitSet_isPreconnected_d1`, slice connectivity lemmas), but no finished bridge
from that infrastructure to the exact overlap identity used in
`iterated_eow_permutation_extension`.

### 19.4 External consultation attempt

A fresh Gemini consultation was attempted with the exact local context prompt for
the remaining branch. The command returned an empty response file, so no
actionable external proof strategy was obtained in this run.

### 19.5 Small infrastructure cleanup landed

`PermutationFlow.lean` now imports `BHWPermutation/IndexSetD1` and reuses
`orbitSet_isPreconnected_d1_of_mem_extendedTube` from that shared file,
removing a duplicated local d1 helper theorem.

This is a pure refactor (no theorem-strength change): build still succeeds with
exactly one remaining `sorry` in `iterated_eow_permutation_extension`.

## 20. Session Update (2026-02-28, later)

### 20.1 Seed-slice convexity infrastructure added

In `BHWPermutation/SeedSlices.lean`, I added:

- `permutedForwardTube_convex`
- `permSeedSlice_convex`
- `permSeedSlice_isPreconnected`
- `permSeedSet_eq_inter_permutedForwardTube`
- `isOpen_permSeedSet`
- `permSeedSet_nonempty_iff_permForwardOverlapSet_nonempty`

All compile cleanly and are intended for the seed-connectedness route
(`permSeedSet = ET ∩ sigmaFT` as a union of fixed-`Lambda` seed slices).

### 20.2 New bridge theorem in PermutationFlow

Added:

- `extendF_perm_overlap_of_jostWitness_and_indexConnected`

This theorem packages:

- local Jost witness
- `IsConnected (permForwardOverlapIndexSet ...)`

into the target overlap identity for `extendF`.

It gives a cleaner target for the remaining branch (index-connectedness can now
be used directly, without first manually producing forward-overlap connectedness
at each call site).

The remaining `sorry` site was refactored accordingly: the local reduction now
targets

- `IsConnected (permForwardOverlapIndexSet (d := d) n sigma)`

rather than directly phrasing the gap as seed-connectedness.

I also rewired
`extendF_perm_overlap_of_jostWitness_and_real_double_coset_generation` to use
this bridge theorem via index-connectedness.

### 20.3 Build status

Targeted builds pass:

- `SeedSlices`
- `PermutationFlow`
- `Connectedness.BHWPermutation`

with one remaining warning:

- `PermutationFlow.lean:2177` declaration uses `sorry`.

### 20.4 Refactor: seed-connected reduction wrapper

Added a new local wrapper theorem in `PermutationFlow.lean`:

- `extendF_perm_overlap_of_jostWitness_and_seedConnected`

This packages the already-proved equivalence

- `isConnected_permOrbitSeedSet_iff_permForwardOverlapSet`

with the existing local-witness theorem

- `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`.

Then the remaining `sorry` block in
`iterated_eow_permutation_extension` was cleaned to use this wrapper directly
(`hExtPerm_of_seedConnected`) and remove dead intermediate scaffolding.

Net effect:

- no theorem-strength change,
- no additional gaps introduced,
- blocker shape is now explicit:
  - `d >= 2`: needs seed connectedness input (`permOrbitSeedSet`),
  - `d = 1`: needs a separate non-real-Jost mechanism.

Current build still succeeds with exactly one remaining `sorry` warning at:

- `PermutationFlow.lean:2210`.

### 20.5 Wrapper Cleanup Policy Applied

The temporary wrapper-style reductions introduced during exploration were
removed to keep theorem flow direct and hypothesis-explicit.

Removed local wrappers:

- `extendF_perm_overlap_of_forwardOverlapConnected_and_openAnchor`
- `extendF_perm_overlap_of_jostWitness_and_seedConnected`

The remaining blocker branch now references the underlying core route directly:

- convert seed connectedness via
  `isConnected_permOrbitSeedSet_iff_permForwardOverlapSet`,
- apply `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`.

Targeted build still passes with exactly one warning:

- `PermutationFlow.lean:2177` declaration uses `sorry`.
