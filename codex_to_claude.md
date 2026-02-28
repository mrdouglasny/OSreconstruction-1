# Codex -> Claude: Request for Blocker-B Proof Assistance

## Context

We are down to one remaining `sorry` on the BHW path:

- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`
- inside `iterated_eow_permutation_extension`
- around line ~1490 in the nontrivial branch (`σ ≠ 1`, `n ≥ 2`, `d ≥ 1`)

Current goal there is to build:

```lean
hExtPerm :
  ∀ z, z ∈ ExtendedTube d n →
    permAct (d := d) σ z ∈ ExtendedTube d n →
    extendF F (permAct (d := d) σ z) = extendF F z
```

Current branch status has been refactored:

- new wrapper in working file:
  `extendF_perm_overlap_of_jostWitness_and_seedConnected`
- local hole now explicitly reduces to:
  - `d >= 2`: provide `IsConnected (permOrbitSeedSet (d := d) n σ)`
    together with existing `JostWitnessGeneralSigma.jostWitness_exists`;
  - `d = 1`: separate mechanism (cannot rely on real Jost witness).

So the blocker is no longer phrased as index-connectedness/double-coset generation
at this site; it is now seed-connectedness + d=1 completion.

## Non-negotiable constraints

1. No `axiom`, no assumption-smuggling.
2. Do not alter definitions to "simplify away" math content.
3. Test-first workflow: prove in `test/*.lean` first, then port.
4. Keep wrappers minimal; prefer direct theorem statements when possible.

## What we need from Claude

Please propose and (if possible) implement a proof route that **eliminates the final `sorry`** in `PermutationFlow.lean`.

### Deliverables

1. A concrete plan selecting one of:
   - prove `IsConnected (permOrbitSeedSet (d := d) n σ)` in `d >= 2` plus a valid `d = 1` route;
   - or provide a mathematically valid refactor of
     `iterated_eow_permutation_extension`/`eow_chain_adj_swap` that avoids this
     seed-connectedness obligation while preserving BHW assumptions.
2. A compilable test file:
   - `test/claude_blockerB_close_attempt.lean`
3. If successful in test, a minimal patch for working files.
4. If not successful, a precise diagnosis:
   - which statement is too strong / incorrect,
   - what corrected intermediate theorem should replace it,
   - exact downstream call-site changes needed.

## Technical notes from current state

- False routes already ruled out by tests:
  - midpoint implication route (counterexample exists)
  - global bridge `∀ x ∈ JostSet, realEmbed x ∈ ExtendedTube` (counterexample exists)
- ET midpoint implication is also false (compiled):
  - `test/jostset_et_counterexample_test.lean`
  - theorem:
    `BHW.midpoint_condition_identity_false_ET {d : ℕ} (hd : 1 ≤ d) :
      ¬∀ (y : Fin 3 → Fin (d + 1) → ℂ),
        (fun k => y (swap12 k)) ∈ ExtendedTube d 3 → y ∈ ExtendedTube d 3`
- Useful local infrastructure already in `PermutationFlow.lean`:
  - `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`
  - `extendF_perm_overlap_of_jostWitness_and_seedConnected`
  - `extendF_perm_overlap_of_jostWitness_and_real_double_coset_generation`
  - `permInvariance_forwardTube_iff_extendF_overlap`
- Adjacent-swap infrastructure in:
  - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`

## Additional constraints from current diagnostics

- A naive proof of `ExtendedTube` permutation invariance by witness transport fails:
  proving `ForwardTube` permutation invariance is required and is false in general.
- So any route reducing the blocker to an ET midpoint condition or ET permutation
  invariance should be treated as invalid unless new nontrivial geometric lemmas
  are supplied.
- For `d = 1`, test probes show no global real-Jost witness package for general
  permutations (e.g. transposition on `Fin 2`), so do not propose that route.

## Preference

Prefer a mathematically honest route that keeps `bargmann_hall_wightman_theorem` statement unchanged and avoids introducing strong global assumptions that are known false.
