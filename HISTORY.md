# Development History: OS Reconstruction Formalization

## Xiyin's Repo (commits `2b86bea`–`2dfc99a`)

Everything below was done in xiyin's repo and merged into ours at `47a4076`.

### Initial Framework (`2b86bea`)

The initial commit with vNA and Wightman axiom definitions, OS axiom framework,
WickRotation.lean skeleton, Reconstruction.lean, AnalyticContinuation.lean, and
the von Neumann algebra modules.

### SeparatelyAnalytic (`3219c29`–`d53bad6`)

`SeparatelyAnalytic.lean` (906 lines added) — Taylor series and separately analytic
function infrastructure. Went from 25 sorrys to 0 (sorry-free).

### Edge-of-the-Wedge (`4221277`–`328decb`)

- **`edge_of_the_wedge_slice`** (`AnalyticContinuation.lean:553`, sorry-free) —
  1D EOW: for each x₀ ∈ E and η ∈ C, extends f_plus and f_minus to a single
  holomorphic function along the slice w ↦ x₀ + wη
- `edge_of_the_wedge_1d` — Full 1D EOW via Morera + Cauchy-Goursat
- `sliceMap` infrastructure — `sliceMap_upper_mem_tubeDomain`, etc.
- `tubeDomain_isOpen`, `neg_image_isOpen`, `tubeDomain_disjoint_neg`
- `holomorphic_extension_across_real`, `tube_domain_gluing`
- Promoted `edge_of_the_wedge` and `bargmann_hall_wightman` to named axioms

### SCV Infrastructure (`1ab849b`, `2dfc99a`)

- **`Osgood.lean`** (627 lines, sorry-free) — Osgood's lemma
- **`Polydisc.lean`** (231 lines, sorry-free) — Polydisc definitions
- **`IteratedCauchyIntegral.lean`** (670 lines) — Iterated contour integrals
- **`TubeDomainExtension.lean`** (2997 lines) — Tube domain extension theory
- **`Analyticity.lean`** (1206 lines) — Multi-variable holomorphic ⟹ analytic
- **`MoebiusMap.lean`** (618 lines) — Möbius product map
- **`EOWMultiDim.lean`** (141 lines) — Multi-dimensional EOW helpers

### Complex Lie Groups (`062e64f`)

- `MatrixLieGroup.lean` (277), `LorentzLieGroup.lean` (283),
  `Complexification.lean` (533), `Connectedness.lean` (171)

### Bridge (`435829c`)

- `Bridge/AxiomBridge.lean` (252 lines) — Type equivalences between SCV/Lie
  group infrastructure and Wightman axiom types

### OS Axiom Fixes (`4508b8e`)

- Fixed OS axioms E1/E2, added Osgood lemma, exponential map infrastructure

---

## Our Work: Before the Merge (6 commits)

These commits branch from xiyin's `2dfc99a` and were merged alongside it.

### GaussianFieldBridge (`87d95e1`–`cf96b5b`, simplified `f905e04`)

- **`GaussianFieldBridge.lean`** (149 lines, sorry-free) — Bridges the gaussian-field
  library (sorry-free Hermite functions, spectral theorem, Gaussian measure,
  Pietsch nuclear space definition) to the project's nuclear space infrastructure
- The Pietsch nuclear space definition (`PietschNuclearSpace`) and the
  Dynin-Mityagin → Pietsch bridge proof (`toPietschNuclearSpace`) now live
  in gaussian-field (`Nuclear/PietschNuclear.lean`). The bridge file provides
  a trivial conversion to OSReconstruction's `NuclearSpace` typeclass.
- **`nuclear_step`** sorry eliminated — direct proof for n=0, gaussian-field
  bridge for n>0
- **`SchwartzNuclear.lean`** reworked (237 lines changed)

### R→E OS Axioms (`8fc7b9c`–`be5b63a`)

This is the core physics content: proving that Wightman functions satisfying R0–R4
produce Schwinger functions satisfying E0–E4.

**`constructSchwingerFunctions`** (`WickRotation.lean:190`) — Defines S_n(f) as:
```
S_n(f) = ∫ F_ext(iτ₁,x⃗₁,...,iτ_n,x⃗_n) · f(x₁,...,x_n) dx
```
where F_ext is the BHW extension of W_analytic to the permuted extended tube.

**`W_analytic_BHW`** (line 155) — Wires `spectrum_condition` into `bargmann_hall_wightman`
to produce the BHW extension with complex Lorentz and permutation invariance.

### SCV Identity Theorem (`8fc7b9c`)

- **`SCV/IdentityTheorem.lean`** (154 lines) — `identity_theorem_SCV` and tube
  domain specialization, reducing to single sorry (`hartogs_analyticity`)

---

## Our Work: After the Merge (12 commits, 8 substantive)

### Lorentz Invariance (`0306f8d`)

**`W_analytic_lorentz_on_tube`** — Proves that the analytic Wightman
function is Lorentz-invariant on the forward tube. Four helper lemmas:

- `restricted_preserves_forward_cone` — SO⁺(1,d) preserves V₊ (metric preservation
  via Lorentz condition + time component positivity via Cauchy-Schwarz). Sorry-free.
- `restricted_preserves_forward_tube` — Λ preserves forward tube (Im linearity +
  above). Sorry-free.
- `W_analytic_lorentz_holomorphic` — z ↦ W_analytic(Λz) is holomorphic (ℂ-linearity
  of Lorentz action + Finset induction for DifferentiableAt). Sorry-free.
- `W_analytic_lorentz_bv_agree` — Distributional BVs match (via two textbook axioms).

Final proof applies `distributional_uniqueness_forwardTube`.

### R→E E3/E1 Proofs + Axiom Infrastructure

- `constructedSchwinger_symmetric` (E3) — sorry-free via `integral_perm_eq_self`
- `constructedSchwinger_translation_invariant` (E1a) — sorry-free via
  `bhw_translation_invariant` axiom + `euclidean_points_in_permutedTube` axiom
- `constructedSchwinger_rotation_invariant` (E1b, det=1) — sorry-free via
  `schwinger_euclidean_invariant` + `integral_orthogonal_eq_self`
- `F_ext_permutation_invariant` — sorry-free from BHW permutation symmetry
- `F_ext_translation_invariant` — from bhw_translation_invariant axiom
- `F_ext_rotation_invariant` (det=1) — via complex Lorentz group embedding

### E→R Analytic Continuation Axioms

- `inductive_analytic_continuation` — converted from sorry to axiom with detailed
  Paley-Wiener docstring (OS II Theorem 4.1: one-variable half-plane extension)
- `bochner_tube_theorem` — added to SCV/TubeDistributions.lean (holomorphic on
  T(C) extends to T(conv C))
- `full_analytic_continuation` docstring updated with 3-step proof strategy:
  iterate Paley-Wiener + E1 rotation + Bochner tube theorem

### Bridge Theorem Proofs

- **`os_to_wightman_full` (E'→R')** — fully proved, sorry-free. Extracts fields
  from `boundary_values_tempered` dependent tuple to satisfy `IsWickRotationPair`.
- **`wightman_to_os_full` (R→E)** — sorry-free. Uses 3 textbook axioms:
  `analytic_boundary_local_commutativity` (Jost-Lehmann-Dyson, S-W Thm 3-5),
  `bhw_distributional_boundary_values` (S-W Thm 2-11, sidesteps coordinate convention
  mismatch), and `wick_rotated_schwinger_tempered` (OS I Prop 5.1).

### Forward Tube Distributions (`b381e5d`–`b655699`)

Two new files totaling **764 lines**, completing the infrastructure that
WickRotation.lean depends on.

**`ForwardTubeDistributions.lean`** — sorry-free (591 lines), 29 definitions
and theorems:

*Forward cone properties:*
- `ForwardConeAbs` — product cone in difference coordinates
- `forwardConeAbs_isOpen`, `_convex`, `_nonempty`
- `convex_inOpenForwardCone` — V₊ is convex (Cauchy-Schwarz on spatial components)
- `inOpenForwardCone_smul` — V₊ closed under positive scaling
- `inOpenForwardCone_add` — V₊ closed under addition (via convexity + scaling)
- `forwardConeAbs_implies_allForwardCone` — ForwardConeAbs ⊆ {η | ∀k, η_k ∈ V₊}
  (key bridge between approach direction conventions)

*Flattening equivalence:*
- `flattenCLEquiv` / `flattenCLEquivReal` — isomorphism
  `(Fin n → Fin d → K) ≃L[K] (Fin (n*d) → K)` via `Equiv.curry` + `finProdFinEquiv`
- `flattenCLEquiv_apply`, `_symm_apply`, `_im` — simp lemmas
- `forwardTube_flatten_eq_tubeDomain` — the forward tube IS a tube domain after
  flattening

*Main theorems:*
- `continuous_boundary_forwardTube` — holomorphic functions on the forward tube
  with distributional boundary values extend continuously to the real boundary
- `distributional_uniqueness_forwardTube` — two such functions with the same
  boundary values agree on the tube

Both derived from general tube domain axioms by flattening coordinates,
transporting DifferentiableOn through the isomorphism, bridging approach
direction conventions, change of variables in boundary integrals, and
pulling back ContinuousWithinAt through the homeomorphism.

**`TubeDistributions.lean`** — axioms (200 lines), encoding results from
Vladimirov (2002) §25-26:

1. `continuous_boundary_tube` — distributional BV ⟹ continuous boundary extension
2. `boundary_value_recovery` — continuous extension integrates to reproduce distributional BV
3. `distributional_uniqueness_tube` — same distributional BV ⟹ equal on tube (theorem, not axiom)
4. `polynomial_growth_tube` — tempered BV ⟹ polynomial growth estimates
5. `bochner_tube_theorem` — holomorphic on T(C) extends to T(conv C)

*Why axioms:* `continuous_boundary_tube` (#1) and `polynomial_growth_tube` (#4)
require the Fourier-Laplace representation of tube-domain holomorphic functions
(Vladimirov §25-26), which is not in Mathlib. `boundary_value_recovery` (#2) is
the second half of Vladimirov's theorem. `boundary_value_zero` (#3) combines
the du Bois-Reymond lemma with boundary value recovery. `bochner_tube_theorem` (#5)
is a deep SCV result (convex hull extension). `distributional_uniqueness_tube` is
proved (sorry-free) from `boundary_value_zero`, edge-of-the-wedge, and the identity
theorem.

---

## External Contributions (commits `9352c53`–`9e1e97f`)

### e-vergo (PR #5): 13 sorrys eliminated across vNA files

- `separating_iff_cyclic_commutant` (Basic.lean) — projection argument
- `strip_boundary` (KMS.lean) — frontier decomposition
- `complexMeasure_eq_inner` (SpectralStieltjes.lean) — polarization identity
- `map_mul`, `map_star`, `continuous_apply`, `fixed_point_Ω` (ModularAutomorphism.lean)
- 3 sorrys in ModularTheory.lean

### xiyin (commits `200ca66`, `9e1e97f`)

- Fixed `power_zero` bug with `IsStrictlyPositive` hypothesis
- Added 1,400+ lines to ComplexLieGroups:
  - Planar boost/spatial rotation lemmas (`LorentzLieGroup.lean`)
  - `complex_lorentz_invariance` theorem (`Connectedness.lean`)
  - SO⁺(1,d;ℂ) `isPathConnected` (`Complexification.lean`)
- **Replaced `edge_of_the_wedge` axiom with theorem** using SCV tube domain extension proof

---

## Axiom Explanation Notes

**Axioms #12-14** (added 2026-02-21) replaced sorrys in the R→E direction:

- **#12 `analytic_boundary_local_commutativity`**: The sorry in `W_analytic_local_commutativity`
  needed to pass from *distributional* local commutativity (W_n(f) = W_n(g) for test functions
  with spacelike-separated supports) to *pointwise* identity of the analytic continuation at
  real boundary points. This requires the Jost-Lehmann-Dyson representation / multi-tube
  edge-of-the-wedge theorem — deep SCV machinery not in Mathlib. The axiom states the
  precise pointwise conclusion (S-W Thm 3-5).

- **#13 `bhw_distributional_boundary_values`**: The sorry `h_in_tube` (showing x + iεη ∈
  ForwardTube when each η_k ∈ V₊) was **false as stated**. ForwardTube requires successive
  *differences* Im(z_k − z_{k-1}) ∈ V₊, but spectrum_condition provides each η_k ∈ V₊
  individually — having each η_k ∈ V₊ does not imply η_k − η_{k-1} ∈ V₊. The axiom
  sidesteps the coordinate convention mismatch by directly asserting the distributional
  boundary value property for the BHW extension (S-W Thm 2-11), which is the actual
  mathematical content needed.

- **#14 `wick_rotated_schwinger_tempered`**: The sorry in `constructedSchwinger_tempered`
  needed continuity of S_n(f) = ∫ F_ext(Wick(x)) f(x) dx in the Schwartz topology. This
  requires polynomial growth bounds on F_ext at Wick-rotated points across all n! permuted
  tubes. The existing `polynomial_growth_tube` axiom gives bounds per-tube, but combining
  them across permutations and verifying the integral is Schwartz-continuous requires
  substantial analytic estimates (OS I Prop 5.1).
