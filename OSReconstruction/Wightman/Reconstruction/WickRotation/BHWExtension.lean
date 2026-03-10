/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.ForwardTubeLorentz
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# BHW Extension

The Bargmann-Hall-Wightman extension of the analytic Wightman function
from the forward tube to the permuted extended tube, with Lorentz
invariance and permutation symmetry properties.
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]
/-! #### BHW extension (needed before constructing Schwinger functions) -/

private theorem continuous_minkowskiNormSq (d : ℕ) :
    Continuous (fun η : Fin (d + 1) → ℝ => MinkowskiSpace.minkowskiNormSq d η) := by
  simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
  apply continuous_finset_sum
  intro i _
  exact ((continuous_const.mul (continuous_apply i)).mul (continuous_apply i))

private theorem integral_swap_eq_self {d n : ℕ} [NeZero d]
    (i j : Fin n) (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun k => x (Equiv.swap i j k)) =
    ∫ x : NPointDomain d n, h x := by
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  let e : NPointDomain d n ≃ᵐ NPointDomain d n :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Fin (d + 1) → ℝ) σ
  have hmp : MeasureTheory.MeasurePreserving (⇑e) MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin n => Fin (d + 1) → ℝ) σ
  have hEq : ∫ x : NPointDomain d n, h (e x) = ∫ x : NPointDomain d n, h x := hmp.integral_comp' h
  rw [MeasurableEquiv.coe_piCongrLeft] at hEq
  calc
    ∫ x : NPointDomain d n, h (fun k => x (Equiv.swap i j k))
        = ∫ x : NPointDomain d n,
            h ((Equiv.piCongrLeft (fun _ : Fin n => Fin (d + 1) → ℝ) σ) x) := by
            congr 1
            ext x
            congr 1
            ext k μ
            simpa [σ] using (congrArg (fun u => u μ)
              (Equiv.piCongrLeft_apply
                (P := fun _ : Fin n => Fin (d + 1) → ℝ)
                (e := σ) x k)).symm
    _ = ∫ x : NPointDomain d n, h x := hEq

/-- W_analytic inherits real Lorentz invariance from the Wightman distribution.

    Both z ↦ W_analytic(z) and z ↦ W_analytic(Λz) are holomorphic on the forward tube
    with the same distributional boundary values (by Lorentz invariance of W_n).
    By `distributional_uniqueness_forwardTube`, they agree on the forward tube.

    Ref: Streater-Wightman, §2.4 -/
theorem W_analytic_lorentz_on_tube (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ (Λ : LorentzGroup.Restricted (d := d))
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      (Wfn.spectrum_condition n).choose
        (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
      (Wfn.spectrum_condition n).choose z := by
  intro Λ z hz
  -- Apply distributional uniqueness: two holomorphic functions on the forward tube
  -- with the same distributional boundary values must agree.
  have huniq := distributional_uniqueness_forwardTube
    (W_analytic_lorentz_holomorphic Wfn n Λ)
    (Wfn.spectrum_condition n).choose_spec.1
    (fun f η ε hε hη => by
      have hInt₁ : MeasureTheory.Integrable
          (fun x : NPointDomain d n =>
            (Wfn.spectrum_condition n).choose
              (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) *
                (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * f x) := by
        exact forward_tube_bv_integrable
          (fun z => (Wfn.spectrum_condition n).choose
            (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν))
          (W_analytic_lorentz_holomorphic Wfn n Λ)
          ⟨Wfn.W n, Wfn.tempered n, fun f' η' hη' =>
            lorentz_covariant_distributional_bv (d := d) (n := n)
              Wfn (Wfn.spectrum_condition n).choose
              (Wfn.spectrum_condition n).choose_spec.1
              (Wfn.spectrum_condition n).choose_spec.2
              Λ f' η' hη'⟩
          f η hη ε hε
      have hInt₂ : MeasureTheory.Integrable
          (fun x : NPointDomain d n =>
            (Wfn.spectrum_condition n).choose
              (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x) := by
        exact forward_tube_bv_integrable
          (Wfn.spectrum_condition n).choose
          (Wfn.spectrum_condition n).choose_spec.1
          ⟨Wfn.W n, Wfn.tempered n, (Wfn.spectrum_condition n).choose_spec.2⟩
          f η hη ε hε
      simpa [sub_mul] using hInt₁.sub hInt₂)
    (W_analytic_lorentz_bv_agree Wfn n Λ)
  exact huniq z hz

/-- W_analytic extends continuously to the real boundary of the forward tube.

    BLOCKED: Previously depended on `continuous_boundary_forwardTube` which was
    overstrong as stated (conclusion referenced F at boundary points unconstrained
    by hypotheses). Will be unblocked by either:
    (a) Distributional EOW infrastructure (codex building) → direct proof
    (b) Constructing `HasFourierLaplaceReprRegular` from Wightman axioms →
        use `_of_flatRegular` variant

    Ref: Streater-Wightman, Theorem 2-9 -/
theorem W_analytic_continuous_boundary (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt (Wfn.spectrum_condition n).choose
        (ForwardTube d n) (fun k μ => (x k μ : ℂ)) := by
  sorry

/-- Distributional swap-agreement on boundary values in test-function form.

    Fix adjacent indices `i, i+1`. If `g` is obtained from `f` by swapping those
    coordinates and `f` is supported on configurations where the swapped pair is
    spacelike separated, then local commutativity gives `W n g = W n f`.

    Combining this with the boundary-value convergence for `f` and `g` along the
    same forward direction `η`, the smeared boundary-value difference converges to 0:
    `∫ W_analytic(x+iεη) * (g-f) → 0`. -/
theorem W_analytic_swap_distributional_agree {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
    (hW_cont : Continuous (W n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hLC : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ x : NPointDomain d n, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x - f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  intro f g η hsep hswap hη
  have h_g : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W n g)) := hBV g η hη
  have h_f : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W n f)) := hBV f η hη
  have h_diff : Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) -
        (∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W n g - W n f)) := Filter.Tendsto.sub h_g h_f
  have hW_eq : W n g = W n f := (hLC n i ⟨i.val + 1, hi⟩ f g hsep hswap).symm
  have h_diff_zero : Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) -
        (∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    simpa [hW_eq] using h_diff
  refine h_diff_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← MeasureTheory.integral_sub]
  · congr 1
    ext x
    ring
  · exact forward_tube_bv_integrable
      W_analytic hW_hol ⟨W n, hW_cont, hBV⟩ g η hη ε (Set.mem_Ioi.mp hε)
  · exact forward_tube_bv_integrable
      W_analytic hW_hol ⟨W n, hW_cont, hBV⟩ f η hη ε (Set.mem_Ioi.mp hε)

/-- Boundary-pairing form of local commutativity for adjacent swaps.

    For test functions `f, g` related by adjacent swap on a spacelike support
    region, the real-boundary pairings of `W_analytic` coincide:
    `∫ W_analytic(x) g(x) dx = ∫ W_analytic(x) f(x) dx`.

    BLOCKED: Previously depended on `boundary_value_recovery_forwardTube` (overstrong,
    deleted). Will be unblocked by distributional EOW infrastructure or by constructing
    `HasFourierLaplaceReprRegular` → use `boundary_value_recovery_forwardTube_of_flatRegular`. -/
theorem W_analytic_swap_boundary_pairing_eq {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
    (hW_cont : Continuous (W n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hLC : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      (∫ x : NPointDomain d n,
        W_analytic (fun k μ => (x k μ : ℂ)) * (g x)) =
      (∫ x : NPointDomain d n,
        W_analytic (fun k μ => (x k μ : ℂ)) * (f x)) := by
  sorry

/-- Pointwise local commutativity of the analytic continuation at spacelike boundary.

    Proof strategy (preserved from previous version):
    1. Construct bump function χ supported on spacelike region
    2. Use `W_analytic_swap_boundary_pairing_eq` to show swap-invariance of boundary pairings
    3. Localize via χ and `eq_zero_of_schwartz_integral_zero` to get pointwise equality

    BLOCKED: Depends on `W_analytic_swap_boundary_pairing_eq` (blocked on boundary value
    recovery) and `boundary_function_continuous_forwardTube` (overstrong, deleted).
    Will be unblocked by distributional EOW infrastructure.

    Ref: Streater-Wightman Thm 3-5; Jost §IV.3 -/
theorem analytic_boundary_local_commutativity {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
    (hW_cont : Continuous (W n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hLC : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hx : MinkowskiSpace.minkowskiNormSq d
      (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0) :
    W_analytic (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
    W_analytic (fun k μ => (x k μ : ℂ)) := by
  sorry

/-- Local commutativity of W_analytic at spacelike-separated boundary points.

    At real points where consecutive arguments are spacelike separated
    (Minkowski norm > 0), swapping those arguments doesn't change the boundary
    value. This follows from `analytic_boundary_local_commutativity` applied to
    the analytic continuation from `spectrum_condition`.

    Ref: Streater-Wightman, §3.3; Jost, §IV.3 -/
theorem W_analytic_local_commutativity (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        MinkowskiSpace.minkowskiNormSq d
          (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0 →
        (Wfn.spectrum_condition n).choose
          (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        (Wfn.spectrum_condition n).choose (fun k μ => (x k μ : ℂ)) := by
  intro i hi x hx
  exact analytic_boundary_local_commutativity (d := d) (n := n)
    (Wfn.spectrum_condition n).choose
    (Wfn.spectrum_condition n).choose_spec.1
    Wfn.W
    (Wfn.tempered n)
    (Wfn.spectrum_condition n).choose_spec.2
    Wfn.locally_commutative
    i hi x hx

/-- The BHW extension of W_analytic from the forward tube to the permuted extended tube.

    Proved by applying the `bargmann_hall_wightman` axiom (AnalyticContinuation.lean) to
    the holomorphic extension `W_analytic` from `spectrum_condition`, with:
    - Lorentz invariance from `W_analytic_lorentz_on_tube`
    - Continuous boundary values from `W_analytic_continuous_boundary`
    - Local commutativity from `W_analytic_local_commutativity`

    Ref: Streater-Wightman, Theorem 2-11; Jost, Ch. IV -/
noncomputable def W_analytic_BHW (Wfn : WightmanFunctions d) (n : ℕ) :
    { F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ //
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n,
        F_ext z = (Wfn.spectrum_condition n).choose z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k μ => ∑ ν, Λ.val μ ν * z k ν) = F_ext z) ∧
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) } := by
  let h := bargmann_hall_wightman n
      (Wfn.spectrum_condition n).choose
      (Wfn.spectrum_condition n).choose_spec.1
      (W_analytic_lorentz_on_tube Wfn n)
      (W_analytic_continuous_boundary Wfn n)
      (W_analytic_local_commutativity Wfn n)
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1,
    h.choose_spec.2.2.2.1⟩

/-- Uniqueness of the BHW extension chosen in `W_analytic_BHW`.

    This restates the uniqueness clause of `bargmann_hall_wightman` for the
    specific extension packaged by `W_analytic_BHW`. It is the concrete
    uniqueness fact needed when comparing `W_analytic_BHW` to other holomorphic
    functions on the permuted extended tube with the same forward-tube boundary
    data. -/
theorem W_analytic_BHW_unique (Wfn : WightmanFunctions d) (n : ℕ)
    (G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hG_holo : DifferentiableOn ℂ G (PermutedExtendedTube d n))
    (hG_eq : ∀ z ∈ ForwardTube d n, G z = (Wfn.spectrum_condition n).choose z) :
    ∀ z ∈ PermutedExtendedTube d n, G z = (W_analytic_BHW Wfn n).val z := by
  let h := bargmann_hall_wightman n
      (Wfn.spectrum_condition n).choose
      (Wfn.spectrum_condition n).choose_spec.1
      (W_analytic_lorentz_on_tube Wfn n)
      (W_analytic_continuous_boundary Wfn n)
      (W_analytic_local_commutativity Wfn n)
  have hchosen : (W_analytic_BHW Wfn n).val = h.choose := by
    rfl
  intro z hz
  rw [hchosen]
  exact h.choose_spec.2.2.2.2 G hG_holo hG_eq z hz


end
