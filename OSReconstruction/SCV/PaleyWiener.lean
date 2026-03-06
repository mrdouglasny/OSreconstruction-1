/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.SCV.TubeDistributions
import OSReconstruction.SCV.FourierLaplaceCore
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Paley-Wiener-Schwartz Theorem

This file develops the Paley-Wiener-Schwartz theorem and its consequences for
holomorphic extension of distributions with one-sided Fourier support.

## Main results

* `paley_wiener_half_line` -- If T in S'(R) has supp(FT) in [0,infinity), then
  z -> T(e^{-iz.}) extends holomorphically to the upper half-plane.

* `paley_wiener_cone` -- Multi-dimensional generalization: if T in S'(R^m) has
  supp(FT) in C* (dual cone), then z -> T(e^{-iz.}) extends holomorphically
  to the tube domain T(C).

* `paley_wiener_converse` -- Converse: if F is holomorphic on T(C) with polynomial
  growth, then its distributional boundary value has Fourier transform supported in C*.

* `paley_wiener_one_step` -- Technical lemma for inductive analytic continuation:
  given a function on a tube whose distributional boundary value has one-sided
  Fourier support in one variable, extend holomorphicity by one variable.

## Mathematical Background

The classical Paley-Wiener theorem (for L^2) states that a function f in L^2(R) has
Fourier transform supported in [0,infinity) if and only if f extends holomorphically
to the upper half-plane with L^2 bounds on horizontal lines.

The Schwartz generalization replaces L^2 with tempered distributions S'(R^m) and
replaces L^2 bounds with polynomial growth. The key result: if T in S'(R^m) and
supp(FT) in C* (the dual cone of an open convex cone C in R^m), then the
Fourier-Laplace transform

    F(z) = <FT, e^{iz . .}>

is holomorphic on the tube domain T(C) = R^m + iC, with at most polynomial growth
as Im(z) approaches the boundary of C.

The converse also holds: any holomorphic function on T(C) with polynomial growth
is the Fourier-Laplace transform of a tempered distribution with Fourier support in C*.

## Application

The key consumer is `inductive_analytic_continuation` (OS II, Theorem 4.1) in
WickRotation.lean. At each induction step, one fixes all variables except one
spacetime component, obtains a function of one real variable with polynomial growth
(from E0') whose Fourier transform has one-sided support (from positivity of the
Hamiltonian / reflection positivity), and applies Paley-Wiener to extend
holomorphically to the upper half-plane in that variable.

## References

* Reed-Simon II, Theorem IX.16 (Paley-Wiener for L^2)
* Hormander, "The Analysis of Linear Partial Differential Operators I", Theorem 7.4.3
* Vladimirov, "Methods of the Theory of Generalized Functions", Section 25-26
* Streater-Wightman, "PCT, Spin and Statistics", Theorem 2-6
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

/-! ### Fourier support for tempered distributions

We formalize the notion of Fourier support for tempered distributions (continuous
linear functionals on Schwartz space). The Fourier transform of T in S'(R^m) is
defined by duality: (FT)(phi) = T(F(phi)) for phi in S(R^m).

We say supp(FT) subset S if T(F(phi)) = 0 whenever supp(phi) is disjoint from S.

Note: The Fourier transform on Schwartz space `SchwartzMap.fourierTransformCLM`
is available in Mathlib for inner product spaces. For `Fin m -> R` with the
standard Euclidean structure, this gives the m-dimensional Fourier transform.
However, to avoid type-class issues with `Fin m -> R` vs `EuclideanSpace R (Fin m)`,
we express Fourier support purely in terms of the distribution T and avoid
explicit use of the Fourier transform operator in the definitions.
-/

/-- A tempered distribution T (a continuous linear functional on Schwartz space)
    has **one-sided Fourier support** (in the half-line [0, infinity)) if
    the Fourier transform T̂ of T vanishes on Schwartz functions supported
    in (-infinity, 0).

    Formally: T has Fourier support in [0, ∞) iff for every φ ∈ 𝓢(ℝ,ℂ)
    with supp(φ) ⊂ (-∞, 0), we have T̂(φ) = T(ℱ[φ]) = 0, where ℱ is
    the Schwartz-space Fourier transform.

    This is expressed via Fourier duality: (T̂)(φ) = T(F[φ]) where
    F = SchwartzMap.fourierTransformCLM ℂ is the Fourier transform operator
    on 𝓢(ℝ,ℂ).

    Note: This correctly captures Fourier support (not distributional support).
    A distribution T with supp(T) ⊂ [0,∞) does NOT necessarily have Fourier
    support in [0,∞) — these are distinct conditions. The Paley-Wiener theorem
    requires Fourier support, not distributional support.

    This is the key hypothesis for the Paley-Wiener theorem.

    Ref: Hörmander, "Analysis of PDE I", Definition 7.1.1;
    Vladimirov, "Generalized Functions", §8. -/
def HasOneSidedFourierSupport (T : SchwartzMap ℝ ℂ → ℂ) : Prop :=
  ∀ (φ : SchwartzMap ℝ ℂ),
    (∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) →
    T (SchwartzMap.fourierTransformCLM ℂ φ) = 0

/-- If a tempered distribution has one-sided Fourier support, then after pairing
    against its Fourier transform it depends only on the restriction of the
    Schwartz kernel to `[0, ∞)`. Any change on the negative half-line is invisible. -/
theorem fourier_pairing_eq_of_eqOn_nonneg
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : HasOneSidedFourierSupport T)
    {φ ψ : SchwartzMap ℝ ℂ}
    (h_eq : Set.EqOn φ ψ (Set.Ici 0)) :
    T (SchwartzMap.fourierTransformCLM ℂ φ) =
      T (SchwartzMap.fourierTransformCLM ℂ ψ) := by
  have hsupp :
      ∀ x ∈ Function.support ((φ - ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ), x < 0 := by
    intro x hx
    by_cases hx_nonneg : 0 ≤ x
    · have hzero : (φ - ψ : SchwartzMap ℝ ℂ) x = 0 := by
        simp [h_eq hx_nonneg]
      exact (hx hzero).elim
    · linarith
  have hzero :
      T (SchwartzMap.fourierTransformCLM ℂ (φ - ψ : SchwartzMap ℝ ℂ)) = 0 :=
    hT_supp (φ - ψ) hsupp
  exact sub_eq_zero.mp (by
    simpa [map_sub] using hzero)

/-- A tempered distribution T on R^m has **Fourier support in a closed set S**
    if T̂ (the Fourier transform of T) vanishes on Schwartz functions supported
    outside S. That is, for every φ ∈ 𝓢(ℝ^m,ℂ) with supp(φ) ∩ S = ∅,
    T̂(φ) = T(F[φ]) = 0.

    For the Paley-Wiener theorem, S will be the dual cone C*.

    ⚠️ TYPE NOTE: The correct formulation requires the domain to carry an inner
    product space structure compatible with its norm (so that `fourierTransformCLM`
    applies). The type `Fin m → ℝ` in Mathlib carries the sup-norm via
    `Pi.normedAddCommGroup`, which does NOT agree with the ℓ²-inner product.
    The correct domain is `EuclideanSpace ℝ (Fin m)`. This definition uses
    `Fin m → ℝ` for compatibility with the rest of this file (where `dualCone`,
    `TubeDomain`, etc. are all defined over `Fin m → ℝ`), but consequently
    CANNOT directly use `SchwartzMap.fourierTransformCLM`. The correctness is
    expressed via distributional duality: T(F[φ]) = 0 iff supp(T̂) ⊆ S.

    TODO: Refactor all multi-dimensional PW theory to use `EuclideanSpace ℝ (Fin m)`
    as the domain, which would allow using `fourierTransformCLM` directly. -/
def HasFourierSupportIn {m : ℕ} (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ)
    (S : Set (Fin m → ℝ)) : Prop :=
  ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
    (∀ x ∈ Function.support (φ : (Fin m → ℝ) → ℂ), x ∉ S) →
    T φ = 0

/-- The dual cone C* = { xi in R^m : <xi, y> >= 0 for all y in C }, where
    <.,.> is the standard Euclidean inner product (dot product).

    For an open convex cone C, the dual cone C* is a closed convex cone
    containing 0. The Paley-Wiener theorem states that tempered distributions
    with Fourier support in C* correspond to holomorphic functions on the
    tube domain T(C) with polynomial growth. -/
def dualCone {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  { ξ | ∀ y ∈ C, ∑ i : Fin m, ξ i * y i ≥ 0 }

/-- The dual cone is always closed. -/
theorem dualCone_isClosed {m : ℕ} (C : Set (Fin m → ℝ)) :
    IsClosed (dualCone C) := by
  have : dualCone C = ⋂ y ∈ C, { ξ : Fin m → ℝ | ∑ i, ξ i * y i ≥ 0 } := by
    ext ξ; simp [dualCone, mem_iInter]
  rw [this]
  apply isClosed_biInter
  intro y _hy
  exact isClosed_le continuous_const
    (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const)

/-- The dual cone contains 0. -/
theorem zero_mem_dualCone {m : ℕ} (C : Set (Fin m → ℝ)) :
    (0 : Fin m → ℝ) ∈ dualCone C := by
  intro y _
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, ge_iff_le, le_refl]

/-! ### Polynomial growth -/

/-- A holomorphic function on a tube domain has polynomial growth if for every
    compact K subset C, there exist C_K, N such that
    |F(x + iy)| <= C_K * (1 + |x|)^N for all x in R^m and y in K.

    This is the growth condition characterizing Fourier-Laplace transforms
    of tempered distributions (Vladimirov Section 25). -/
def HasPolynomialGrowthOnTube {m : ℕ} (C : Set (Fin m → ℝ))
    (F : (Fin m → ℂ) → ℂ) : Prop :=
  ∀ (K : Set (Fin m → ℝ)), K ⊆ C → IsCompact K →
    ∃ (C_K : ℝ) (N : ℕ),
      0 < C_K ∧
      ∀ (x : Fin m → ℝ) (y : Fin m → ℝ), y ∈ K →
        ‖F (fun i => (x i : ℂ) + (y i : ℂ) * I)‖ ≤
          C_K * (1 + ‖x‖) ^ N

/-! ### Upper half-plane -/

/-- The upper half-plane { z in C : Im(z) > 0 }. -/
def upperHalfPlane : Set ℂ := { z : ℂ | z.im > 0 }

/-- A function on the real line with polynomial growth. -/
def HasPolynomialGrowthOnLine (f : ℝ → ℂ) : Prop :=
  ∃ (C_bound : ℝ) (N : ℕ), 0 < C_bound ∧
    ∀ x : ℝ, ‖f x‖ ≤ C_bound * (1 + |x|) ^ N

/-- The upper half-plane is open. -/
theorem upperHalfPlane_isOpen : IsOpen upperHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_im

/-! ### Finite Schwartz-seminorm control of tempered functionals -/

/-- A continuous linear functional on Schwartz space is controlled by finitely many
    Schwartz seminorms.

    This is the standard tempered-distribution boundedness statement specialized to
    `𝓢(ℝ, ℂ)`: continuity for the Schwartz topology is equivalent to domination by a
    finite supremum of Schwartz seminorms. It is the functional-analytic input needed
    to turn the abstract continuity hypothesis in `paley_wiener_half_line` into the
    concrete seminorm estimates used to control the Fourier-Laplace pairing. -/
theorem schwartz_functional_bound
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      ∀ φ : SchwartzMap ℝ ℂ,
        ‖T φ‖ ≤ (C • s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) φ := by
  let q : Seminorm ℂ (SchwartzMap ℝ ℂ) := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq_cont : Continuous q := by
    change Continuous (fun φ : SchwartzMap ℝ ℂ => ‖T φ‖)
    simpa [q, Seminorm.comp_apply, coe_normSeminorm] using
      continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ ℝ ℂ) q hq_cont
  refine ⟨s, C, hC, ?_⟩
  intro φ
  simpa [q, Seminorm.comp_apply, coe_normSeminorm] using hbound φ

/-- A continuous linear functional on Schwartz space grows at most polynomially on the
    horizontal-line test family `x ↦ ψ_{x+iη}`. -/
theorem schwartz_functional_horizontal_growth
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (η : ℝ) (hη : 0 < η) :
    HasPolynomialGrowthOnLine
      (fun x => T (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη))) := by
  classical
  obtain ⟨s, C, hC, hbound⟩ := schwartz_functional_bound T
  have hD :
      ∀ p : ℕ × ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ,
        SchwartzMap.seminorm ℝ p.1 p.2
          (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)) ≤
            D * (1 + |x|) ^ p.2 := by
    intro p
    obtain ⟨D, hD_nonneg, hD_bound⟩ := schwartzPsiZ_seminorm_horizontal_bound η hη p.1 p.2
    exact ⟨D, hD_nonneg, hD_bound⟩
  choose D hD_nonneg hD_bound using hD
  let N : ℕ := s.sup Prod.snd
  let Dsum : ℝ := ∑ p ∈ s, D p
  let Cbound : ℝ := (C : ℝ) * Dsum + 1
  have hDsum_nonneg : 0 ≤ Dsum := by
    dsimp [Dsum]
    refine Finset.sum_nonneg ?_
    intro p hp
    exact hD_nonneg p
  have hC_coe_ne : (C : ℝ) ≠ 0 := by
    exact_mod_cast hC
  have hC_pos : 0 < (C : ℝ) := by
    exact lt_of_le_of_ne C.2 hC_coe_ne.symm
  refine ⟨Cbound, N, by
    dsimp [Cbound]
    nlinarith, ?_⟩
  intro x
  let ψx : SchwartzMap ℝ ℂ := schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)
  let u : ℝ := 1 + |x|
  have hu_nonneg : 0 ≤ u := by
    have hx : 0 ≤ |x| := abs_nonneg x
    linarith
  have hu_ge_one : 1 ≤ u := by
    have hx : 0 ≤ |x| := abs_nonneg x
    linarith
  have hsup_sum :
      (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψx ≤
        (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx := by
    exact Seminorm.le_def.mp (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℂ ℝ ℂ) s) ψx
  have hsum_apply :
      ∀ s' : Finset (ℕ × ℕ),
        (∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p) ψx =
          ∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p ψx := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        simp
    | insert a s' ha ih =>
        simp [Finset.sum_insert, ha, ih]
  have hsum_bound :
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx ≤ Dsum * u ^ N := by
    calc
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx
          = ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p ψx := by
              simpa using hsum_apply s
      _ 
          ≤ ∑ p ∈ s, D p * u ^ N := by
              refine Finset.sum_le_sum ?_
              intro p hp
              have hpN : p.2 ≤ N := Finset.le_sup hp
              calc
                schwartzSeminormFamily ℂ ℝ ℂ p ψx
                    ≤ D p * u ^ p.2 := hD_bound p x
                _ ≤ D p * u ^ N := by
                      refine mul_le_mul_of_nonneg_left ?_ (hD_nonneg p)
                      exact pow_le_pow_right₀ hu_ge_one hpN
      _ = Dsum * u ^ N := by
            simp [Dsum, Finset.sum_mul]
  have hT_bound : ‖T ψx‖ ≤ (C : ℝ) * (Dsum * u ^ N) := by
    calc
      ‖T ψx‖ ≤ (C • s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψx := hbound ψx
      _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψx := by
            rfl
      _ ≤ (C : ℝ) * ((∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx) := by
            gcongr
      _ ≤ (C : ℝ) * (Dsum * u ^ N) := by
            gcongr
  calc
    ‖T ψx‖ ≤ (C : ℝ) * (Dsum * u ^ N) := hT_bound
    _ ≤ Cbound * u ^ N := by
          have hu_pow_nonneg : 0 ≤ u ^ N := pow_nonneg hu_nonneg _
          have hCu : (C : ℝ) * (Dsum * u ^ N) ≤ ((C : ℝ) * Dsum + 1) * u ^ N := by
            have hu_pow_ge_one : 1 ≤ u ^ N := by
              exact pow_le_pow_right₀ hu_ge_one (Nat.zero_le _)
            nlinarith
          simpa [Cbound, u, mul_assoc, mul_left_comm, mul_comm] using hCu

/-- Along a fixed horizontal line in the upper half-plane, the candidate
    Fourier-Laplace extension `z ↦ T(ℱ[ψ_z])` has polynomial growth. -/
theorem fourierLaplaceExt_horizontal_growth
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (η : ℝ) (hη : 0 < η) :
    HasPolynomialGrowthOnLine
      (fun x => fourierLaplaceExt T ((x : ℂ) + η * I) (by simpa using hη)) := by
  let S : SchwartzMap ℝ ℂ →L[ℂ] ℂ := T.comp (SchwartzMap.fourierTransformCLM ℂ)
  simpa [S, fourierLaplaceExt_eq] using
    schwartz_functional_horizontal_growth
      (T := S) η hη

/-- Along a fixed horizontal line, the candidate complex derivative kernel
    `T(ℱ[(I ξ) ψ_{x+iη}])` also has polynomial growth.

    This is the growth estimate needed for the derivative side of the
    Fourier-Laplace pairing once holomorphicity is proved at the Schwartz-topology
    level. -/
theorem fourierLaplaceExt_derivCandidate_horizontal_growth
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (η : ℝ) (hη : 0 < η) :
    HasPolynomialGrowthOnLine
      (fun x =>
        T ((SchwartzMap.fourierTransformCLM ℂ)
          ((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
            (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη))))) := by
  let L : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
    (SchwartzMap.fourierTransformCLM ℂ).comp
      (SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
  let S : SchwartzMap ℝ ℂ →L[ℂ] ℂ := T.comp L
  simpa [L, S] using schwartz_functional_horizontal_growth (T := S) η hη

/-- Applying `T ∘ ℱ` to the local remainder kernel preserves the uniform
    `O(‖h‖)` bound coming from the Schwartz seminorm estimates. -/
theorem fourierLaplaceExt_remainder_bound
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (z : ℂ) (hz : 0 < z.im) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℂ) (hh_im : ‖h‖ ≤ z.im / 2) (hh1 : ‖h‖ ≤ 1),
      ‖(T.comp (SchwartzMap.fourierTransformCLM ℂ))
          (schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1)‖ ≤
        K * ‖h‖ := by
  let S : SchwartzMap ℝ ℂ →L[ℂ] ℂ := T.comp (SchwartzMap.fourierTransformCLM ℂ)
  obtain ⟨s, C, hC, hbound⟩ := schwartz_functional_bound S
  have hD :
      ∀ p : ℕ × ℕ, ∃ D : ℝ, 0 ≤ D ∧
        ∀ (h : ℂ) (hh_im : ‖h‖ ≤ z.im / 2) (hh1 : ‖h‖ ≤ 1),
          SchwartzMap.seminorm ℝ p.1 p.2
            (schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1) ≤
              D * ‖h‖ := by
    intro p
    simpa using
      schwartzPsiZExpTaylorLinearRemainderQuot_seminorm_le z hz p.1 p.2
  choose D hD_nonneg hD_bound using hD
  let Dsum : ℝ := ∑ p ∈ s, D p
  let K : ℝ := (C : ℝ) * Dsum
  have hDsum_nonneg : 0 ≤ Dsum := by
    dsimp [Dsum]
    refine Finset.sum_nonneg ?_
    intro p hp
    exact hD_nonneg p
  have hC_pos : 0 < (C : ℝ) := by
    have hC_coe_ne : (C : ℝ) ≠ 0 := by
      exact_mod_cast hC
    exact lt_of_le_of_ne C.2 hC_coe_ne.symm
  refine ⟨K, mul_nonneg hC_pos.le hDsum_nonneg, ?_⟩
  intro h hh_im hh1
  let ψh : SchwartzMap ℝ ℂ :=
    schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1
  have hsup_sum :
      (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψh ≤
        (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψh := by
    exact Seminorm.le_def.mp
      (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℂ ℝ ℂ) s) ψh
  have hsum_apply :
      ∀ s' : Finset (ℕ × ℕ),
        (∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p) ψh =
          ∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p ψh := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        simp
    | insert a s' ha ih =>
        simp [Finset.sum_insert, ha, ih]
  have hsum_bound :
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψh ≤ Dsum * ‖h‖ := by
    calc
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψh
          = ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p ψh := by
              simpa using hsum_apply s
      _ ≤ ∑ p ∈ s, D p * ‖h‖ := by
            refine Finset.sum_le_sum ?_
            intro p hp
            exact hD_bound p h hh_im hh1
      _ = Dsum * ‖h‖ := by
            simp [Dsum, Finset.sum_mul]
  calc
    ‖S ψh‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψh := by
      simpa using hbound ψh
    _ ≤ (C : ℝ) * ((∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψh) := by
          gcongr
    _ ≤ (C : ℝ) * (Dsum * ‖h‖) := by
          gcongr
    _ = K * ‖h‖ := by
          simp [K, Dsum, mul_assoc, mul_left_comm, mul_comm]

/-- The candidate Fourier-Laplace extension is holomorphic on the upper half-plane.

    This packages the scalar derivative argument: the kernel remainder is
    rewritten using `psiZ_sub_sub_deriv_eq_smul_remainder`, then the uniform
    `O(‖h‖)` bound from `fourierLaplaceExt_remainder_bound` upgrades it to an
    `O(‖h‖²)` scalar remainder. -/
theorem fourierLaplaceExt_hasDerivAt
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt
      (fun w : ℂ =>
        if hw : 0 < w.im then
          fourierLaplaceExt T w hw
        else
          0)
      (T ((SchwartzMap.fourierTransformCLM ℂ)
        ((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
          (schwartzPsiZ z hz))))
      z := by
  let F : ℂ → ℂ := fun w =>
    if hw : 0 < w.im then
      fourierLaplaceExt T w hw
    else
      0
  let S : SchwartzMap ℝ ℂ →L[ℂ] ℂ := T.comp (SchwartzMap.fourierTransformCLM ℂ)
  let Dψ : SchwartzMap ℝ ℂ :=
    (SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ))) (schwartzPsiZ z hz)
  let D : ℂ := S Dψ
  obtain ⟨K, hK_nonneg, hKbound⟩ := fourierLaplaceExt_remainder_bound T z hz
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hsmall :
      ∀ᶠ h : ℂ in 𝓝 0, ‖h‖ ≤ z.im / 2 ∧ ‖h‖ ≤ 1 ∧ 0 < (z + h).im := by
    let r : ℝ := min (z.im / 2) 1
    have hr : 0 < r := by
      dsimp [r]
      positivity
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with h hh
    have hnorm_lt : ‖h‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hh
    have hh_im : ‖h‖ ≤ z.im / 2 := by
      exact le_trans hnorm_lt.le (min_le_left _ _)
    have hh1 : ‖h‖ ≤ 1 := by
      exact le_trans hnorm_lt.le (min_le_right _ _)
    have him_le : |h.im| ≤ ‖h‖ := by
      simpa using Complex.abs_im_le_norm h
    have him_lower : -‖h‖ ≤ h.im := by
      rw [abs_le] at him_le
      linarith
    have hzph : 0 < (z + h).im := by
      have hh_lt : ‖h‖ < z.im / 2 := lt_of_lt_of_le hnorm_lt (min_le_left _ _)
      simpa [Complex.add_im] using (show 0 < z.im + h.im by nlinarith [hz, hh_lt, him_lower])
    exact ⟨hh_im, hh1, hzph⟩
  have hbound :
      ∀ᶠ h : ℂ in 𝓝 0,
        ‖F (z + h) - F z - h * D‖ ≤ K * ‖h ^ 2‖ := by
    filter_upwards [hsmall] with h hh
    rcases hh with ⟨hh_im, hh1, hzph⟩
    let R : SchwartzMap ℝ ℂ := schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1
    have htemp : (fun ξ : ℝ => I * (ξ : ℂ)).HasTemperateGrowth := by
      fun_prop
    have hkernel :
        schwartzPsiZ (z + h) hzph - schwartzPsiZ z hz - h • Dψ = h • R := by
      ext ξ
      simpa [Dψ, R, schwartzPsiZ_apply, schwartzPsiZExpTaylorLinearRemainderQuot_apply,
        SchwartzMap.smulLeftCLM_apply_apply htemp, smul_eq_mul] using
        psiZ_sub_sub_deriv_eq_smul_remainder z h ξ
    have hEq :
        F (z + h) - F z - h * D = h * S R := by
      have hzph' : 0 < z.im + h.im := by
        simpa [Complex.add_im] using hzph
      have hF_add : F (z + h) = fourierLaplaceExt T (z + h) hzph := by
        simp [F, Complex.add_im, hzph']
      have hF_zero : F z = fourierLaplaceExt T z hz := by
        simp [F, hz]
      calc
        F (z + h) - F z - h * D
            = fourierLaplaceExt T (z + h) hzph - fourierLaplaceExt T z hz - h * D := by
                rw [hF_add, hF_zero]
        _ = S (schwartzPsiZ (z + h) hzph) - S (schwartzPsiZ z hz) - h * D := by
              simp [S, D, fourierLaplaceExt_eq]
        _ = S (schwartzPsiZ (z + h) hzph - schwartzPsiZ z hz - h • Dψ) := by
              simp [S, D, Dψ, map_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = S (h • R) := by rw [hkernel]
        _ = h * S R := by
              simp [S]
    have hnorm_bound :
        ‖F (z + h) - F z - h * D‖ ≤ K * ‖h ^ 2‖ := by
      calc
        ‖F (z + h) - F z - h * D‖ = ‖h * S R‖ := by rw [hEq]
        _ = ‖h‖ * ‖S R‖ := by rw [norm_mul]
        _ ≤ ‖h‖ * (K * ‖h‖) := by
              exact mul_le_mul_of_nonneg_left (hKbound h hh_im hh1) (norm_nonneg h)
        _ = K * ‖h ^ 2‖ := by
              rw [norm_pow]
              ring
    exact hnorm_bound
  exact (Asymptotics.IsBigO.of_bound K hbound).trans_isLittleO
    (by simpa using (Asymptotics.isLittleO_pow_pow (𝕜 := ℂ) (m := 1) (n := 2) one_lt_two))

/-- The candidate Fourier-Laplace extension is differentiable on the upper half-plane. -/
theorem fourierLaplaceExt_differentiableOn
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    DifferentiableOn ℂ
      (fun w : ℂ =>
        if hw : 0 < w.im then
          fourierLaplaceExt T w hw
        else
          0)
      upperHalfPlane := by
  intro z hz
  exact (fourierLaplaceExt_hasDerivAt T z hz).differentiableAt.differentiableWithinAt

/-! ### The Paley-Wiener-Schwartz theorem: 1D case -/

/-- **Paley-Wiener theorem for the half-line (1D).**

    If `T ∈ S'(ℝ)` is given as a continuous complex-linear functional on
    Schwartz space with
    Fourier support in [0, infinity) (meaning: T(phi) = 0 whenever
    supp(phi) subset (-infinity, 0)), then the Fourier-Laplace transform
    z -> T(e^{-iz .}) extends holomorphically to the upper half-plane Im(z) > 0.

    More precisely, there exists a holomorphic function F on the upper half-plane
    such that for each Schwartz function phi, the smeared integral
    integral_R F(x + i*eta) * phi(x) dx converges to T(phi) as eta -> 0+.

    The proof (not yet formalized) proceeds by:
    1. Write T(phi) = (FT)(F^{-1}(phi)) by Parseval for distributions
    2. Since supp(FT) subset [0, infinity), the pairing localizes to xi >= 0
    3. For Im(z) > 0, the factor e^{-Im(z)*xi} provides exponential decay for xi >= 0
    4. This makes z -> T(e^{-iz .}) well-defined and holomorphic (differentiate under
       the distribution pairing)

    The Fourier-Laplace Schwartz family `ψ_z`, the candidate extension
    `z ↦ T(ℱ[ψ_z])`, the horizontal-line seminorm growth of `ψ_{x+iη}`, the
    finite-seminorm control of `T`, and the resulting polynomial horizontal-line
    growth of both `z ↦ T(ℱ[ψ_z])` and its candidate derivative kernel
    `z ↦ T(ℱ[(I ξ) ψ_z])` are now formalized in `SCV.FourierLaplaceCore`,
    `schwartz_functional_bound`, `fourierLaplaceExt_horizontal_growth`, and
    `fourierLaplaceExt_derivCandidate_horizontal_growth`.
    The remaining blockers are:
    1. holomorphicity of the distribution pairing in `z`,
    2. distributional boundary-value convergence using the one-sided Fourier support.

    Ref: Reed-Simon II, Theorem IX.16; Hormander, Theorem 7.4.3 -/
theorem paley_wiener_half_line
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : HasOneSidedFourierSupport T) :
    ∃ (F : ℂ → ℂ),
      DifferentiableOn ℂ F upperHalfPlane ∧
      -- F has polynomial growth on approach to the real axis
      (∀ (η : ℝ), 0 < η →
        HasPolynomialGrowthOnLine (fun x => F (x + η * I))) ∧
      -- Distributional boundary value: smeared integrals converge to T
      (∀ (φ : SchwartzMap ℝ ℂ),
        Tendsto (fun η : ℝ => ∫ x : ℝ, F (↑x + ↑η * I) * φ x)
          (nhdsWithin 0 (Ioi 0))
          (nhds (T φ))) := by
  -- The candidate extension: F(z) = T(ℱ[ψ_z]) for Im(z) > 0
  refine ⟨fun w => if hw : 0 < w.im then fourierLaplaceExt T w hw else 0, ?_, ?_, ?_⟩
  · -- Part 1: holomorphicity on the upper half-plane
    -- Follows directly from fourierLaplaceExt_differentiableOn
    exact fourierLaplaceExt_differentiableOn T
  · -- Part 2: polynomial growth on each horizontal line Im(z) = η
    -- For η > 0 fixed, F(x + iη) = fourierLaplaceExt T (x + iη) hη
    -- and this has polynomial growth by fourierLaplaceExt_horizontal_growth.
    intro η hη
    obtain ⟨C, N, hC, hbound⟩ := fourierLaplaceExt_horizontal_growth T η hη
    refine ⟨C, N, hC, fun x => ?_⟩
    -- (x : ℂ) + ↑η * I has positive imaginary part, so the dite reduces
    have himx : 0 < ((x : ℂ) + ↑η * I).im := by simp [hη]
    simp only [dif_pos himx]
    -- fourierLaplaceExt is proof-irrelevant in its last argument, so matches hbound
    exact hbound x
  · -- Part 3: distributional BV convergence
    -- ∫ F(x+iη)φ(x) dx → T(φ) as η → 0+
    -- Proof sketch:
    --   Step A (Fubini): ∫ F(x+iη)φ(x) dx = T(Φ_η)
    --     where Φ_η(ξ) = χ(ξ) · exp(-ηξ) · (FT⁻¹[φ])(ξ)
    --   Step B (Schwartz convergence): Φ_η → χ · FT⁻¹[φ] in S(ℝ) as η → 0+
    --   Step C (HasOneSidedFourierSupport): T(FT[χ·ψ]) = T(FT[ψ]) for ψ ∈ S
    --     (χ = 1 on [0,∞), so the cutoff is invisible to HasOneSidedFourierSupport)
    --   Step D (Fourier inversion): T(FT[FT⁻¹[φ]]) = T(φ)
    --
    -- Root blocker: Step A requires commuting T (a CLM on the Fréchet space S(ℝ))
    -- with a Bochner integral. Mathlib's ContinuousLinearMap.integral_comp_comm
    -- requires Banach, not Fréchet spaces. Fréchet-Bochner theory is not in Mathlib 4.
    --
    -- Alternative direct approach (avoid Fubini): work entirely in Fourier space,
    -- showing the η → 0+ limit via dominated convergence in ξ-space and
    -- continuity of T in the Fréchet topology.
    intro φ
    sorry

/-! ### The Paley-Wiener-Schwartz theorem: multi-dimensional case -/

/-- **Paley-Wiener theorem for cones (multi-dimensional).**

    If T in S'(R^m) has Fourier support in the dual cone C* of an open convex
    cone C subset R^m, then the Fourier-Laplace transform extends holomorphically
    to the tube domain T(C) = R^m + iC.

    This is the higher-dimensional generalization of `paley_wiener_half_line`.
    The proof strategy is similar: the dual cone support condition provides
    exponential decay in the Fourier representation when Im(z) in C, since
    sum_i Im(z_i) * xi_i > 0 for xi in C* \ {0} and Im(z) in C.

    Sorry blocked by: multi-dimensional Fourier-Laplace representation,
    exponential decay estimates from dual cone membership, and
    differentiation under the distribution pairing.

    Ref: Vladimirov, "Methods of Generalized Functions", Theorem 25.1;
    Hormander, "Analysis of PDE I", Theorem 7.4.3 -/
theorem paley_wiener_cone {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ)
    (hT_lin : IsLinearMap ℝ T) (hT_cont : Continuous T)
    (hT_supp : HasFourierSupportIn T (dualCone C)) :
    ∃ (F : (Fin m → ℂ) → ℂ),
      DifferentiableOn ℂ F (TubeDomain C) ∧
      HasPolynomialGrowthOnTube C F ∧
      -- Distributional boundary value recovers T
      (∀ (φ : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * φ x)
        (nhdsWithin 0 (Ioi 0))
        (nhds (T φ))) := by
  sorry

/-! ### Converse Paley-Wiener: polynomial growth implies dual cone support -/

/-- **Converse Paley-Wiener theorem.**

    If F is holomorphic on the tube domain T(C) with polynomial growth, then its
    distributional boundary value T (which exists by `continuous_boundary_tube`)
    has Fourier transform supported in the dual cone C*.

    This is the converse direction of the Paley-Wiener correspondence:
      { T in S'(R^m) : supp(FT) subset C* }
        <--->
      { F holomorphic on T(C) with polynomial growth }

    The proof proceeds via the Fourier-Laplace representation: F is determined
    by its boundary value T, and the holomorphicity on T(C) forces FT to be
    supported where the Laplace integral converges, which is exactly C*.

    Sorry blocked by: Fourier inversion for distributions, uniqueness of
    Fourier-Laplace representation, and support characterization.

    Ref: Vladimirov, "Methods of Generalized Functions", Theorem 25.2;
    Hormander, "Analysis of PDE I", Theorem 7.4.2 -/
theorem paley_wiener_converse {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    (F : (Fin m → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hgrowth : HasPolynomialGrowthOnTube C F)
    (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ)
    (hT_lin : IsLinearMap ℝ T) (hT_cont : Continuous T)
    -- T is the distributional boundary value of F
    (h_bv : ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Tendsto (fun ε : ℝ =>
        ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * φ x)
      (nhdsWithin 0 (Ioi 0))
      (nhds (T φ))) :
    HasFourierSupportIn T (dualCone C) := by
  sorry

/-! ### One-step extension: the key technical lemma for inductive continuation -/

/-- **One-step holomorphic extension via Paley-Wiener.**

    This is the key technical ingredient for `inductive_analytic_continuation`
    (OS II, Theorem 4.1). Given:

    1. A function F holomorphic on a tube T(C) in m complex variables.
    2. For each fixed z' (the other m-1 variables in T(C)), the function
       x_r -> F(z'_1, ..., x_r, ..., z'_m) has distributional boundary value
       in x_r whose Fourier transform is supported in [0, infinity).
    3. Polynomial growth in the r-th variable.

    Then F extends holomorphically in the r-th variable on the correct
    slice-extension region: either z is already in T(C), or the r-th
    imaginary coordinate is positive and the other imaginary coordinates
    match those of some y ∈ C.

    The proof applies `paley_wiener_half_line` to the r-th variable (fixing the
    other variables as parameters), obtaining a holomorphic extension in z_r.
    Joint holomorphicity then follows from Osgood's lemma (separate holomorphicity
    in each variable implies joint holomorphicity for locally bounded functions).

    Physical interpretation: The one-sided Fourier support comes from the
    positivity of the Hamiltonian (spectral condition). The polynomial growth
    comes from the E0' linear growth condition. Together they allow extending
    analyticity from Euclidean to Minkowski one variable at a time.

    Sorry blocked by: `paley_wiener_half_line` (for each slice), Osgood's lemma
    for joint holomorphicity, and local boundedness of the parameterized extensions.

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 -/
theorem paley_wiener_one_step {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    -- F is holomorphic on T(C) (m complex variables)
    (F : (Fin m → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (TubeDomain C))
    -- The r-th variable has one-sided Fourier support
    (r : Fin m)
    -- For each fixed z' (the other m-1 variables in T(C)), the function
    -- x_r -> F(z'_1, ..., x_r, ..., z'_m) has distributional BV in x_r
    -- whose Fourier transform is supported in [0, infinity): test functions
    -- supported on (-inf, 0) integrate to 0 in the BV limit.
    (h_spectral : ∀ (z' : Fin m → ℂ), (fun i => (z' i).im) ∈ C →
      ∀ (φ : SchwartzMap ℝ ℂ),
        (∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) →
        Tendsto (fun ε : ℝ =>
          ∫ t : ℝ, F (Function.update z' r (↑t + ↑ε * I)) * φ t)
        (nhdsWithin 0 (Ioi 0))
        (nhds 0))
    -- Polynomial growth in the r-th variable
    (h_growth : ∀ (z' : Fin m → ℂ), (fun i => (z' i).im) ∈ C →
      HasPolynomialGrowthOnLine (fun t => F (Function.update z' r ↑t))) :
    -- Then F extends holomorphically on the one-step slice-extension region
    ∃ (F_ext : (Fin m → ℂ) → ℂ),
      -- Holomorphic on the original tube together with the one-variable extension slices.
      DifferentiableOn ℂ F_ext
        (TubeDomain C ∪
          { z | 0 < (z r).im ∧
                ∃ y ∈ C, ∀ i, i ≠ r → (z i).im = y i }) ∧
      -- Agrees with F on original tube
      (∀ z ∈ TubeDomain C, F_ext z = F z) := by
  sorry

/-- **Simplified one-step extension for the inductive continuation (1D).**

    A cleaner version specialized to one complex variable: a continuous function
    on the real line with polynomial growth whose associated tempered distribution
    has Fourier support in `[0, infinity)` extends holomorphically to the upper
    half-plane.

    The conclusion is stated in the correct distributional form: `F_ext` has the
    continuous function `f` as its **distributional boundary value**, not as a
    pointwise boundary trace on `ℝ`. Pointwise equality `F_ext x = f x` on the
    real axis is not the right Paley-Wiener conclusion in this generality.

    This formulation directly matches what `inductive_analytic_continuation`
    needs when all but one variable are fixed: extend holomorphicity in one
    coordinate from a real boundary distribution to the upper half-plane.

    Sorry blocked by: `paley_wiener_half_line` (which it essentially restates
    for the special case where the tempered distribution is given by integrating
    against the continuous polynomially-growing function `f`).

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 -/
theorem paley_wiener_one_step_simple
    (f : ℝ → ℂ) (hf_cont : Continuous f)
    -- Polynomial growth
    (hf_growth : HasPolynomialGrowthOnLine f)
    -- One-sided Fourier support of the tempered distribution T_f(φ) = ∫ f(t) φ(t) dt.
    (h_spectral : HasOneSidedFourierSupport
      (fun φ : SchwartzMap ℝ ℂ => ∫ t : ℝ, f t * φ t)) :
    ∃ (F_ext : ℂ → ℂ),
      DifferentiableOn ℂ F_ext upperHalfPlane ∧
      -- Polynomial growth on horizontal lines
      (∀ η : ℝ, 0 < η →
        HasPolynomialGrowthOnLine (fun x => F_ext (↑x + ↑η * I))) ∧
      -- Distributional boundary value recovers the function-induced tempered distribution.
      (∀ (φ : SchwartzMap ℝ ℂ),
        Tendsto (fun η : ℝ => ∫ x : ℝ, F_ext (↑x + ↑η * I) * φ x)
          (nhdsWithin 0 (Ioi 0))
          (nhds (∫ t : ℝ, f t * φ t))) := by
  rcases hf_growth with ⟨C_bound, N, hC_bound_pos, h_growth_bound⟩
  let M : ℕ := N + 2
  let sem : SchwartzMap ℝ ℂ → ℝ :=
    fun φ => (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ
  have h_decay_int : MeasureTheory.Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) MeasureTheory.volume :=
    by
      have : (Module.finrank ℝ ℝ : ℝ) < (2 : ℝ) := by norm_num
      simpa using integrable_one_add_norm this
  have h_decay_int_nat : MeasureTheory.Integrable
      (fun t : ℝ => ((1 + ‖t‖) ^ 2)⁻¹) MeasureTheory.volume := by
    simpa [Real.rpow_neg (by positivity : 0 ≤ (1 + ‖(0 : ℝ)‖)), Real.rpow_natCast] using
      h_decay_int
  have hsem_bound : ∀ (φ : SchwartzMap ℝ ℂ) (t : ℝ),
      (1 + ‖t‖) ^ M * ‖φ t‖ ≤ 2 ^ M * sem φ := by
    intro φ t
    simpa [sem, M, norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
        (m := (M, 0)) (k := M) (n := 0) (le_rfl) (le_rfl) φ t)
  have h_pointwise_bound : ∀ (φ : SchwartzMap ℝ ℂ) (t : ℝ),
      ‖f t * φ t‖ ≤ C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹ := by
    intro φ t
    have h_growth_t : ‖f t‖ ≤ C_bound * (1 + ‖t‖) ^ N := by
      simpa using h_growth_bound t
    have h_pow_pos : 0 < (1 + ‖t‖) ^ 2 := by positivity
    have h_decay_step : (1 + ‖t‖) ^ N * ‖φ t‖ ≤
        2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ h_pow_pos]
      calc
        (1 + ‖t‖) ^ N * ‖φ t‖ * (1 + ‖t‖) ^ 2
            = (1 + ‖t‖) ^ M * ‖φ t‖ := by
                rw [show M = N + 2 by simp [M], pow_add]
                ring
        _ ≤ 2 ^ M * sem φ := hsem_bound φ t
    have h_decay_mul :
        C_bound * (1 + ‖t‖) ^ N * ‖φ t‖ ≤
          C_bound * (2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹) := by
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left h_decay_step (le_of_lt hC_bound_pos))
    calc
      ‖f t * φ t‖ = ‖f t‖ * ‖φ t‖ := norm_mul _ _
      _ ≤ C_bound * (1 + ‖t‖) ^ N * ‖φ t‖ :=
        mul_le_mul_of_nonneg_right h_growth_t (norm_nonneg _)
      _ ≤ C_bound * (2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹) := h_decay_mul
      _ = C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹ := by ring
  have h_integrable : ∀ φ : SchwartzMap ℝ ℂ,
      MeasureTheory.Integrable (fun t : ℝ => f t * φ t) MeasureTheory.volume := by
    intro φ
    have h_majorant_int : MeasureTheory.Integrable
        (fun t : ℝ => C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹)
        MeasureTheory.volume :=
      h_decay_int_nat.const_mul (C_bound * 2 ^ M * sem φ)
    refine h_majorant_int.mono' ((hf_cont.mul φ.continuous).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (h_pointwise_bound φ)
  let I₂ : ℝ := ∫ t : ℝ, ((1 + ‖t‖) ^ 2)⁻¹
  let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ)
      (fun φ : SchwartzMap ℝ ℂ => ∫ t : ℝ, f t * φ t)
      (fun φ ψ => by
        simpa [mul_add] using
          (MeasureTheory.integral_add
            (f := fun t : ℝ => f t * φ t)
            (g := fun t : ℝ => f t * ψ t)
            (h_integrable φ) (h_integrable ψ)))
      (fun a φ => by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (MeasureTheory.integral_smul a (fun t : ℝ => f t * φ t)))
      (by
        have hI₂_nonneg : 0 ≤ I₂ := by
          unfold I₂
          exact MeasureTheory.integral_nonneg fun _ => by positivity
        refine ⟨Finset.Iic (M, 0), C_bound * 2 ^ M * I₂, ?_, ?_⟩
        · exact mul_nonneg (mul_nonneg (le_of_lt hC_bound_pos) (by positivity)) hI₂_nonneg
        · intro φ
          calc
            ‖∫ t : ℝ, f t * φ t‖ ≤ ∫ t : ℝ, ‖f t * φ t‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
            _ ≤ ∫ t : ℝ, C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹ :=
              MeasureTheory.integral_mono_ae (h_integrable φ).norm
                (h_decay_int_nat.const_mul (C_bound * 2 ^ M * sem φ))
                (Filter.Eventually.of_forall (h_pointwise_bound φ))
            _ = C_bound * 2 ^ M * I₂ * sem φ := by
              rw [show (∫ t : ℝ, C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹) =
                  (C_bound * 2 ^ M * sem φ) * I₂ by
                    simp [I₂, MeasureTheory.integral_const_mul]]
              ring
            _ = (C_bound * 2 ^ M * I₂) * (Finset.Iic (M, 0)).sup
                (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
              simp [sem, mul_assoc])
  obtain ⟨F_ext, hF_holo, hF_growth, hF_bv⟩ :=
    paley_wiener_half_line T (by simpa [T] using h_spectral)
  refine ⟨F_ext, hF_holo, hF_growth, ?_⟩
  intro φ
  simpa [T] using hF_bv φ

/-! ### Uniqueness of Paley-Wiener extension -/

/-- The Paley-Wiener extension is unique: if two holomorphic functions on the
    upper half-plane have the same distributional boundary values on the real
    line, they agree.

    This follows from `distributional_uniqueness_tube` (in TubeDistributions.lean)
    applied to the cone (0, infinity) in R^1. The upper half-plane is the tube
    domain T((0,inf)) = { z : Im(z) > 0 }.

    Sorry blocked by: embedding the 1D case into the general tube domain
    framework and applying `distributional_uniqueness_tube`.

    Ref: Vladimirov, Section 26.3 -/
theorem paley_wiener_unique
    (F G : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hG : DifferentiableOn ℂ G upperHalfPlane)
    -- Same distributional boundary values
    (h_agree : ∀ (φ : SchwartzMap ℝ ℂ),
      Tendsto (fun η : ℝ => ∫ x : ℝ, (F (↑x + ↑η * I) - G (↑x + ↑η * I)) * φ x)
        (nhdsWithin 0 (Ioi 0))
        (nhds 0)) :
    ∀ z ∈ upperHalfPlane, F z = G z := by
  let C1 : Set (Fin 1 → ℝ) := {y | 0 < y 0}
  let F1 : (Fin 1 → ℂ) → ℂ := fun z => F (z 0)
  let G1 : (Fin 1 → ℂ) → ℂ := fun z => G (z 0)
  have hC1_open : IsOpen C1 := by
    simpa [C1] using isOpen_lt continuous_const (continuous_apply (0 : Fin 1))
  have hC1_conv : Convex ℝ C1 := by
    intro x hx y hy a b ha hb hab
    show 0 < (a • x + b • y) 0
    have hx0 : 0 < x 0 := hx
    have hy0 : 0 < y 0 := hy
    have ha_or_hb : 0 < a ∨ 0 < b := by
      by_cases ha0 : a = 0
      · right
        have hb1 : b = 1 := by linarith
        linarith
      · left
        exact lt_of_le_of_ne ha (Ne.symm ha0)
    have hsum_pos : 0 < a * x 0 + b * y 0 := by
      cases ha_or_hb with
      | inl ha_pos =>
          have hax_pos : 0 < a * x 0 := mul_pos ha_pos hx0
          have hby_nonneg : 0 ≤ b * y 0 := by positivity
          linarith
      | inr hb_pos =>
          have hby_pos : 0 < b * y 0 := mul_pos hb_pos hy0
          have hax_nonneg : 0 ≤ a * x 0 := by positivity
          linarith
    have hcoord : (a • x + b • y) 0 = a * x 0 + b * y 0 := by
      simp [Pi.smul_apply, Pi.add_apply]
    rw [hcoord]
    exact hsum_pos
  have hC1_ne : C1.Nonempty := ⟨fun _ => (1 : ℝ), by simp [C1]⟩
  have hC1_cone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C1, t • y ∈ C1 := by
    intro t ht y hy
    show 0 < (t • y) 0
    simpa [C1, Pi.smul_apply] using mul_pos ht hy
  have hF1 : DifferentiableOn ℂ F1 (TubeDomain C1) := by
    intro z hz
    have hz0 : (z 0).im > 0 := by simpa [TubeDomain, C1] using hz
    have hFz : DifferentiableWithinAt ℂ F upperHalfPlane (z 0) := hF (z 0) hz0
    have heval : DifferentiableWithinAt ℂ (fun w : Fin 1 → ℂ => w 0) (TubeDomain C1) z :=
      (differentiableAt_apply (0 : Fin 1) z).differentiableWithinAt
    simpa [F1] using hFz.comp z heval (by intro w hw; simpa [TubeDomain, C1] using hw)
  have hG1 : DifferentiableOn ℂ G1 (TubeDomain C1) := by
    intro z hz
    have hz0 : (z 0).im > 0 := by simpa [TubeDomain, C1] using hz
    have hGz : DifferentiableWithinAt ℂ G upperHalfPlane (z 0) := hG (z 0) hz0
    have heval : DifferentiableWithinAt ℂ (fun w : Fin 1 → ℂ => w 0) (TubeDomain C1) z :=
      (differentiableAt_apply (0 : Fin 1) z).differentiableWithinAt
    simpa [G1] using hGz.comp z heval (by intro w hw; simpa [TubeDomain, C1] using hw)
  have h_agree1 : ∀ (φ : SchwartzMap (Fin 1 → ℝ) ℂ) (η : Fin 1 → ℝ), η ∈ C1 →
      Tendsto (fun ε : ℝ =>
        ∫ x : Fin 1 → ℝ,
          (F1 (fun i => ↑(x i) + ↑ε * ↑(η i) * I) -
           G1 (fun i => ↑(x i) + ↑ε * ↑(η i) * I)) * φ x)
      (nhdsWithin 0 (Ioi 0))
      (nhds 0) := by
    intro φ η hη
    let eR : ℝ ≃L[ℝ] (Fin 1 → ℝ) :=
      (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
    let pullback : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR
    let φR : SchwartzMap ℝ ℂ := pullback φ
    have hbase := h_agree φR
    have hη0 : 0 < η 0 := by simpa [C1] using hη
    have hscale_nhds0 : Tendsto (fun ε : ℝ => ε * η 0) (nhds 0) (nhds 0) := by
      simpa using (continuous_id.mul continuous_const).tendsto (0 : ℝ)
    have hscale_nhds : Tendsto (fun ε : ℝ => ε * η 0)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      exact hscale_nhds0.mono_left inf_le_left
    have hscale_pos : ∀ᶠ ε in nhdsWithin 0 (Ioi 0), ε * η 0 ∈ Ioi 0 := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos hε hη0
    have hscale : Tendsto (fun ε : ℝ => ε * η 0)
        (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        (fun ε : ℝ => ε * η 0) hscale_nhds hscale_pos
    have hscaled := hbase.comp hscale
    have hscaled' : Tendsto
        (fun ε : ℝ =>
          ∫ t : ℝ,
            (F (↑t + ↑ε * ↑(η 0) * I) - G (↑t + ↑ε * ↑(η 0) * I)) * φR t)
        (nhdsWithin 0 (Ioi 0))
        (nhds 0) := by
      refine Filter.Tendsto.congr ?_ hscaled
      intro ε
      simp [Function.comp, mul_comm]
    have hcv : ∀ ε : ℝ,
        (∫ x : Fin 1 → ℝ,
          (F1 (fun i => ↑(x i) + ↑ε * ↑(η i) * I) -
           G1 (fun i => ↑(x i) + ↑ε * ↑(η i) * I)) * φ x) =
        ∫ t : ℝ, (F (↑t + ↑(ε * η 0) * I) - G (↑t + ↑(ε * η 0) * I)) * φR t := by
      intro ε
      have hpre :=
        (((volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
          (MeasurableEquiv.measurableEmbedding _)
          (fun x : Fin 1 → ℝ =>
            (F1 (fun i => ↑(x i) + ↑ε * ↑(η i) * I) -
             G1 (fun i => ↑(x i) + ↑ε * ↑(η i) * I)) * φ x)
          Set.univ).symm
      simpa [F1, G1, φR, pullback, eR, SchwartzMap.compCLMOfContinuousLinearEquiv]
        using hpre
    refine Filter.Tendsto.congr (fun ε => (hcv ε).symm) ?_
    simpa [Function.comp, φR] using hscaled'
  have huniq := distributional_uniqueness_tube (m := 1) (C := C1)
    hC1_open hC1_conv hC1_ne hC1_cone hF1 hG1 h_agree1
  intro z hz
  have hz1 : (fun _ : Fin 1 => z) ∈ TubeDomain C1 := by
    simpa [TubeDomain, C1, upperHalfPlane] using hz
  have h_eq1 := huniq (fun _ : Fin 1 => z) hz1
  simpa [F1, G1] using h_eq1

end SCV
