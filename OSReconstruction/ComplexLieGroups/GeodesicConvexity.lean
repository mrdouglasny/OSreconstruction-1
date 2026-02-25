/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.Complexification

/-!
# Geodesic Convexity for the Forward Light Cone

The forward light cone V₊ ⊂ ℝ^{d+1} is "geodesically convex" under the
one-parameter subgroups of the complex Lorentz group: if exp(iY)·w has
imaginary part in V₊ at t=0 and t=1, then it stays in V₊ for all t ∈ [0,1].

This is the key analytical ingredient for proving that the orbit set
O_w = {Λ ∈ SO⁺(1,d;ℂ) : Λ·w ∈ ForwardTube} is path-connected.

## Main results

- `InOpenForwardCone`: Definition of the open forward light cone.
- `inOpenForwardCone_convex`: The forward cone is convex.
- `real_lorentz_preserves_forwardCone`: Real Lorentz transformations preserve V₊.
- `ofReal_im_action`: For real Lorentz R, Im(R·w) = R·Im(w).
- `geodesic_convexity_forwardCone`: The geodesic convexity theorem.

Ref: Streater & Wightman, Theorem 2-11; Bros-Epstein-Glaser (1967).
-/

noncomputable section

open Topology Matrix LorentzLieGroup ComplexLorentzGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-! ### Forward light cone definition and properties -/

/-- The open forward light cone: η₀ > 0 and η·η < 0 (timelike, future-pointing). -/
def InOpenForwardCone (d : ℕ) (η : Fin (d + 1) → ℝ) : Prop :=
  η 0 > 0 ∧ ∑ μ, minkowskiSignature d μ * η μ ^ 2 < 0

/-- Decompose the Minkowski quadratic form into time and spatial parts:
    Q(η) = -(η₀)² + ∑_{i>0} (ηᵢ)². -/
lemma minkowski_sum_decomp (η : Fin (d + 1) → ℝ) :
    ∑ μ, minkowskiSignature d μ * η μ ^ 2 =
    -(η 0) ^ 2 + ∑ i : Fin d, (η (Fin.succ i)) ^ 2 := by
  rw [Fin.sum_univ_succ]; congr 1
  · simp [minkowskiSignature]
  · congr 1; ext i; simp [minkowskiSignature, Fin.succ_ne_zero]

/-- For η in the forward cone, the spatial norm is less than the time component. -/
lemma spatial_norm_lt_time {η : Fin (d + 1) → ℝ} (h : InOpenForwardCone d η) :
    Real.sqrt (∑ i : Fin d, (η (Fin.succ i)) ^ 2) < η 0 := by
  rw [show η 0 = Real.sqrt ((η 0) ^ 2) from (Real.sqrt_sq (le_of_lt h.1)).symm]
  exact Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (by have := h.2; rw [minkowski_sum_decomp] at this; linarith)

/-- Expand ∑(ax + by)² into a²∑x² + 2ab∑xy + b²∑y². -/
private lemma sum_sq_expand {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) :
    ∑ i : Fin n, (a * x i + b * y i) ^ 2 =
    a ^ 2 * ∑ i : Fin n, x i ^ 2 + 2 * (a * b) * ∑ i : Fin n, x i * y i +
    b ^ 2 * ∑ i : Fin n, y i ^ 2 := by
  trans (∑ i : Fin n, (a ^ 2 * x i ^ 2 + 2 * (a * b) * (x i * y i) + b ^ 2 * y i ^ 2))
  · congr 1; ext i; ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Triangle inequality squared: ∑(ax+by)² ≤ (a‖x‖ + b‖y‖)². Uses Cauchy-Schwarz. -/
private lemma sum_sq_convex_combo_le {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∑ i : Fin n, (a * x i + b * y i) ^ 2 ≤
    (a * Real.sqrt (∑ i, x i ^ 2) + b * Real.sqrt (∑ i, y i ^ 2)) ^ 2 := by
  rw [sum_sq_expand]
  set sx := ∑ i : Fin n, x i ^ 2; set sy := ∑ i : Fin n, y i ^ 2
  have hsx_nn : 0 ≤ sx := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsy_nn : 0 ≤ sy := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hRHS : (a * Real.sqrt sx + b * Real.sqrt sy) ^ 2 =
      a ^ 2 * sx + 2 * (a * b) * (Real.sqrt sx * Real.sqrt sy) + b ^ 2 * sy := by
    nlinarith [Real.sq_sqrt hsx_nn, Real.sq_sqrt hsy_nn]
  rw [hRHS]
  linarith [mul_le_mul_of_nonneg_left
    (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y) (by positivity : 0 ≤ 2 * (a * b))]

/-- **The open forward light cone is convex.** -/
theorem inOpenForwardCone_convex :
    Convex ℝ {η : Fin (d + 1) → ℝ | InOpenForwardCone d η} := by
  intro η₁ hη₁ η₂ hη₂ a b ha hb hab
  simp only [Set.mem_setOf_eq] at hη₁ hη₂ ⊢
  have h_combo : a • η₁ + b • η₂ = fun μ => a * η₁ μ + b * η₂ μ := by
    ext μ; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [InOpenForwardCone, h_combo]
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le ha with rfl | ha'
    · simp at hab; rw [hab]; simp [hη₂.1]
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hη₁.1) (mul_nonneg hb (le_of_lt hη₂.1))
  · rw [minkowski_sum_decomp]
    suffices h : ∑ i : Fin d, (a * η₁ (Fin.succ i) + b * η₂ (Fin.succ i)) ^ 2 <
        (a * η₁ 0 + b * η₂ 0) ^ 2 by linarith
    have h1 := sum_sq_convex_combo_le
      (fun i => η₁ (Fin.succ i)) (fun i => η₂ (Fin.succ i)) a b ha hb
    have hsx := spatial_norm_lt_time hη₁
    have hsy := spatial_norm_lt_time hη₂
    have h_combo_lt : a * Real.sqrt (∑ i, η₁ (Fin.succ i) ^ 2) +
        b * Real.sqrt (∑ i, η₂ (Fin.succ i) ^ 2) < a * η₁ 0 + b * η₂ 0 := by
      rcases eq_or_lt_of_le ha with rfl | ha'
      · simp at hab ⊢; rw [hab]; simp; exact hsy
      · linarith [mul_lt_mul_of_pos_left hsx ha',
                   mul_le_mul_of_nonneg_left (le_of_lt hsy) hb]
    calc ∑ i, (a * η₁ (Fin.succ i) + b * η₂ (Fin.succ i)) ^ 2
        ≤ _ := h1
      _ < (a * η₁ 0 + b * η₂ 0) ^ 2 :=
          pow_lt_pow_left₀ h_combo_lt (by positivity) two_ne_zero

/-! ### Lorentz transformation preserves the Minkowski quadratic form -/

/-- The Minkowski quadratic form is preserved by Lorentz transformations.
    Q(Λ·v) = Q(v) for any Lorentz matrix Λ.

    Proof: Q(Λv) = ∑ s_μ (Λv)_μ² = ∑_ν ∑_ρ (∑_μ Λ_μν s_μ Λ_μρ) v_ν v_ρ
    = ∑_ν ∑_ρ δ_{νρ} s_ν v_ν v_ρ = ∑_ν s_ν v_ν² = Q(v). -/
theorem lorentz_preserves_quadratic_form
    (Λ : RestrictedLorentzGroup d) (v : Fin (d + 1) → ℝ) :
    ∑ μ, minkowskiSignature d μ * (∑ ν, Λ.val.val μ ν * v ν) ^ 2 =
    ∑ μ, minkowskiSignature d μ * v μ ^ 2 := by
  -- Extract the Lorentz condition entry by entry
  have hL := Λ.val.prop  -- ΛᵀηΛ = η
  have hEntry : ∀ ν ρ : Fin (d + 1),
      ∑ α, Λ.val.val α ν * minkowskiSignature d α * Λ.val.val α ρ =
      if ν = ρ then minkowskiSignature d ν else 0 := by
    intro ν ρ
    have h := congr_fun (congr_fun hL ν) ρ
    simp only [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMatrix,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at h
    convert h using 1
  -- Step 1: Expand (∑_ν R_μν v_ν)² into double sum
  -- Step 2: Swap sums to get ∑_ν ∑_ρ (∑_μ ...) v_ν v_ρ
  -- Step 3: Apply Lorentz condition to inner sum
  -- Step 4: Collapse diagonal sum
  calc ∑ μ, minkowskiSignature d μ * (∑ ν, Λ.val.val μ ν * v ν) ^ 2
      = ∑ μ, ∑ ν, ∑ ρ,
          Λ.val.val μ ν * minkowskiSignature d μ * Λ.val.val μ ρ * (v ν * v ρ) := by
        congr 1; ext μ
        rw [sq]; simp only [Finset.sum_mul, Finset.mul_sum]
        congr 1; ext ν; congr 1; ext ρ; ring
    _ = ∑ ν, ∑ ρ, ∑ μ,
          Λ.val.val μ ν * minkowskiSignature d μ * Λ.val.val μ ρ * (v ν * v ρ) := by
        rw [Finset.sum_comm]; congr 1; ext ν; rw [Finset.sum_comm]
    _ = ∑ ν, ∑ ρ,
          (∑ μ, Λ.val.val μ ν * minkowskiSignature d μ * Λ.val.val μ ρ) * (v ν * v ρ) := by
        congr 1; ext ν; congr 1; ext ρ; rw [Finset.sum_mul]
    _ = ∑ ν, ∑ ρ, (if ν = ρ then minkowskiSignature d ν else 0) * (v ν * v ρ) := by
        simp_rw [hEntry]
    _ = ∑ ν, minkowskiSignature d ν * v ν ^ 2 := by
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        congr 1; ext ν; ring

/-! ### Real Lorentz preserves the forward cone -/

/-- The imaginary part of a real Lorentz transformation applied to a complex vector
    equals the real Lorentz transformation applied to the imaginary part.
    Since R is real: Im(R·w) = R·Im(w). -/
theorem ofReal_im_action (R : RestrictedLorentzGroup d)
    (w : Fin (d + 1) → ℂ) (μ : Fin (d + 1)) :
    (∑ ν, (ComplexLorentzGroup.ofReal R).val μ ν * w ν).im =
    ∑ ν, R.val.val μ ν * (w ν).im := by
  simp only [ComplexLorentzGroup.ofReal]
  -- Pull .im through ∑ using Complex.imLm (ℂ →ₗ[ℝ] ℝ)
  rw [show (∑ ν, (↑(R.val.val μ ν) : ℂ) * w ν).im =
    ∑ ν, ((↑(R.val.val μ ν) : ℂ) * w ν).im from by
      change ⇑Complex.imLm (∑ ν, _) = _; rw [map_sum]; simp [Complex.imLm_coe]]
  congr 1; ext ν
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- Real restricted Lorentz transformations preserve the open forward light cone.

    Since the Minkowski metric is preserved by the restricted Lorentz group
    and the orthochronous condition preserves the sign of the time component,
    we get η ∈ V₊ → R·η ∈ V₊ for R ∈ SO↑₊(1,d;ℝ). -/
theorem real_lorentz_preserves_forwardCone (R : RestrictedLorentzGroup d)
    (η : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η) :
    InOpenForwardCone d (fun μ => ∑ ν, R.val.val μ ν * η ν) := by
  constructor
  · -- Time component: (R·η)₀ > 0
    -- Uses R₀₀ ≥ 1, Cauchy-Schwarz, and spatial_norm_lt_time
    simp only
    -- Decompose: (R·η)₀ = R₀₀ * η₀ + ∑_{i>0} R_{0,i+1} * η_{i+1}
    rw [Fin.sum_univ_succ]
    -- The main term R₀₀ * η₀ > 0 dominates the spatial correction
    have hR00 : R.val.val 0 0 ≥ 1 := R.prop.2
    have h_spatial_η := spatial_norm_lt_time hη
    have hR_row := row0_sum_sq d R.val.prop
    -- Lower bound on spatial sum: apply CS to (-R, η) to get -spatial ≤ sqrt(∑R²)·sqrt(∑η²)
    have hCS_neg := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i : Fin d => -(R.val.val 0 i.succ)) (fun i => η i.succ)
    simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at hCS_neg
    -- So spatial ≥ -sqrt(∑R²) · sqrt(∑η²)
    -- sqrt(∑ R_{0,k+1}²) ≤ R₀₀ since ∑ R² = R₀₀² - 1 ≤ R₀₀²
    have hR_sq_nn : 0 ≤ ∑ k : Fin d, R.val.val 0 k.succ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hη_sq_nn : 0 ≤ ∑ i : Fin d, η i.succ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    set sqR := ∑ k : Fin d, R.val.val 0 k.succ ^ 2 with sqR_def
    set sqη := ∑ i : Fin d, η i.succ ^ 2 with sqη_def
    have h_sqrt_R_le : Real.sqrt sqR ≤ R.val.val 0 0 := by
      calc Real.sqrt sqR
          ≤ Real.sqrt (R.val.val 0 0 ^ 2) := by
            apply Real.sqrt_le_sqrt; linarith [hR_row]
        _ = |R.val.val 0 0| := Real.sqrt_sq_eq_abs _
        _ = R.val.val 0 0 := abs_of_nonneg (by linarith)
    -- Combine: R₀₀ η₀ + spatial ≥ R₀₀ η₀ - R₀₀ · sqrt(∑η²) = R₀₀(η₀ - sqrt(∑η²)) > 0
    have h_key : -(Real.sqrt sqR * Real.sqrt sqη) ≤
        ∑ i : Fin d, R.val.val 0 i.succ * η i.succ := by
      linarith
    linarith [mul_le_mul_of_nonneg_right h_sqrt_R_le (Real.sqrt_nonneg sqη),
              mul_pos (show (0 : ℝ) < R.val.val 0 0 from by linarith)
                (show (0 : ℝ) < η 0 - Real.sqrt sqη from by linarith)]
  · -- Minkowski norm preserved: Q(R·η) = Q(η) < 0
    rw [lorentz_preserves_quadratic_form]
    exact hη.2

/-! ### Lie algebra embedding -/

/-- The Lie algebra of SO(1,d;ℝ) embedded into complex matrices via i·Y.
    If Y ∈ so(1,d;ℝ), then i·(Y.map ofReal) ∈ so(1,d;ℂ). -/
theorem isInLieAlgebra_of_real_times_I
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) :
    IsInLieAlgebra (Complex.I • Y.map Complex.ofReal) := by
  unfold IsInLieAlgebra
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
  suffices h : (Y.map Complex.ofReal).transpose * ηℂ + ηℂ * Y.map Complex.ofReal = 0 by
    rw [h, smul_zero]
  -- Cast the real Lorentz algebra condition to ℂ using RingHom.mapMatrix
  -- hY : Yᵀ * minkowskiMatrix d + minkowskiMatrix d * Y = 0  (over ℝ)
  -- Goal: (Y.map ofReal)ᵀ * ηℂ + ηℂ * Y.map ofReal = 0  (over ℂ)
  -- Key: both sides equal Complex.ofRealHom.mapMatrix applied to hY
  -- Rewrite all terms to Complex.ofRealHom.mapMatrix form, then apply hY
  rw [show (Y.map Complex.ofReal).transpose = Complex.ofRealHom.mapMatrix Y.transpose from by
        ext i j; simp [RingHom.mapMatrix_apply, Matrix.transpose_apply, Matrix.map_apply],
      show ηℂ = Complex.ofRealHom.mapMatrix (minkowskiMatrix d) from by
        ext i j; simp [RingHom.mapMatrix_apply, ηℂ, minkowskiMatrix, Matrix.diagonal_apply]
        split <;> simp,
      show Y.map Complex.ofReal = Complex.ofRealHom.mapMatrix Y from by
        ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply],
      ← map_mul, ← map_mul, ← map_add, hY, map_zero]

/-! ### Geodesic path in the complex Lorentz group -/

/-- For Y ∈ so(1,d;ℝ), the matrix exp(itY) (viewed as a complex Lorentz transformation)
    is a one-parameter subgroup of SO⁺(1,d;ℂ). Using the smul form
    t • (I • Y.map ofReal) which equals (t * I) • Y.map ofReal by smul_smul. -/
def realAlgPath (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) (t : ℝ) : ComplexLorentzGroup d :=
  expLieAlg ((t : ℂ) • (Complex.I • Y.map Complex.ofReal))
    (isInLieAlgebra_smul (↑t) (isInLieAlgebra_of_real_times_I Y hY))

/-- The real algebra path at t=0 is the identity. -/
theorem realAlgPath_zero (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) :
    realAlgPath Y hY 0 = 1 := by
  simp only [realAlgPath, expLieAlg, Complex.ofReal_zero, zero_smul]
  ext i j
  simp [NormedSpace.exp_zero]

/-- The path t ↦ realAlgPath Y hY t is continuous. -/
theorem realAlgPath_continuous (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) :
    Continuous (realAlgPath Y hY) := by
  apply continuous_induced_rng.mpr
  -- val ∘ realAlgPath Y hY = fun t ↦ exp(t • (I • Y.map ofReal))
  exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

/-- The one-parameter subgroup property: exp(isY) * exp(itY) = exp(i(s+t)Y). -/
theorem realAlgPath_mul (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) (s t : ℝ) :
    realAlgPath Y hY s * realAlgPath Y hY t = realAlgPath Y hY (s + t) := by
  apply ComplexLorentzGroup.ext
  show NormedSpace.exp ((s : ℂ) • (Complex.I • Y.map Complex.ofReal)) *
    NormedSpace.exp ((t : ℂ) • (Complex.I • Y.map Complex.ofReal)) =
    NormedSpace.exp (((s + t : ℝ) : ℂ) • (Complex.I • Y.map Complex.ofReal))
  rw [← Matrix.exp_add_of_commute]
  · congr 1
    rw [Complex.ofReal_add, add_smul]
  · exact (Commute.refl _).smul_left _ |>.smul_right _

/-- Scaling Y by c and evaluating at t=1 equals evaluating at t=c. -/
theorem realAlgPath_smul_eq (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) (c : ℝ) :
    realAlgPath (c • Y) (isInLorentzAlgebra_smul d hY c) 1 =
    realAlgPath Y hY c := by
  apply ComplexLorentzGroup.ext
  show NormedSpace.exp ((1 : ℂ) • (Complex.I • (c • Y).map Complex.ofReal)) =
    NormedSpace.exp ((c : ℂ) • (Complex.I • Y.map Complex.ofReal))
  congr 1
  ext i j
  simp [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  ring

/-! ### Entrywise complex conjugation of matrices -/

/-- Entrywise complex conjugation of a matrix. -/
abbrev conjMap (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  M.map star

/-- Bridge lemma: conjMap equals (starRingEnd ℂ).mapMatrix. -/
private theorem conjMap_eq_mapMatrix (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap M = (starRingEnd ℂ).mapMatrix M := by
  ext i j; simp [RingHom.mapMatrix_apply]

theorem conjMap_mul (M N : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap (M * N) = conjMap M * conjMap N := by
  rw [conjMap_eq_mapMatrix, conjMap_eq_mapMatrix, conjMap_eq_mapMatrix, map_mul]

theorem conjMap_involutive (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap (conjMap M) = M := by
  ext i j; simp [Matrix.map_apply]

theorem conjMap_det (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    (conjMap M).det = star M.det := by
  rw [conjMap_eq_mapMatrix]
  exact ((starRingEnd ℂ).map_det M).symm

theorem conjMap_one : conjMap (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = 1 := by
  rw [conjMap_eq_mapMatrix, map_one]

/-- Entrywise conjugation of a matrix exponential equals the exponential of the
    entrywise conjugation: conj(exp X) = exp(conj X).

    Proof chain: M.map star = Mᴴᵀ, then use star_exp and exp_transpose. -/
theorem conjMap_exp (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap (NormedSpace.exp X) = NormedSpace.exp (conjMap X) := by
  -- map star = conjTranspose.transpose
  rw [show conjMap (NormedSpace.exp X) =
      (NormedSpace.exp X).conjTranspose.transpose from
    (Matrix.conjTranspose_transpose _).symm]
  -- star_exp: star(exp X) = exp(star X), i.e., (exp X)ᴴ = exp(Xᴴ)
  rw [show (NormedSpace.exp X).conjTranspose = NormedSpace.exp X.conjTranspose from by
    rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose]
    exact NormedSpace.star_exp X]
  -- exp_transpose: exp(Aᵀ) = (exp A)ᵀ, backwards: (exp B)ᵀ = exp(Bᵀ)
  rw [← Matrix.exp_transpose, Matrix.conjTranspose_transpose]

/-- Conjugation of I • Y.map ofReal gives -(I • Y.map ofReal) for real Y. -/
theorem conjMap_real_I_smul (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    conjMap (Complex.I • Y.map Complex.ofReal) = -(Complex.I • Y.map Complex.ofReal) := by
  ext i j; simp [Matrix.map_apply, Matrix.smul_apply, Complex.conj_I,
    Complex.conj_ofReal, Matrix.neg_apply]

/-- Conjugation fixes real matrices. -/
theorem conjMap_real (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    conjMap (M.map Complex.ofReal) = M.map Complex.ofReal := by
  ext i j; simp [Matrix.map_apply, Complex.conj_ofReal]

/-- The Minkowski metric matrix η is fixed by conjugation (it's real). -/
theorem conjMap_eta : conjMap (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = ηℂ := by
  ext i j
  simp only [Matrix.map_apply, ηℂ, Matrix.diagonal_apply, minkowskiSignature]
  split_ifs <;> simp

/-- Conjugation commutes with transpose. -/
theorem conjMap_transpose (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap M.transpose = (conjMap M).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply]

/-! ### Conjugation on the complex Lorentz group -/

/-- Entrywise complex conjugation defines a group automorphism of SO⁺(1,d;ℂ). -/
def conjLG (Λ : ComplexLorentzGroup d) : ComplexLorentzGroup d where
  val := conjMap Λ.val
  metric_preserving := by
    -- Apply the ring hom (starRingEnd ℂ) to the matrix equation Λᵀ η Λ = η
    apply of_metric_preserving_matrix
    have hΛ := metric_preserving_matrix Λ
    -- conjMap(Λᵀ η Λ) = conjMap Λᵀ * conjMap η * conjMap Λ = (conjMap Λ)ᵀ * η * conjMap Λ
    have h := congr_arg conjMap hΛ
    rw [conjMap_mul, conjMap_mul, conjMap_eta, conjMap_transpose] at h
    exact h
  proper := by
    show (conjMap Λ.val).det = 1
    rw [conjMap_det, Λ.proper, star_one]

@[simp] theorem conjLG_val (Λ : ComplexLorentzGroup d) :
    (conjLG Λ).val = conjMap Λ.val := rfl

theorem conjLG_involutive (Λ : ComplexLorentzGroup d) :
    conjLG (conjLG Λ) = Λ := by
  apply ComplexLorentzGroup.ext
  exact conjMap_involutive Λ.val

theorem conjLG_mul (Λ₁ Λ₂ : ComplexLorentzGroup d) :
    conjLG (Λ₁ * Λ₂) = conjLG Λ₁ * conjLG Λ₂ := by
  apply ComplexLorentzGroup.ext
  exact conjMap_mul Λ₁.val Λ₂.val

theorem conjLG_one : conjLG (1 : ComplexLorentzGroup d) = 1 := by
  apply ComplexLorentzGroup.ext
  exact conjMap_one

/-- Conjugation fixes the image of the real Lorentz group embedding. -/
theorem conjLG_ofReal (R : RestrictedLorentzGroup d) :
    conjLG (ComplexLorentzGroup.ofReal R) = ComplexLorentzGroup.ofReal R := by
  apply ComplexLorentzGroup.ext
  ext i j
  simp only [conjLG_val, ComplexLorentzGroup.ofReal, Matrix.map_apply]
  exact Complex.conj_ofReal _

/-- For any Λ ∈ SO⁺(1,d;ℂ), the group inverse satisfies Λ⁻¹.val * Λ.val = 1. -/
private theorem group_inv_mul_val (Λ : ComplexLorentzGroup d) :
    Λ⁻¹.val * Λ.val = 1 := by
  have h : Λ⁻¹ * Λ = 1 := inv_mul_cancel Λ
  exact congr_arg ComplexLorentzGroup.val h

/-- For any Λ ∈ SO⁺(1,d;ℂ), group inverse = matrix inverse. -/
private theorem group_inv_eq_matrix_inv (Λ : ComplexLorentzGroup d) :
    Λ⁻¹.val = Λ.val⁻¹ := by
  symm
  exact Matrix.inv_eq_left_inv (group_inv_mul_val Λ)

/-- Conjugation preserves inverses (group homomorphism property). -/
theorem conjLG_inv (Λ : ComplexLorentzGroup d) :
    conjLG Λ⁻¹ = (conjLG Λ)⁻¹ := by
  have h : conjLG Λ * conjLG Λ⁻¹ = 1 := by
    rw [← conjLG_mul, mul_inv_cancel, conjLG_one]
  exact eq_comm.mpr (inv_eq_of_mul_eq_one_right h)

/-- Conjugation sends exp(itY) to exp(-itY) for real Y ∈ so(1,d;ℝ). -/
theorem conjLG_realAlgPath (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) (t : ℝ) :
    conjLG (realAlgPath Y hY t) = (realAlgPath Y hY t)⁻¹ := by
  -- Suffices to show conjLG(B) * B = 1, then conjLG(B) = B⁻¹
  suffices h : conjLG (realAlgPath Y hY t) * realAlgPath Y hY t = 1 by
    exact mul_eq_one_iff_eq_inv.mp h
  apply ComplexLorentzGroup.ext
  -- Goal: (conjLG B * B).val = 1, i.e., conjMap(B.val) * B.val = 1
  show conjMap (realAlgPath Y hY t).val * (realAlgPath Y hY t).val = 1
  -- Unfold: B.val = exp((↑t:ℂ) • (I • Y.map ofReal))
  set X := (↑t : ℂ) • (Complex.I • Y.map Complex.ofReal) with hX_def
  -- conjMap(exp X) = exp(conjMap X)
  rw [show (realAlgPath Y hY t).val = NormedSpace.exp X from rfl]
  rw [conjMap_exp]
  -- conjMap X = -X since conj(t*I*Y) = t*(-I)*Y = -t*I*Y = -X
  rw [show conjMap X = -X from by
    rw [hX_def]; ext i j
    simp [Matrix.map_apply, smul_eq_mul, Matrix.neg_apply,
      Complex.conj_ofReal, Complex.conj_I]]
  -- exp(-X) * exp(X) = 1
  rw [Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp X))

/-- Shorthand: conjLG at t=1. -/
theorem conjLG_realAlgPath_one (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) :
    conjLG (realAlgPath Y hY 1) = (realAlgPath Y hY 1)⁻¹ :=
  conjLG_realAlgPath Y hY 1

/-! ### Geodesic convexity of the forward cone -/

/-- **Geodesic convexity of the forward light cone.**

    If w ∈ ℂ^{d+1} has Im(w) ∈ V₊, and for Y ∈ so(1,d;ℝ),
    Im(exp(iY)·w) ∈ V₊, then Im(exp(itY)·w) ∈ V₊ for all t ∈ [0,1].

    The proof uses the ODE d²η/dt² = -Y²η satisfied by η(t) = Im(exp(itY)·w),
    combined with block diagonalization, sinh convexity, and sine positivity.

    Ref: Streater-Wightman, Lemma 2-2; Bros-Epstein-Glaser (1967). -/
theorem geodesic_convexity_forwardCone
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y)
    (w : Fin (d + 1) → ℂ)
    (hw : InOpenForwardCone d (fun μ => (w μ).im))
    (hexp : InOpenForwardCone d (fun μ =>
      (∑ ν, (realAlgPath Y hY 1).val μ ν * w ν).im)) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      InOpenForwardCone d (fun μ =>
        (∑ ν, (realAlgPath Y hY t).val μ ν * w ν).im) := by
  -- Define the imaginary part path η(t) = Im(exp(itY)·w)
  set η : ℝ → Fin (d + 1) → ℝ :=
    fun t μ => (∑ ν, (realAlgPath Y hY t).val μ ν * w ν).im with η_def
  -- The set S = {t ∈ [0,1] | η(t) ∈ V₊} is what we want to show equals [0,1]
  -- Strategy: S is open in [0,1] (by continuity + V₊ open) and non-empty (contains 0 and 1).
  -- We show S is also closed in [0,1], hence S = [0,1] by connectedness.

  -- Step 1: η is continuous
  have η_continuous : Continuous η := by
    apply continuous_pi; intro μ
    -- Im(∑ ν, (realAlgPath Y hY t).val μ ν * w ν) is continuous in t
    apply Complex.continuous_im.comp
    apply continuous_finset_sum; intro ν _
    -- t ↦ (realAlgPath Y hY t).val μ ν is continuous
    have hentry : Continuous (fun t => (realAlgPath Y hY t).val μ ν) :=
      (ComplexLorentzGroup.continuous_entry μ ν).comp (realAlgPath_continuous Y hY)
    exact hentry.mul continuous_const

  -- Step 2: η(0) = Im(w) ∈ V₊
  have η_zero : η 0 = fun μ => (w μ).im := by
    ext μ; simp only [η_def, realAlgPath_zero]
    simp [ComplexLorentzGroup.one_val', Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ]

  -- Step 3: η(1) ∈ V₊
  have η_one : InOpenForwardCone d (η 1) := by
    show InOpenForwardCone d (fun μ => (∑ ν, (realAlgPath Y hY 1).val μ ν * w ν).im)
    exact hexp

  -- Step 4: η(0) ∈ V₊
  have η_zero_cone : InOpenForwardCone d (η 0) := by rw [η_zero]; exact hw

  -- Step 5: The set S = η⁻¹(V₊) ∩ [0,1] is open in [0,1]
  -- since V₊ is open (as a set in ℝ^{d+1}) and η is continuous
  have hV_open : IsOpen {v : Fin (d + 1) → ℝ | InOpenForwardCone d v} := by
    -- V₊ = {v | v 0 > 0} ∩ {v | ∑ μ, η_μ * v_μ² < 0}
    -- Both sets are open (preimages of open sets under continuous functions)
    have h1 : IsOpen {v : Fin (d + 1) → ℝ | v 0 > 0} :=
      isOpen_lt continuous_const (continuous_apply 0)
    have h2 : IsOpen {v : Fin (d + 1) → ℝ | ∑ μ, minkowskiSignature d μ * v μ ^ 2 < 0} := by
      apply isOpen_lt
      · exact continuous_finset_sum _ (fun μ _ =>
          (continuous_const.mul ((continuous_apply μ).pow 2)))
      · exact continuous_const
    exact h1.inter h2

  -- The key mathematical step: geodesic convexity.
  -- {t ∈ [0,1] | η(t) ∈ V₊} is open (proved above) AND closed in [0,1].
  -- The closedness uses the fact that η(t) cannot cross the light cone boundary
  -- because the Lorentz group preserves the causal structure.
  --
  -- Proof idea for closedness: Consider the Minkowski norm Q(η(t)) along the path.
  -- Since exp(itY) ∈ SO⁺(1,d;ℂ), the complex Lorentz transformation preserves
  -- the quadratic form on the full complex vector, which constrains the imaginary part.
  -- Combined with η₀(t) > 0 at endpoints, the intermediate value theorem
  -- and the constraint from the quadratic form prevent η(t) from leaving V₊.
  --
  -- The full proof requires analyzing the ODE η''(t) = -Y²η(t) and showing
  -- that the solutions (combinations of sinh, cosh, sin, cos) preserve the cone.
  -- This is the content of Streater-Wightman Lemma 2-2.
  sorry

/-! ### Polar decomposition (Cartan decomposition of symmetric space) -/

/-- The Cartan element H = conj(Λ)⁻¹ · Λ in the symmetric part of SO⁺(1,d;ℂ). -/
private def cartanElement (Λ : ComplexLorentzGroup d) : ComplexLorentzGroup d :=
  (conjLG Λ)⁻¹ * Λ

/-- The Cartan element satisfies the anti-involution property conj(H) = H⁻¹.
    This is the defining property of the symmetric part P = {g : θ(g) = g⁻¹}
    of the Cartan decomposition. -/
private theorem cartanElement_anti_involution (Λ : ComplexLorentzGroup d) :
    conjLG (cartanElement Λ) = (cartanElement Λ)⁻¹ := by
  unfold cartanElement
  rw [conjLG_mul, conjLG_inv, conjLG_involutive, _root_.mul_inv_rev, inv_inv]

/-- **Cartan symmetric space exponential embedding.**

    Every H ∈ SO⁺(1,d;ℂ) satisfying the anti-involution conjLG(H) = H⁻¹ lies
    in the image of the exponential map from the imaginary Lie algebra:
    H = exp(iY) for some Y ∈ so(1,d;ℝ).

    This is the surjectivity of exp : ip → P where p = so(1,d;ℝ) and
    P = {H ∈ SO⁺(1,d;ℂ) : conjLG(H) = H⁻¹} is the symmetric part.
    For Riemannian symmetric spaces of noncompact type, exp : p → P is a
    diffeomorphism (Helgason, Ch. VI, Thm 1.1).

    The proof requires: the matrix logarithm for "positive" elements of the
    symmetric space, and the fact that the real Lie algebra so(1,d;ℝ) maps
    surjectively onto P via Y ↦ exp(iY). -/
private theorem cartan_exp_embedding (H : ComplexLorentzGroup d)
    (h_anti : conjLG H = H⁻¹) :
    ∃ (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hY : IsInLorentzAlgebra d Y),
      H = realAlgPath Y hY 1 := by
  -- Proof strategy (Helgason, Ch. VI, Thm 1.1):
  -- The anti-involution condition conj(H) = H⁻¹ means H̄·H = I.
  -- Combined with the Lorentz condition Hᵀ·η·H = η, the matrix
  -- A = η·H̄ᵀ·η·H = η·(H⁻¹)ᵀ·η·H is "positive" in a suitable sense.
  --
  -- Step 1: Take X = log(H) using the matrix logarithm.
  --   For this, we need H to be in a neighborhood of the identity where
  --   log is defined, or we use the global surjectivity of exp on the
  --   symmetric space P = {g : θ(g) = g⁻¹}.
  --
  -- Step 2: Show X = iY for real Y.
  --   From conj(H) = H⁻¹, we get conj(exp(X)) = exp(conj(X)) = exp(-X),
  --   hence conj(X) = -X (at least locally). Writing X = A + iB with A, B real,
  --   this gives A - iB = -A - iB, so A = 0, i.e., X = iB.
  --
  -- Step 3: Show Y = B ∈ so(1,d;ℝ).
  --   From H ∈ SO⁺(1,d;ℂ) and H = exp(iY), the Lie algebra condition
  --   follows from d/dt|_{t=0} exp(itY) ∈ SO⁺(1,d;ℂ).
  --
  -- Infrastructure needed:
  -- (a) Matrix logarithm (not in Mathlib): log : GL_n(ℂ) → M_n(ℂ)
  --     satisfying exp(log(A)) = A for A near I.
  -- (b) Global surjectivity of exp on symmetric spaces of noncompact type.
  -- (c) Injectivity of exp (to conclude conj(X) = -X from conj(exp(X)) = exp(-X)).
  sorry

/-- **Polar decomposition for the complex Lorentz group.**

    Every Λ ∈ SO⁺(1,d;ℂ) can be written as R · exp(iY) where
    R ∈ SO↑₊(1,d;ℝ) and Y ∈ so(1,d;ℝ).

    Proof outline: The Cartan element H = conj(Λ)⁻¹ · Λ satisfies
    conj(H) = H⁻¹ (proved in `cartanElement_anti_involution`).
    By `cartan_exp_embedding`, H = exp(iY₀) for some Y₀ ∈ so(1,d;ℝ).
    Setting Y = Y₀/2 and P = exp(iY), we get P² = H, and
    R = Λ · P⁻¹ satisfies conj(R) = R (i.e., R is real).
    R is in the restricted Lorentz group by the connectivity argument:
    R = Λ · exp(-iY) is connected to I in SO⁺(1,d;ℂ), hence orthochronous.

    Ref: Helgason, Differential Geometry, Lie Groups and Symmetric Spaces, Ch. VI. -/
theorem polar_decomposition (Λ : ComplexLorentzGroup d) :
    ∃ (R : RestrictedLorentzGroup d)
      (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (_ : IsInLorentzAlgebra d Y),
      Λ = ComplexLorentzGroup.ofReal R * realAlgPath Y ‹_› 1 := by
  -- Step 1: The Cartan element satisfies the anti-involution
  have h_anti := cartanElement_anti_involution Λ
  -- Step 2: Get Y₀ from the Cartan embedding
  obtain ⟨Y₀, hY₀, hH⟩ := cartan_exp_embedding (cartanElement Λ) h_anti
  -- Step 3: Set Y = (1/2) • Y₀
  set Y := (1 / 2 : ℝ) • Y₀ with Y_def
  have hY : IsInLorentzAlgebra d Y := isInLorentzAlgebra_smul d hY₀ (1 / 2)
  -- Step 4: P = realAlgPath Y hY 1 = realAlgPath Y₀ hY₀ (1/2) and P² = H
  have hP_eq : realAlgPath Y hY 1 = realAlgPath Y₀ hY₀ (1 / 2) :=
    realAlgPath_smul_eq Y₀ hY₀ (1 / 2)
  -- P² = realAlgPath Y₀ hY₀ (1/2) * realAlgPath Y₀ hY₀ (1/2) = realAlgPath Y₀ hY₀ 1
  have hP_sq : realAlgPath Y hY 1 * realAlgPath Y hY 1 = realAlgPath Y₀ hY₀ 1 := by
    rw [hP_eq, realAlgPath_mul Y₀ hY₀ (1/2) (1/2)]
    norm_num
  -- So P² = H = cartanElement Λ = conj(Λ)⁻¹ * Λ
  have hP_sq_H : realAlgPath Y hY 1 * realAlgPath Y hY 1 = cartanElement Λ := by
    rw [hP_sq, hH]
  -- Step 5: Define R_CLG = Λ * P⁻¹
  set P := realAlgPath Y hY 1 with P_def
  set R_CLG := Λ * P⁻¹ with R_CLG_def
  -- Step 6: Show conj(R_CLG) = R_CLG
  have hconj_R : conjLG R_CLG = R_CLG := by
    rw [R_CLG_def, conjLG_mul, conjLG_inv]
    -- conj(P) = P⁻¹ by conjLG_realAlgPath
    rw [conjLG_realAlgPath Y hY 1]
    -- So conj(P)⁻¹ = (P⁻¹)⁻¹ = P
    rw [inv_inv]
    -- Need: conj(Λ) * P = Λ * P⁻¹
    -- i.e., conj(Λ) = Λ * P⁻¹ * P⁻¹ = Λ * (P * P)⁻¹ = Λ * H⁻¹
    -- H = conj(Λ)⁻¹ * Λ, so Λ * H⁻¹ = Λ * Λ⁻¹ * conj(Λ) = conj(Λ)
    suffices h : conjLG Λ * P = Λ * P⁻¹ by exact h
    -- From P² = H = conj(Λ)⁻¹ * Λ, we get conj(Λ) = Λ * P⁻²
    -- conj(Λ) * P = Λ * P⁻² * P = Λ * P⁻¹
    have h_conjΛ_eq : conjLG Λ = Λ * (P * P)⁻¹ := by
      -- P * P = cartanElement Λ = conj(Λ)⁻¹ * Λ
      have : (P * P)⁻¹ = (cartanElement Λ)⁻¹ := by rw [hP_sq_H]
      rw [this]
      -- Λ * (conj(Λ)⁻¹ * Λ)⁻¹ = Λ * Λ⁻¹ * conj(Λ) = conj(Λ)
      rw [show (cartanElement Λ)⁻¹ = Λ⁻¹ * conjLG Λ from by
        unfold cartanElement
        rw [_root_.mul_inv_rev, inv_inv]]
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    calc conjLG Λ * P
        = Λ * (P * P)⁻¹ * P := by rw [h_conjΛ_eq]
      _ = Λ * ((P * P)⁻¹ * P) := by rw [mul_assoc]
      _ = Λ * (P⁻¹ * P⁻¹ * P) := by rw [_root_.mul_inv_rev]
      _ = Λ * (P⁻¹ * (P⁻¹ * P)) := by rw [mul_assoc]
      _ = Λ * (P⁻¹ * 1) := by rw [inv_mul_cancel]
      _ = Λ * P⁻¹ := by rw [mul_one]
  -- Step 7: Extract real matrix from R_CLG
  -- Since conj(R_CLG) = R_CLG, entries are real: R_CLG.val i j = star(R_CLG.val i j)
  have hreal : ∀ i j, (R_CLG.val i j).im = 0 := by
    intro i j
    have h := congr_fun (congr_fun (congr_arg ComplexLorentzGroup.val hconj_R) i) j
    simp only [conjLG_val, Matrix.map_apply] at h
    -- h : star (R_CLG.val i j) = R_CLG.val i j
    rw [Complex.ext_iff] at h
    simp [Complex.conj_re, Complex.conj_im] at h
    linarith
  -- Define the real matrix
  set M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := fun i j => (R_CLG.val i j).re
  -- M.map ofReal = R_CLG.val
  have hM_lift : M.map Complex.ofReal = R_CLG.val := by
    ext i j
    simp only [Matrix.map_apply, M]
    exact Complex.ext (Complex.ofReal_re _) (by simp [hreal i j])
  -- M is a Lorentz matrix (preserves metric): Mᵀ * η * M = η
  have hM_lorentz : IsLorentzMatrix d M := by
    -- R_CLG satisfies: R_CLG.valᵀ * ηℂ * R_CLG.val = ηℂ (over ℂ)
    have hR_met := ComplexLorentzGroup.metric_preserving_matrix R_CLG
    -- Rewrite in terms of M.map ofReal
    rw [← hM_lift] at hR_met
    -- Need: Mᵀ * η * M = η (over ℝ)
    -- Lift via ofRealHom.mapMatrix which is injective
    show M.transpose * minkowskiMatrix d * M = minkowskiMatrix d
    -- Show the ℂ-version: (M.map ofReal)ᵀ * ηℂ * (M.map ofReal) = ηℂ is exactly hR_met
    -- And (M.map ofReal)ᵀ = Mᵀ.map ofReal, ηℂ = (η).map ofReal (as diagonal)
    -- So hR_met says: ofRealHom.mapMatrix(Mᵀ * η * M) = ofRealHom.mapMatrix(η)
    suffices h : (M.transpose * minkowskiMatrix d * M).map Complex.ofReal =
        (minkowskiMatrix d).map Complex.ofReal by
      have hinj : Function.Injective (Matrix.map · Complex.ofReal :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
        intro A B hab; ext i j
        have := congr_fun (congr_fun hab i) j
        simp [Matrix.map_apply] at this; exact this
      exact hinj h
    -- η as complex: (minkowskiMatrix d).map ofReal = ηℂ
    have h_eta : (minkowskiMatrix d).map Complex.ofReal = ηℂ := by
      ext i j; simp [Matrix.map_apply, ηℂ, minkowskiMatrix, Matrix.diagonal_apply]
      split_ifs <;> simp
    -- The map M ↦ M.map ofReal preserves mul and transpose
    -- So (Mᵀ η M).map ofReal = (M.map ofReal)ᵀ * (η.map ofReal) * (M.map ofReal) = ... = ηℂ
    -- This equals (η).map ofReal, so by injectivity, Mᵀ η M = η
    have h_lhs : (M.transpose * minkowskiMatrix d * M).map Complex.ofReal =
        (M.map Complex.ofReal).transpose * ηℂ * (M.map Complex.ofReal) := by
      rw [← h_eta]
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply]
      push_cast; ring
    rw [h_lhs, hR_met, h_eta]
  -- M has det 1
  have hM_det : M.det = 1 := by
    have h1 : (M.det : ℂ) = R_CLG.val.det := by
      have hmap : Complex.ofRealHom.mapMatrix M = M.map Complex.ofReal := by
        ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply]
      have := RingHom.map_det Complex.ofRealHom M  -- ofRealHom(det M) = det(mapMatrix M)
      rw [hmap, hM_lift] at this; exact this
    rw [R_CLG.proper] at h1
    exact_mod_cast h1
  -- M is orthochronous: M 0 0 ≥ 1
  -- R_CLG = Λ * P⁻¹ is in the connected component of 1 in SO⁺(1,d;ℂ).
  -- Since both Λ and P are in the connected group SO⁺(1,d;ℂ), so is R_CLG.
  -- For a real Lorentz matrix in the identity component, (0,0) entry ≥ 1.
  have hM_orth : M 0 0 ≥ 1 := by
    -- From the Cartan decomposition G = K · exp(p), the K-factor lies in the
    -- maximal compact subgroup K = SO(d) (spatial rotations), which satisfies
    -- R 0 0 = 1 (the rotation doesn't affect the time component).
    -- In general, the Cartan polar factor R = Λ · exp(-iY) satisfies
    -- conj(R) = R and R ∈ SO⁺(1,d;ℂ), making it a real proper Lorentz matrix.
    -- The orthochronous condition M 0 0 ≥ 1 follows from:
    -- (a) M 0 0 ^ 2 ≥ 1 (from IsLorentzMatrix.entry00_sq_ge_one)
    -- (b) The Cartan decomposition lands in K = SO(d) ⊂ SO⁺(1,d;ℝ), and
    --     every element of SO(d) (spatial rotation) has (0,0) entry = 1.
    -- Proving (b) formally requires the symmetric space structure theorem
    -- (Helgason Ch. VI): exp : p → P is a diffeomorphism, and the K-factor
    -- of Λ = K · exp(X) is uniquely determined by K = Λ · exp(-X) ∈ K_max.
    sorry
  -- Package as RestrictedLorentzGroup
  refine ⟨⟨⟨M, hM_lorentz⟩, hM_det, hM_orth⟩, Y, hY, ?_⟩
  -- Show Λ = ofReal R * P, i.e., Λ = R_CLG * P (since ofReal R = R_CLG as complex matrices)
  apply ComplexLorentzGroup.ext
  show Λ.val = (ComplexLorentzGroup.ofReal ⟨⟨M, hM_lorentz⟩, hM_det, hM_orth⟩).val *
    (realAlgPath Y hY 1).val
  -- ofReal R has matrix M.map ofReal = R_CLG.val
  have h_ofReal_val : (ComplexLorentzGroup.ofReal
      ⟨⟨M, hM_lorentz⟩, hM_det, hM_orth⟩).val = R_CLG.val := by
    ext i j
    simp only [ComplexLorentzGroup.ofReal, M]
    exact Complex.ext (Complex.ofReal_re _) (by simp [hreal i j])
  rw [h_ofReal_val]
  -- Λ = R_CLG * P means Λ.val = R_CLG.val * P.val
  -- R_CLG = Λ * P⁻¹, so R_CLG * P = Λ * P⁻¹ * P = Λ
  have : R_CLG * P = Λ := by
    rw [R_CLG_def, mul_assoc, inv_mul_cancel, mul_one]
  exact (congr_arg ComplexLorentzGroup.val this).symm

end BHW

end
