/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.Connectedness

/-!
# Difference Coordinates for the Forward Tube

This file defines the **difference-coordinate map** `L` that transforms the forward tube
from "absolute coordinates" `z₀, z₁, ..., z_{n-1}` to "difference coordinates"
`ξ₀ = z₀, ξₖ = zₖ - z_{k-1}` for `k > 0`.

In difference coordinates, the forward tube becomes a **product tube domain**:
each `ξₖ` independently satisfies `Im(ξₖ) ∈ V₊` (the open forward light cone).

## Main definitions

* `BHW.diffCoordFun` — the difference-coordinate function `L : z ↦ ξ`
* `BHW.partialSumFun` — the inverse (partial-sum) function `L⁻¹ : ξ ↦ z`
* `BHW.diffCoordEquiv` — the continuous linear equivalence `L`
* `BHW.ProductForwardCone` — the product tube domain `{w | ∀ k, Im(w k) ∈ V₊}`

## Main results

* `BHW.forwardTube_eq_diffCoord_preimage` — `ForwardTube d n = L⁻¹(ProductForwardCone d n)`

## References

* Streater & Wightman, *PCT, Spin and Statistics*, §2.4
* Jost (1965), *The General Theory of Quantized Fields*, Ch. IV
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter Finset

variable {d : ℕ}

namespace BHW

/-! ### Difference-coordinate functions -/

/-- The difference-coordinate function `L`:
    - `L(z)(0) = z(0)` (base point)
    - `L(z)(k) = z(k) - z(k-1)` for `k > 0` (successive differences) -/
def diffCoordFun (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    if h : k.val = 0 then z k μ
    else z k μ - z ⟨k.val - 1, by omega⟩ μ

/-- The partial-sum function `L⁻¹`:
    - `L⁻¹(ξ)(k) = ∑_{j=0}^{k} ξ(j)` -/
def partialSumFun (n d : ℕ) (ξ : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ => ∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ μ

/-! ### Telescoping lemmas -/

/-- Key telescoping: the partial sum of differences equals the original value. -/
private lemma partialSum_diffCoord_val (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ)
    (m : ℕ) (hm : m < n) (μ : Fin (d + 1)) :
    (∑ j : Fin (m + 1), diffCoordFun n d z ⟨j.val, by omega⟩ μ) = z ⟨m, hm⟩ μ := by
  induction m with
  | zero =>
    simp [diffCoordFun]
  | succ m ih =>
    -- Split: ∑_{j=0}^{m+1} f(j) = ∑_{j=0}^{m} f(castSucc j) + f(last)
    rw [Fin.sum_univ_castSucc]
    -- Convert (castSucc j).val to j.val so ih matches, then apply ih
    simp_rw [Fin.val_castSucc]
    rw [ih (by omega)]
    -- Goal: z ⟨m, _⟩ μ + diffCoordFun n d z ⟨(Fin.last (m+1)).val, _⟩ μ = z ⟨m+1, hm⟩ μ
    simp only [Fin.val_last, diffCoordFun, show ¬(m + 1 = 0) from Nat.succ_ne_zero m, ↓reduceDIte]
    have : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ :=
      Fin.ext (show m + 1 - 1 = m by omega)
    rw [this]; ring

/-- `L⁻¹ ∘ L = id`: partial sums of differences recover the original. -/
theorem partialSum_diffCoord (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ) :
    partialSumFun n d (diffCoordFun n d z) = z := by
  funext k μ
  exact partialSum_diffCoord_val n d z k.val k.isLt μ

/-! ### Linear maps -/

/-- The difference-coordinate map as a linear map. -/
def diffCoordLM (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin n → Fin (d + 1) → ℂ) where
  toFun := diffCoordFun n d
  map_add' z₁ z₂ := by
    funext k μ
    simp only [diffCoordFun, Pi.add_apply]
    by_cases hk : k.val = 0 <;> simp [hk, sub_add_sub_comm]
  map_smul' c z := by
    funext k μ
    simp only [diffCoordFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    by_cases hk : k.val = 0 <;> simp [hk, mul_sub]

/-- The partial-sum map as a linear map. -/
def partialSumLM (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin n → Fin (d + 1) → ℂ) where
  toFun := partialSumFun n d
  map_add' ξ₁ ξ₂ := by
    funext k μ
    simp only [partialSumFun, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
  map_smul' c ξ := by
    funext k μ
    simp only [partialSumFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]

/-- `L ∘ L⁻¹ = id`: differences of partial sums recover the original.
    Proved by finite-dimensional linear algebra: since L⁻¹∘L = id, L is injective.
    On finite-dimensional spaces, injective linear maps are surjective.
    Therefore L⁻¹ is also a right inverse. -/
theorem diffCoord_partialSum (n d : ℕ) (ξ : Fin n → Fin (d + 1) → ℂ) :
    diffCoordFun n d (partialSumFun n d ξ) = ξ := by
  -- L⁻¹ ∘ L = id gives injectivity of L
  have h_left_inv : ∀ z, partialSumFun n d (diffCoordFun n d z) = z :=
    partialSum_diffCoord n d
  have h_inj : Function.Injective (diffCoordLM n d) := by
    intro a b h
    have : diffCoordFun n d a = diffCoordFun n d b := h
    calc a = partialSumFun n d (diffCoordFun n d a) := (h_left_inv a).symm
      _ = partialSumFun n d (diffCoordFun n d b) := congr_arg _ this
      _ = b := h_left_inv b
  -- Injective ↔ surjective for linear endomorphisms on finite-dimensional spaces
  have h_surj : Function.Surjective (diffCoordLM n d) :=
    LinearMap.injective_iff_surjective.mp h_inj
  -- For any ξ, find z with L(z) = ξ, then L(L⁻¹(ξ)) = L(L⁻¹(L(z))) = L(z) = ξ
  obtain ⟨z, rfl⟩ := h_surj ξ
  exact congr_arg (diffCoordFun n d) (h_left_inv z)

/-! ### Linear equivalence -/

/-- The difference-coordinate linear equivalence. -/
def diffCoordLinearEquiv (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin n → Fin (d + 1) → ℂ) where
  toLinearMap := diffCoordLM n d
  invFun := partialSumFun n d
  left_inv z := partialSum_diffCoord n d z
  right_inv ξ := diffCoord_partialSum n d ξ

/-- The difference-coordinate continuous linear equivalence. -/
def diffCoordEquiv (n d : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ] (Fin n → Fin (d + 1) → ℂ) :=
  (diffCoordLinearEquiv n d).toContinuousLinearEquiv

theorem diffCoordEquiv_apply (n d : ℕ) (z : Fin n → Fin (d + 1) → ℂ)
    (k : Fin n) (μ : Fin (d + 1)) :
    diffCoordEquiv n d z k μ =
      if _h : k.val = 0 then z k μ
      else z k μ - z ⟨k.val - 1, by omega⟩ μ := by
  show diffCoordFun n d z k μ = _
  simp [diffCoordFun]

theorem diffCoordEquiv_symm_apply (n d : ℕ) (ξ : Fin n → Fin (d + 1) → ℂ)
    (k : Fin n) (μ : Fin (d + 1)) :
    (diffCoordEquiv n d).symm ξ k μ =
      ∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ μ := rfl

/-! ### Product forward cone -/

/-- The product forward cone: the set of `ξ` where `Im(ξ k) ∈ V₊` for all `k`.
    In difference coordinates, the forward tube becomes exactly this product set. -/
def ProductForwardCone (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  { ξ | ∀ k : Fin n, InOpenForwardCone d (fun μ => (ξ k μ).im) }

/-! ### Forward tube = preimage of product forward cone under L -/

/-- The forward tube condition at index k is equivalent to the InOpenForwardCone
    condition on the k-th difference coordinate. -/
private lemma forwardTube_cond_iff_diffCoord (n d : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) :
    InOpenForwardCone d
      (fun μ => (z k μ - (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) μ).im) ↔
    InOpenForwardCone d (fun μ => (diffCoordFun n d z k μ).im) := by
  suffices heq : (fun μ => (z k μ -
      (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) μ).im) =
      (fun μ => (diffCoordFun n d z k μ).im) by rw [heq]
  funext μ; simp only [diffCoordFun]
  by_cases hk : k.val = 0 <;> simp [hk]

/-- The forward tube equals the preimage of the product forward cone under the
    difference-coordinate map. -/
theorem forwardTube_eq_diffCoord_preimage (n d : ℕ) [NeZero d] :
    ForwardTube d n = diffCoordEquiv n d ⁻¹' ProductForwardCone d n := by
  ext z
  simp only [Set.mem_preimage, ProductForwardCone, Set.mem_setOf_eq,
    ForwardTube, Set.mem_setOf_eq]
  exact ⟨fun hz k => (forwardTube_cond_iff_diffCoord n d z k).mp (hz k),
         fun hξ k => (forwardTube_cond_iff_diffCoord n d z k).mpr (hξ k)⟩

/-- The image of the forward tube under the difference-coordinate map is
    exactly the product forward cone. -/
theorem diffCoordEquiv_image_forwardTube (n d : ℕ) [NeZero d] :
    diffCoordEquiv n d '' ForwardTube d n = ProductForwardCone d n := by
  rw [forwardTube_eq_diffCoord_preimage]
  exact (diffCoordEquiv n d).toEquiv.image_preimage _

/-- The open forward cone is an open set. -/
private theorem isOpen_inOpenForwardCone :
    IsOpen {η : Fin (d + 1) → ℝ | InOpenForwardCone d η} :=
  IsOpen.inter
    (isOpen_lt continuous_const (continuous_apply 0))
    (isOpen_lt (continuous_finset_sum _ (fun μ _ =>
      (continuous_const.mul ((continuous_apply μ).pow 2)))) continuous_const)

/-- The product forward cone is open. -/
theorem isOpen_productForwardCone (n d : ℕ) [NeZero d] :
    IsOpen (ProductForwardCone d n) := by
  suffices h : ProductForwardCone d n =
      ⋂ k : Fin n, {ξ : Fin n → Fin (d + 1) → ℂ |
        InOpenForwardCone d (fun μ => (ξ k μ).im)} by
    rw [h]
    apply isOpen_iInter_of_finite
    intro k
    have : {ξ : Fin n → Fin (d + 1) → ℂ | InOpenForwardCone d (fun μ => (ξ k μ).im)} =
        (fun ξ => fun μ => (ξ k μ).im) ⁻¹' {η | InOpenForwardCone d η} := rfl
    rw [this]
    exact isOpen_inOpenForwardCone.preimage
      (continuous_pi (fun μ =>
        Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply k))))
  ext ξ; simp [ProductForwardCone, Set.mem_iInter]

/-! ### Swap action in difference coordinates -/

/-- In difference coordinates, swapping indices i and i+1 causes
    the (i+1)-th difference coordinate to flip sign.

    This is crucial because the sign flip creates the EOW setup:
    forward tube has Im(ξ_{i+1}) ∈ V₊, while the swapped tube has Im(-ξ_{i+1}) ∈ -V₊. -/
theorem diffCoord_swap_sign_flip (n d : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin (d + 1) → ℂ) (μ : Fin (d + 1)) :
    let σ := Equiv.swap i ⟨i.val + 1, hi⟩
    diffCoordFun n d (fun k => z (σ k)) ⟨i.val + 1, hi⟩ μ =
      -(diffCoordFun n d z ⟨i.val + 1, hi⟩ μ) := by
  simp only [diffCoordFun]
  have hk_ne : ¬ ((i.val + 1) = 0) := Nat.succ_ne_zero _
  simp only [hk_ne, ↓reduceDIte]
  have hpred : (⟨i.val + 1 - 1, by omega⟩ : Fin n) = i := by ext; simp
  rw [hpred, Equiv.swap_apply_right, Equiv.swap_apply_left]
  ring

/-- Coordinates far from the swap are unchanged in difference coordinates. -/
theorem diffCoord_swap_far_unchanged (n d : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin (d + 1) → ℂ) (k : Fin n) (μ : Fin (d + 1))
    (hk_ne_i : k ≠ i) (hk_ne_ip1 : k ≠ ⟨i.val + 1, hi⟩)
    (hkm1_ne_i : k.val ≠ 0 → (⟨k.val - 1, by omega⟩ : Fin n) ≠ i)
    (hkm1_ne_ip1 : k.val ≠ 0 → (⟨k.val - 1, by omega⟩ : Fin n) ≠ ⟨i.val + 1, hi⟩) :
    let σ := Equiv.swap i ⟨i.val + 1, hi⟩
    diffCoordFun n d (fun k => z (σ k)) k μ = diffCoordFun n d z k μ := by
  simp only [diffCoordFun]
  by_cases hk0 : k.val = 0
  · simp only [hk0, ↓reduceDIte]
    congr 1
    exact Equiv.swap_apply_of_ne_of_ne hk_ne_i hk_ne_ip1
  · simp only [hk0, ↓reduceDIte]
    rw [Equiv.swap_apply_of_ne_of_ne hk_ne_i hk_ne_ip1,
        Equiv.swap_apply_of_ne_of_ne (hkm1_ne_i hk0) (hkm1_ne_ip1 hk0)]

end BHW

end
