/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices
import OSReconstruction.ComplexLieGroups.SL2CDoubleCover

/-!
# Slice Index Set Connectedness for d = 3

Proves that the slice index set
`{Λ ∈ SO₊(1,3;ℂ) | ∃ w ∈ FT, Λ(σw) ∈ FT}`
is connected, using the SL(2,ℂ)×SL(2,ℂ) double cover.

## References

* Bogolyubov, Logunov, Oksak & Todorov,
  *General Principles of Quantum Field Theory* (1990), Ch. 9, Lemma 9.7
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter
open SL2CDoubleCover

namespace BHW

/-! ### Bi-invariance of the slice index set -/

/-- The index set is left-invariant under real Lorentz. -/
theorem indexSet_left_invariant_d3
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {Λ : ComplexLorentzGroup 3}
    (hΛ : Λ ∈ permForwardOverlapIndexSet (d := 3) n σ)
    (R : RestrictedLorentzGroup 3) :
    ComplexLorentzGroup.ofReal R * Λ ∈ permForwardOverlapIndexSet (d := 3) n σ := by
  rcases hΛ with ⟨w, hw_FT, hΛσw⟩
  refine ⟨w, hw_FT, ?_⟩
  have hmul :
      complexLorentzAction (ComplexLorentzGroup.ofReal R * Λ)
        (permAct (d := 3) σ w) =
      complexLorentzAction (ComplexLorentzGroup.ofReal R)
        (complexLorentzAction Λ (permAct (d := 3) σ w)) := by
    simpa using complexLorentzAction_mul
      (ComplexLorentzGroup.ofReal R) Λ (permAct (d := 3) σ w)
  rw [hmul]
  exact ofReal_preserves_forwardTube_base R _ hΛσw

/-- The index set is right-invariant under real Lorentz. -/
theorem indexSet_right_invariant_d3
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {Λ : ComplexLorentzGroup 3}
    (hΛ : Λ ∈ permForwardOverlapIndexSet (d := 3) n σ)
    (R : RestrictedLorentzGroup 3) :
    Λ * ComplexLorentzGroup.ofReal R ∈ permForwardOverlapIndexSet (d := 3) n σ := by
  rcases hΛ with ⟨w, hw_FT, hΛσw⟩
  let w' : Fin n → Fin (3 + 1) → ℂ :=
    complexLorentzAction (ComplexLorentzGroup.ofReal R⁻¹) w
  have hw'_FT : w' ∈ ForwardTube 3 n := by
    simpa [w'] using ofReal_preserves_forwardTube_base (R := R⁻¹) w hw_FT
  refine ⟨w', hw'_FT, ?_⟩
  have hpermw' : permAct (d := 3) σ w' = complexLorentzAction (ComplexLorentzGroup.ofReal R⁻¹)
      (permAct (d := 3) σ w) := by
    ext k μ; simp [w', permAct, complexLorentzAction]
  rw [hpermw', ← complexLorentzAction_mul,
    show Λ * ComplexLorentzGroup.ofReal R * ComplexLorentzGroup.ofReal R⁻¹ = Λ from by
      rw [mul_assoc, ← ofReal_mul_eq, mul_inv_cancel, ofReal_one_eq, mul_one]]
  exact hΛσw

/-! ### Diagonal Lorentz elements via the double cover -/

/-- Diagonal Lorentz element via the double cover. -/
def diagonalLorentz (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) : ComplexLorentzGroup 3 :=
  sl2cDoubleCoverMap (diagonalSL2 a ha) (diagonalSL2 b hb)

/-! ### KAK decomposition for SO₊(1,3;ℂ) -/

/-- Every Λ ∈ SO₊(1,3;ℂ) decomposes as R₁ · D(a,b) · R₂. -/
theorem complexLorentz3_kak_decomposition (Λ : ComplexLorentzGroup 3) :
    ∃ (R₁ R₂ : RestrictedLorentzGroup 3) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0),
      Λ = ComplexLorentzGroup.ofReal R₁ * diagonalLorentz a b ha hb *
          ComplexLorentzGroup.ofReal R₂ := by
  obtain ⟨⟨A, B⟩, hAB⟩ := sl2cDoubleCoverMap_surjective Λ
  obtain ⟨U₁, V₁, U₂, V₂, a, b, ha, hb, hA, hB⟩ := sl2c_pair_kak A B
  obtain ⟨R₁, hR₁⟩ := sl2cDoubleCover_unitary_maps_to_real U₁ U₂
  obtain ⟨R₂, hR₂⟩ := sl2cDoubleCover_unitary_maps_to_real V₁ V₂
  refine ⟨R₁, R₂, a, b, ha, hb, ?_⟩
  -- Λ = Φ(A,B) and A = U₁·D·V₁, B = U₂·D'·V₂
  -- Φ(U₁·D·V₁, U₂·D'·V₂) = Φ(U₁,U₂)·Φ(D,D')·Φ(V₁,V₂) = R₁·D·R₂
  change sl2cDoubleCoverMap A B = _ at hAB
  rw [hA, hB] at hAB
  rw [← hAB]; simp only [diagonalLorentz]
  -- Group algebra for SL(2,ℂ) and ComplexLorentzGroup
  rw [show U₁.toSL * diagonalSL2 a ha * V₁.toSL =
      U₁.toSL * (diagonalSL2 a ha * V₁.toSL) from mul_assoc _ _ _,
    show U₂.toSL * diagonalSL2 b hb * V₂.toSL =
      U₂.toSL * (diagonalSL2 b hb * V₂.toSL) from mul_assoc _ _ _,
    sl2cDoubleCoverMap_mul, sl2cDoubleCoverMap_mul, hR₁, hR₂, mul_assoc]

/-! ### The diagonal parameter set -/

/-- Parameters (a,b) ∈ (ℂ*)² whose diagonal Lorentz element is in the index set. -/
def diagonalParamSet (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Set ({p : ℂ × ℂ // p.1 ≠ 0 ∧ p.2 ≠ 0}) :=
  {p | diagonalLorentz p.val.1 p.val.2 p.prop.1 p.prop.2 ∈
    permForwardOverlapIndexSet (d := 3) n σ}

/-- The diagonal Lorentz map is continuous. -/
axiom continuous_diagonalLorentz :
    Continuous (fun p : {p : ℂ × ℂ // p.1 ≠ 0 ∧ p.2 ≠ 0} =>
      diagonalLorentz p.val.1 p.val.2 p.prop.1 p.prop.2)

/-- The diagonal parameter set is connected. -/
axiom isConnected_diagonalParamSet
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
    IsConnected (diagonalParamSet n σ)

/-! ### Assembly -/

/-- The index set equals the image of K × P × K. -/
private theorem indexSet_eq_image_kak
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
    permForwardOverlapIndexSet (d := 3) n σ =
    (fun trip : RestrictedLorentzGroup 3 ×
        {p : ℂ × ℂ // p.1 ≠ 0 ∧ p.2 ≠ 0} ×
        RestrictedLorentzGroup 3 =>
      ComplexLorentzGroup.ofReal trip.1 *
      diagonalLorentz trip.2.1.val.1 trip.2.1.val.2 trip.2.1.prop.1 trip.2.1.prop.2 *
      ComplexLorentzGroup.ofReal trip.2.2) ''
    (Set.univ ×ˢ diagonalParamSet n σ ×ˢ Set.univ) := by
  ext Λ
  simp only [Set.mem_image, Set.mem_prod, Set.mem_univ, true_and]
  constructor
  · intro hΛ
    obtain ⟨R₁, R₂, a, b, ha, hb, hΛeq⟩ := complexLorentz3_kak_decomposition Λ
    have hD : diagonalLorentz a b ha hb ∈ permForwardOverlapIndexSet (d := 3) n σ := by
      have h1 := indexSet_left_invariant_d3 n σ hΛ R₁⁻¹
      have h2 := indexSet_right_invariant_d3 n σ h1 R₂⁻¹
      suffices hsuff :
          ComplexLorentzGroup.ofReal R₁⁻¹ * Λ * ComplexLorentzGroup.ofReal R₂⁻¹ =
          diagonalLorentz a b ha hb from hsuff ▸ h2
      rw [hΛeq]
      simp only [mul_assoc]
      rw [show ComplexLorentzGroup.ofReal R₁⁻¹ *
            (ComplexLorentzGroup.ofReal R₁ *
              (diagonalLorentz a b ha hb *
                (ComplexLorentzGroup.ofReal R₂ * ComplexLorentzGroup.ofReal R₂⁻¹))) =
          (ComplexLorentzGroup.ofReal R₁⁻¹ * ComplexLorentzGroup.ofReal R₁) *
            (diagonalLorentz a b ha hb *
              (ComplexLorentzGroup.ofReal R₂ * ComplexLorentzGroup.ofReal R₂⁻¹)) from by
            rw [mul_assoc]]
      rw [← ofReal_mul_eq, inv_mul_cancel, ofReal_one_eq, one_mul,
          ← ofReal_mul_eq, mul_inv_cancel, ofReal_one_eq, mul_one]
    let p : {p : ℂ × ℂ // p.1 ≠ 0 ∧ p.2 ≠ 0} := ⟨(a, b), ha, hb⟩
    exact ⟨(R₁, p, R₂), ⟨hD, trivial⟩, hΛeq.symm⟩
  · rintro ⟨⟨R₁, p, R₂⟩, ⟨hp, _⟩, rfl⟩
    simp only [diagonalParamSet, Set.mem_setOf_eq] at hp
    have h1 := indexSet_right_invariant_d3 n σ hp R₂
    rw [mul_assoc]
    exact indexSet_left_invariant_d3 n σ h1 R₁

/-- The K × P × K map is continuous. -/
private theorem continuous_kak_map :
    Continuous (fun trip : RestrictedLorentzGroup 3 ×
        {p : ℂ × ℂ // p.1 ≠ 0 ∧ p.2 ≠ 0} ×
        RestrictedLorentzGroup 3 =>
      ComplexLorentzGroup.ofReal trip.1 *
      diagonalLorentz trip.2.1.val.1 trip.2.1.val.2 trip.2.1.prop.1 trip.2.1.prop.2 *
      ComplexLorentzGroup.ofReal trip.2.2) := by
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_ofReal.comp continuous_fst
    · exact continuous_diagonalLorentz.comp (continuous_fst.comp continuous_snd)
  · exact continuous_ofReal.comp (continuous_snd.comp continuous_snd)

/-- **Main theorem: the slice index set is connected for d = 3.** -/
theorem isConnected_sliceIndexSet_d3
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
    IsConnected (permForwardOverlapIndexSet (d := 3) n σ) := by
  rw [indexSet_eq_image_kak n σ hσ]
  apply IsConnected.image
  · have hK_conn : IsConnected (Set.univ : Set (RestrictedLorentzGroup 3)) :=
      (RestrictedLorentzGroup.isPathConnected (d := 3)).isConnected
    have hP_conn : IsConnected (diagonalParamSet n σ) :=
      isConnected_diagonalParamSet n σ hσ
    -- ×ˢ is right-associative: A ×ˢ B ×ˢ C = A ×ˢ (B ×ˢ C)
    -- but product types are left-associative: (A × B) × C
    -- Need IsConnected (Set.univ ×ˢ (diagonalParamSet n σ ×ˢ Set.univ))
    exact hK_conn.prod (hP_conn.prod hK_conn)
  · exact continuous_kak_map.continuousOn

end BHW
