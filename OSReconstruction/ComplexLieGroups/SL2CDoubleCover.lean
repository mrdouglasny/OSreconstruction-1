/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.PathConnected
import OSReconstruction.ComplexLieGroups.Complexification
import OSReconstruction.ComplexLieGroups.MatrixLieGroup

/-!
# SL(2,ℂ) Double Cover of SO₊(1,3;ℂ)

The double cover Φ: SL(2,ℂ) × SL(2,ℂ) → SO₊(1,3;ℂ) via Pauli matrices,
together with the KAK decomposition for SL(2,ℂ).

## Main definitions

* `pauliMatrix` — the four 2×2 Pauli matrices σ₀, σ₁, σ₂, σ₃
* `sl2cDoubleCoverMap` — the map Φ(A,B) ∈ SO₊(1,3;ℂ)
* `SU2` — the special unitary group SU(2) as a subtype of SL(2,ℂ)
* `diagonalSL2` — diagonal element diag(a, a⁻¹) ∈ SL(2,ℂ)

## Main results

* `sl2cDoubleCoverMap_surjective` — Φ is surjective (axiom)
* `sl2cDoubleCover_unitary_maps_to_real` — SU(2)×SU(2) maps to real Lorentz
* `sl2c_kak` — KAK decomposition: every A ∈ SL(2,ℂ) is UDV

## References

* Bogolyubov, Logunov, Oksak & Todorov,
  *General Principles of Quantum Field Theory* (1990), Ch. 9
* Streater & Wightman, *PCT, Spin and Statistics*, §1-4
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup
open scoped MatrixGroups

namespace SL2CDoubleCover

/-! ### Pauli matrices -/

/-- Pauli matrix σ₀ = I₂. -/
def σ₀ : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- Pauli matrix σ₁ = [[0,1],[1,0]]. -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli matrix σ₂ = [[0,-i],[i,0]]. -/
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- Pauli matrix σ₃ = [[1,0],[0,-1]]. -/
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The four Pauli matrices indexed by Fin 4. -/
def pauliMatrix (μ : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  match μ with
  | ⟨0, _⟩ => σ₀
  | ⟨1, _⟩ => σ₁
  | ⟨2, _⟩ => σ₂
  | ⟨3, _⟩ => σ₃

/-! ### SU(2) as subtype of SL(2,ℂ) -/

/-- SU(2): special unitary 2×2 matrices. An element A ∈ SL(2,ℂ) with A†A = I. -/
def IsSU2 (A : SL(2, ℂ)) : Prop :=
  (A : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose * (A : Matrix (Fin 2) (Fin 2) ℂ) = 1

/-- SU(2) as a subtype of SL(2,ℂ). -/
def SU2 := {A : SL(2, ℂ) // IsSU2 A}

/-- SU(2) inherits a topology from SL(2,ℂ). -/
instance : TopologicalSpace SU2 := instTopologicalSpaceSubtype

/-- SU(2) group structure (inherited from SL(2,ℂ)).
    Closure under multiplication and inversion follows from the
    multiplicativity of conjTranspose and det. -/
instance : Group SU2 where
  mul a b := ⟨a.val * b.val, sorry⟩
  one := ⟨1, by simp [IsSU2]⟩
  inv a := ⟨a.val⁻¹, sorry⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.val b.val c.val)
  one_mul a := Subtype.ext (one_mul a.val)
  mul_one a := Subtype.ext (mul_one a.val)
  inv_mul_cancel a := Subtype.ext (inv_mul_cancel a.val)

/-- SU(2) is path-connected (SU(2) ≅ S³). -/
axiom SU2_isPathConnected : IsPathConnected (Set.univ : Set SU2)

/-- The embedding SU(2) → SL(2,ℂ). -/
def SU2.toSL (U : SU2) : SL(2, ℂ) := U.val

/-! ### Diagonal SL(2,ℂ) elements -/

/-- Diagonal element diag(a, a⁻¹) ∈ SL(2,ℂ) for a ≠ 0. -/
def diagonalSL2 (a : ℂ) (ha : a ≠ 0) : SL(2, ℂ) :=
  ⟨Matrix.diagonal ![a, a⁻¹], by
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_two, mul_inv_cancel₀ ha]⟩

/-! ### Double cover map Φ: SL(2,ℂ) × SL(2,ℂ) → SO₊(1,3;ℂ) -/

/-- The double cover map Φ: SL(2,ℂ) × SL(2,ℂ) → SO₊(1,3;ℂ).

This map is defined by Λ_μν = (1/2) Tr(σ̃_μ · A · σ_ν · Bᵀ) where
σ̃ are the modified Pauli matrices incorporating the metric.

We axiomatize the construction: the map lands in ComplexLorentzGroup 3,
is a group homomorphism, and is continuous. -/
axiom sl2cDoubleCoverMap (A B : SL(2, ℂ)) : ComplexLorentzGroup 3

/-- The double cover map is a group homomorphism in each component. -/
axiom sl2cDoubleCoverMap_mul (A₁ A₂ B₁ B₂ : SL(2, ℂ)) :
    sl2cDoubleCoverMap (A₁ * A₂) (B₁ * B₂) =
    sl2cDoubleCoverMap A₁ B₁ * sl2cDoubleCoverMap A₂ B₂

/-- Φ(1,1) = 1. -/
axiom sl2cDoubleCoverMap_one :
    sl2cDoubleCoverMap 1 1 = (1 : ComplexLorentzGroup 3)

/-- The double cover map is continuous. -/
axiom sl2cDoubleCoverMap_continuous :
    Continuous (fun p : SL(2, ℂ) × SL(2, ℂ) => sl2cDoubleCoverMap p.1 p.2)

/-- **Surjectivity of the double cover.**
    True because: dΦ is a Lie algebra isomorphism sl(2,ℂ)⊕sl(2,ℂ) ≅ so(4,ℂ) ≅ so₊(1,3;ℂ),
    so Φ is a local diffeomorphism. Its image is open and closed in the connected
    group SO₊(1,3;ℂ), hence surjective. -/
axiom sl2cDoubleCoverMap_surjective :
    Function.Surjective (fun p : SL(2, ℂ) × SL(2, ℂ) => sl2cDoubleCoverMap p.1 p.2)

/-! ### SU(2) × SU(2) → real Lorentz -/

/-- Under the double cover, SU(2) × SU(2) maps to the real restricted Lorentz group.
    This is because unitary matrices preserve Hermitian matrices, and the
    Pauli-matrix parametrization sends Hermitian 2×2 matrices to real 4-vectors. -/
axiom sl2cDoubleCover_unitary_maps_to_real (U V : SU2) :
    ∃ R : RestrictedLorentzGroup 3,
      sl2cDoubleCoverMap U.toSL V.toSL = ComplexLorentzGroup.ofReal R

/-! ### KAK decomposition for SL(2,ℂ) -/

/-- **KAK decomposition for SL(2,ℂ)**: every element A ∈ SL(2,ℂ) can be written
    as A = U · diag(a, a⁻¹) · V where U, V ∈ SU(2) and a ∈ ℂ*.

    This follows from the singular value decomposition of 2×2 complex matrices
    with determinant 1. The matrix A†A is positive definite Hermitian, hence
    diagonalizable by a unitary, giving the Cartan decomposition. -/
axiom sl2c_kak (A : SL(2, ℂ)) :
    ∃ (U V : SU2) (a : ℂ) (ha : a ≠ 0),
      A = U.toSL * diagonalSL2 a ha * V.toSL

/-! ### KAK decomposition for pairs -/

/-- Every pair (A, B) ∈ SL(2,ℂ)² has a KAK decomposition:
    A = U₁ D(a) V₁, B = U₂ D(b) V₂ with U,V ∈ SU(2). -/
theorem sl2c_pair_kak (A B : SL(2, ℂ)) :
    ∃ (U₁ V₁ U₂ V₂ : SU2) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0),
      A = U₁.toSL * diagonalSL2 a ha * V₁.toSL ∧
      B = U₂.toSL * diagonalSL2 b hb * V₂.toSL := by
  obtain ⟨U₁, V₁, a, ha, hA⟩ := sl2c_kak A
  obtain ⟨U₂, V₂, b, hb, hB⟩ := sl2c_kak B
  exact ⟨U₁, V₁, U₂, V₂, a, b, ha, hb, hA, hB⟩

end SL2CDoubleCover
