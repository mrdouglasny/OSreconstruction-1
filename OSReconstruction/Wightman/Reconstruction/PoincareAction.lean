/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import OSReconstruction.Wightman.WightmanAxioms

/-!
# Poincaré Action on Schwartz Test Functions

This file defines the action of the Poincaré group on Schwartz test functions:
  (g · f)(x) = f(g⁻¹ · x)

The Schwartz class is preserved because:
- Poincaré transformations are affine maps (linear + translation)
- Composition with an invertible affine map preserves smoothness
- Composition with an invertible affine map preserves polynomial decay
  (since ‖g⁻¹ · x‖ ∼ ‖x‖ for invertible linear maps)

## Main definitions
- `poincareActSchwartz`: The Poincaré action on Schwartz functions
- `poincareActSchwartz_spec`: (g · f)(x) = f(g⁻¹ · x)
-/

open scoped Matrix

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### Smoothness and decay for affine reparametrization -/

/-- Composition of a Schwartz function with an affine map is smooth.
    This follows because affine maps are smooth (ContDiff ℝ ⊤) and
    the composition of smooth functions is smooth. -/
private theorem affineComp_smooth (g : PoincareGroup d) (f : SchwartzSpacetime d) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : SpacetimeDim d => f (PoincareGroup.act g x)) :=
  f.smooth'.comp (ContDiff.add
    ((Matrix.mulVecLin g.lorentz.val).toContinuousLinearMap).contDiff contDiff_const)

/-- Composition of a Schwartz function with an invertible affine map has polynomial decay.
    This is the key technical result: if f ∈ S(ℝⁿ) and g is an invertible affine map,
    then f ∘ g has Schwartz decay.

    The proof uses:
    1. The Faà di Bruno formula for iteratedFDeriv (f ∘ g), which simplifies for
       affine g to: D^n(f ∘ g)(x) = D^n f(g(x)) ∘ (L, ..., L) where L is the linear part
    2. The norm bound ‖x‖ ≤ C * (1 + ‖g(x)‖) from invertibility of g
    3. The Schwartz decay of f: ‖x‖^k * ‖D^n f(x)‖ ≤ C_{k,n} -/
private theorem affineComp_decay (g : PoincareGroup d) (f : SchwartzSpacetime d)
    (k n : ℕ) :
    ∃ C, ∀ (x : SpacetimeDim d),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f (PoincareGroup.act g x)) x‖ ≤ C := by
  sorry

/-! ### The Poincaré action on Schwartz test functions -/

/-- The Poincaré action on a Schwartz test function:
    (g · f)(x) = f(g⁻¹ · x)

    This is well-defined because composition with an invertible affine map
    preserves the Schwartz class. -/
def poincareActSchwartz (g : PoincareGroup d) (f : SchwartzSpacetime d) :
    SchwartzSpacetime d where
  toFun x := f (PoincareGroup.act g⁻¹ x)
  smooth' := affineComp_smooth g⁻¹ f
  decay' k n := affineComp_decay g⁻¹ f k n

/-- The Poincaré action satisfies the pointwise spec:
    (g · f)(x) = f(g⁻¹ · x). -/
@[simp]
theorem poincareActSchwartz_apply (g : PoincareGroup d) (f : SchwartzSpacetime d)
    (x : SpacetimeDim d) :
    (poincareActSchwartz g f) x = f (PoincareGroup.act g⁻¹ x) := rfl

/-- The Poincaré action spec in terms of `.toFun` (matching WightmanQFT.poincareAction_spec). -/
theorem poincareActSchwartz_toFun (g : PoincareGroup d) (f : SchwartzSpacetime d)
    (x : SpacetimeDim d) :
    (poincareActSchwartz g f).toFun x = f.toFun (PoincareGroup.act g⁻¹ x) := rfl

/-! ### Group action properties -/

/-- The identity acts trivially: 1 · f = f. -/
theorem poincareActSchwartz_one (f : SchwartzSpacetime d) :
    poincareActSchwartz 1 f = f := by
  ext x
  simp [poincareActSchwartz_apply, PoincareGroup.act_one]

/-- The action is compatible with group multiplication: (g₁g₂) · f = g₁ · (g₂ · f). -/
theorem poincareActSchwartz_mul (g₁ g₂ : PoincareGroup d) (f : SchwartzSpacetime d) :
    poincareActSchwartz (g₁ * g₂) f = poincareActSchwartz g₁ (poincareActSchwartz g₂ f) := by
  ext x
  simp [poincareActSchwartz_apply, ← PoincareGroup.act_mul, mul_inv_rev]

end
