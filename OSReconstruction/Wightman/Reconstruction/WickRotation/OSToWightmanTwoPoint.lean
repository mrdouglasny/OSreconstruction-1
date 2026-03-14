/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman

/-!
# OS to Wightman Two-Point Continuation Reductions

This file contains the specialized `k = 2` continuation/reduction ladder for the
`E→R` reconstruction chain:

- admissible-shell vs witness-shell equivalences
- normalized-center reduction and uniqueness
- Laplace / polarized-Laplace sufficient criteria
- semigroup spectral and matrix-element criteria
- product-shell sufficient criteria

The analytic-continuation core and live base-step blocker remain in
`OSToWightman.lean`.
-/

open scoped Classical NNReal
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]

theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_iff_xiShiftWitness_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (χ h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    (∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))))) ↔
    (∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
              ((t : ℂ) * Complex.I)) *
              (χ (y 0) * h (y 1)))) := by
  constructor
  · rintro ⟨H, hH_holo, hH_real⟩
    refine ⟨H, hH_holo, ?_⟩
    intro t ht
    rw [hH_real t ht]
    exact schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      χ h hh_pos t ht
  · rintro ⟨H, hH_holo, hH_real⟩
    refine ⟨H, hH_holo, ?_⟩
    intro t ht
    rw [hH_real t ht]
    exact (schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      χ h hh_pos t ht).symm

/-- Real-axis center collapse directly in the original `Ψ` witness coordinates.
For each fixed positive Euclidean time `t`, the admissible two-point
`ξ`-shifted witness on the center/difference shell depends on the center cutoff
only through `∫ χ`. -/
theorem schwinger_twoPoint_xiShiftWitness_exists_const_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ c : ℂ, ∀ χ : SchwartzSpacetime d,
      ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ (y 0) * h (y 1)) =
        c * ∫ u : SpacetimeDim d, χ u := by
  have hshift0 :
      (0 : SpacetimeDim d) ∉ tsupport
        (((SCV.translateSchwartz (- timeShiftVec d t) h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)) := by
    refine zero_not_mem_tsupport_translate_of_notMem (d := d) h (- timeShiftVec d t) ?_
    exact neg_timeShiftVec_not_mem_positive_tsupport (d := d) h hh_pos t ht
  obtain ⟨c, hc⟩ :=
    OsterwalderSchraderAxioms.exists_const_twoPointDifferenceLift_eq_integral
      (d := d) (OS := OS) (h := SCV.translateSchwartz (- timeShiftVec d t) h) hshift0
  refine ⟨c, ?_⟩
  intro χ
  calc
    ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ (y 0) * h (y 1))
      = OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
          symm
          exact schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            χ h hh_pos t ht
    _ = c * ∫ u : SpacetimeDim d, χ u := hc χ

/-- Normalized center-value form of the real-axis two-point `ξ`-shift witness.
Fixing one center cutoff with integral `1` identifies the scalar from
`schwinger_twoPoint_xiShiftWitness_exists_const_of_positiveSupport` explicitly. -/
theorem schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d) :
    ∫ y : NPointDomain d 2,
      Ψ (xiShift ⟨1, by omega⟩ 0
        (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
        ((t : ℂ) * Complex.I)) *
        (χ (y 0) * h (y 1)) =
      (∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) *
        ∫ u : SpacetimeDim d, χ u := by
  obtain ⟨c, hc⟩ :=
    schwinger_twoPoint_xiShiftWitness_exists_const_of_positiveSupport
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid) h hh_pos t ht
  calc
    ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ (y 0) * h (y 1))
      = c * ∫ u : SpacetimeDim d, χ u := hc χ
    _ = (c * ∫ u : SpacetimeDim d, χ₀ u) * ∫ u : SpacetimeDim d, χ u := by
          rw [hχ₀, mul_one]
    _ = (∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) *
          ∫ u : SpacetimeDim d, χ u := by
          rw [hc χ₀]

/-- Zero-mean center cutoffs are annihilated by the real-axis two-point
`ξ`-shift witness. This is the exact real-axis vanishing statement needed for a
future identity-theorem step once the holomorphic shell is built on the
admissible center/difference family. -/
theorem schwinger_twoPoint_xiShiftWitness_eq_zero_of_centerIntegral_zero_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d)
    (hχ : ∫ u : SpacetimeDim d, χ u = 0) :
    ∫ y : NPointDomain d 2,
      Ψ (xiShift ⟨1, by omega⟩ 0
        (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
        ((t : ℂ) * Complex.I)) *
        (χ (y 0) * h (y 1)) = 0 := by
  rw [schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport
    (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
    h hh_pos t ht χ₀ hχ₀ χ, hχ, mul_zero]

/-- Equivalent center cutoffs, i.e. cutoffs with the same integral, give the
same real-axis two-point `ξ`-shift witness value. This is the clean
“depends only on `∫ χ`” form of center collapse in the original `Ψ`
coordinates. -/
theorem schwinger_twoPoint_xiShiftWitness_eq_of_centerIntegral_eq_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ χ₁ : SchwartzSpacetime d)
    (hint : ∫ u : SpacetimeDim d, χ₀ u = ∫ u : SpacetimeDim d, χ₁ u) :
    (∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) =
      ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₁ (y 0) * h (y 1)) := by
  obtain ⟨c, hc⟩ :=
    schwinger_twoPoint_xiShiftWitness_exists_const_of_positiveSupport
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid) h hh_pos t ht
  calc
    ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))
      = c * ∫ u : SpacetimeDim d, χ₀ u := hc χ₀
    _ = c * ∫ u : SpacetimeDim d, χ₁ u := by rw [hint]
    _ = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₁ (y 0) * h (y 1)) := by
          rw [hc χ₁]

/-- Direct normalized-center formula for the positive-time shifted Schwinger
two-point family. Fixing one center cutoff with integral `1` identifies the
entire admissible real-axis family as a single normalized `ξ`-shift witness
value times `∫ χ`. -/
theorem schwinger_twoPointDifferenceLift_timeShift_eq_centerValue_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d) :
    OS.S 2
      (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ
          (SCV.translateSchwartz (- timeShiftVec d t) h))) =
      (∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) *
        ∫ u : SpacetimeDim d, χ u := by
  calc
    OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ
            (SCV.translateSchwartz (- timeShiftVec d t) h)))
      = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * h (y 1)) := by
          exact schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            χ h hh_pos t ht
    _ = (∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) *
          ∫ u : SpacetimeDim d, χ u := by
          exact schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            h hh_pos t ht χ₀ hχ₀ χ

/-- Zero-mean center cutoffs are annihilated by the positive-time shifted
two-point Schwinger family. This is the `OS.S 2` form of the real-axis
center-slot collapse. -/
theorem schwinger_twoPointDifferenceLift_timeShift_eq_zero_of_centerIntegral_zero_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d)
    (hχ : ∫ u : SpacetimeDim d, χ u = 0) :
    OS.S 2
      (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ
          (SCV.translateSchwartz (- timeShiftVec d t) h))) = 0 := by
  rw [schwinger_twoPointDifferenceLift_timeShift_eq_centerValue_of_positiveSupport
    (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
    h hh_pos t ht χ₀ hχ₀ χ, hχ, mul_zero]

/-- Once a holomorphic family is known for one normalized center cutoff `χ₀`,
the real-axis center-collapse formulas promote it to every other center cutoff
by simple scalar multiplication by `∫ χ`. This reduces the `k = 2` admissible
shell holomorphic existence problem to a single normalized center test. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (H₀ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1)))
    (χ : SchwartzSpacetime d) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
  let c : ℂ := ∫ u : SpacetimeDim d, χ u
  refine ⟨fun z => c * H₀ z, ?_, ?_⟩
  · exact hH₀_holo.const_mul c
  · intro t ht
    calc
      c * H₀ (t : ℂ)
        = c * ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (y 0) * h (y 1)) := by
              rw [hH₀_real t ht]
      _ = OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
              rw [mul_comm]
              symm
              exact schwinger_twoPointDifferenceLift_timeShift_eq_centerValue_of_positiveSupport
                (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
                h hh_pos t ht χ₀ hχ₀ χ

/-- Uniqueness of the holomorphic continuation for the admissible positive-time
two-point center/difference shell. Once the positive-real values are fixed,
there is at most one holomorphic family on the right half-plane. -/
theorem twoPointDifferenceLift_timeShift_holomorphicValue_eq_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (h : SchwartzSpacetime d)
    (χ : SchwartzSpacetime d)
    (H₀ H₁ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₁_holo : DifferentiableOn ℂ H₁ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))))
    (hH₁_real : ∀ t : ℝ, 0 < t →
      H₁ (t : ℂ) =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h)))) :
    Set.EqOn H₀ H₁ {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_re_gt (0 : ℝ)
  have hU_conn : IsConnected U := ⟨⟨1, by simp [U]⟩, hU_conv.isPreconnected⟩
  have h_freq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, H₀ z = H₁ z := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    rintro ⟨V, hV_open, h1_mem, hV_sub⟩
    obtain ⟨r, hr_pos, hrV⟩ := Metric.isOpen_iff.mp hV_open 1 h1_mem
    let ε : ℝ := min (r / 2) (1 / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have hε_lt_r : ε < r := by
      have hr2 : r / 2 < r := by linarith
      exact lt_of_le_of_lt (by dsimp [ε]; exact min_le_left _ _) hr2
    have hz_in_V : (((1 + ε : ℝ) : ℂ)) ∈ V := by
      apply hrV
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact hε_lt_r
    have hz_ne : (((1 + ε : ℝ) : ℂ)) ≠ 1 := by
      intro hz
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      have hε_zero : (ε : ℂ) = 0 := by
        simpa [hsub] using sub_eq_zero.mpr hz
      exact hε_pos.ne' (Complex.ofReal_eq_zero.mp hε_zero)
    have hreal_eq : H₀ ((1 + ε : ℝ) : ℂ) = H₁ ((1 + ε : ℝ) : ℂ) := by
      have hpos : 0 < 1 + ε := by linarith
      rw [hH₀_real (1 + ε) hpos, hH₁_real (1 + ε) hpos]
    exact hV_sub ⟨hz_in_V, hz_ne⟩ hreal_eq
  exact identity_theorem_connected hU_open hU_conn H₀ H₁
    hH₀_holo hH₁_holo (1 : ℂ) (by simp [U]) h_freq

/-- Witness-level promotion of a normalized-center holomorphic family on the
admissible two-point center/difference shell. Once one normalized cutoff `χ₀`
with `∫ χ₀ = 1` is handled holomorphically, every other center cutoff `χ` is
recovered by multiplying by `∫ χ`. This is the exact `ξ`-shift witness form of
the `k = 2` reduction, with no `OS.S 2` left in the conclusion. -/
theorem exists_twoPoint_xiShiftWitness_holomorphicValue_of_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (H₀ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1)))
    (χ : SchwartzSpacetime d) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
              ((t : ℂ) * Complex.I)) *
              (χ (y 0) * h (y 1)) := by
  let c : ℂ := ∫ u : SpacetimeDim d, χ u
  refine ⟨fun z => c * H₀ z, hH₀_holo.const_mul c, ?_⟩
  intro t ht
  calc
    c * H₀ (t : ℂ)
      = c * ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1)) := by
          rw [hH₀_real t ht]
    _ = (∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) *
          ∫ u : SpacetimeDim d, χ u := by
          rw [mul_comm]
    _ = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * h (y 1)) := by
          symm
          exact schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            h hh_pos t ht χ₀ hχ₀ χ

/-- Any two holomorphic realizations of the normalized-center admissible
two-point `ξ`-shift witness must agree on the whole right half-plane. So once
existence is proved for one normalized center cutoff, the resulting
holomorphic family is canonical and independent of that choice. -/
theorem twoPoint_xiShiftWitness_holomorphicValue_eq_of_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ χ₁ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hχ₁ : ∫ u : SpacetimeDim d, χ₁ u = 1)
    (H₀ H₁ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₁_holo : DifferentiableOn ℂ H₁ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1)))
    (hH₁_real : ∀ t : ℝ, 0 < t →
      H₁ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₁ (y 0) * h (y 1))) :
    Set.EqOn H₀ H₁ {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_re_gt (0 : ℝ)
  have hU_conn : IsConnected U := ⟨⟨1, by simp [U]⟩, hU_conv.isPreconnected⟩
  have h_freq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, H₀ z = H₁ z := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    rintro ⟨V, hV_open, h1_mem, hV_sub⟩
    obtain ⟨r, hr_pos, hrV⟩ := Metric.isOpen_iff.mp hV_open 1 h1_mem
    let ε : ℝ := min (r / 2) (1 / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have hε_lt_r : ε < r := by
      have hr2 : r / 2 < r := by linarith
      exact lt_of_le_of_lt (by dsimp [ε]; exact min_le_left _ _) hr2
    have hz_in_V : (((1 + ε : ℝ) : ℂ)) ∈ V := by
      apply hrV
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact hε_lt_r
    have hz_ne : (((1 + ε : ℝ) : ℂ)) ≠ 1 := by
      intro hz
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      have hε_zero : (ε : ℂ) = 0 := by
        simpa [hsub] using sub_eq_zero.mpr hz
      exact hε_pos.ne' (Complex.ofReal_eq_zero.mp hε_zero)
    have hreal_eq : H₀ ((1 + ε : ℝ) : ℂ) = H₁ ((1 + ε : ℝ) : ℂ) := by
      have hpos : 0 < 1 + ε := by linarith
      rw [hH₀_real (1 + ε) hpos, hH₁_real (1 + ε) hpos]
      exact schwinger_twoPoint_xiShiftWitness_eq_of_centerIntegral_eq_of_positiveSupport
        (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
        h hh_pos (1 + ε) hpos χ₀ χ₁ (by simp [hχ₀, hχ₁])
    exact hV_sub ⟨hz_in_V, hz_ne⟩ hreal_eq
  exact identity_theorem_connected hU_open hU_conn H₀ H₁
    hH₀_holo hH₁_holo (1 : ℂ) (by simp [U]) h_freq

omit [NeZero d] in
/-- Uniqueness of the holomorphic continuation on the admissible positive-time
two-point `ξ`-shift witness shell. Once the positive-real witness values are
fixed for one center cutoff `χ`, the holomorphic family on the right half-plane
is unique. -/
theorem twoPoint_xiShiftWitness_holomorphicValue_eq_of_positiveSupport
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (h : SchwartzSpacetime d)
    (χ : SchwartzSpacetime d)
    (H₀ H₁ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₁_holo : DifferentiableOn ℂ H₁ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * h (y 1)))
    (hH₁_real : ∀ t : ℝ, 0 < t →
      H₁ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * h (y 1))) :
    Set.EqOn H₀ H₁ {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_re_gt (0 : ℝ)
  have hU_conn : IsConnected U := ⟨⟨1, by simp [U]⟩, hU_conv.isPreconnected⟩
  have h_freq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, H₀ z = H₁ z := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    rintro ⟨V, hV_open, h1_mem, hV_sub⟩
    obtain ⟨r, hr_pos, hrV⟩ := Metric.isOpen_iff.mp hV_open 1 h1_mem
    let ε : ℝ := min (r / 2) (1 / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have hε_lt_r : ε < r := by
      have hr2 : r / 2 < r := by linarith
      exact lt_of_le_of_lt (by dsimp [ε]; exact min_le_left _ _) hr2
    have hz_in_V : (((1 + ε : ℝ) : ℂ)) ∈ V := by
      apply hrV
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact hε_lt_r
    have hz_ne : (((1 + ε : ℝ) : ℂ)) ≠ 1 := by
      intro hz
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      have hε_zero : (ε : ℂ) = 0 := by
        simpa [hsub] using sub_eq_zero.mpr hz
      exact hε_pos.ne' (Complex.ofReal_eq_zero.mp hε_zero)
    have hreal_eq : H₀ ((1 + ε : ℝ) : ℂ) = H₁ ((1 + ε : ℝ) : ℂ) := by
      have hpos : 0 < 1 + ε := by linarith
      rw [hH₀_real (1 + ε) hpos, hH₁_real (1 + ε) hpos]
    exact hV_sub ⟨hz_in_V, hz_ne⟩ hreal_eq
  exact identity_theorem_connected hU_open hU_conn H₀ H₁
    hH₀_holo hH₁_holo (1 : ℂ) (by simp [U]) h_freq

/-- Exact witness-level `k = 2` reduction on the admissible positive-time
    center/difference shell. For a fixed normalized center cutoff `χ₀`,
    constructing one holomorphic `ξ`-shift witness family for `χ₀` is
    equivalent to constructing, for every center cutoff `χ`, the canonical
    holomorphic witness family, unique on the right half-plane. -/
theorem exists_twoPoint_xiShiftWitness_holomorphicValue_iff_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1) :
    (∃ H₀ : ℂ → ℂ,
      DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H₀ (t : ℂ) =
          ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (y 0) * h (y 1)))) ↔
    (∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            ∫ y : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                ((t : ℂ) * Complex.I)) *
                (χ (y 0) * h (y 1))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              ∫ y : NPointDomain d 2,
                Ψ (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                  ((t : ℂ) * Complex.I)) *
                  (χ (y 0) * h (y 1))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re}) := by
  constructor
  · intro hcenter χ
    rcases hcenter with ⟨H₀, hH₀_holo, hH₀_real⟩
    rcases exists_twoPoint_xiShiftWitness_holomorphicValue_of_centerValue
        (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
        h hh_pos χ₀ hχ₀ H₀ hH₀_holo hH₀_real χ with ⟨H, hH_holo, hH_real⟩
    refine ⟨H, hH_holo, hH_real, ?_⟩
    intro H' hH'_holo hH'_real
    have hH_os : ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
      intro t ht
      rw [hH_real t ht]
      exact (schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
        (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
        χ h hh_pos t ht).symm
    have hH'_os : ∀ t : ℝ, 0 < t →
        H' (t : ℂ) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
      intro t ht
      rw [hH'_real t ht]
      exact (schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
        (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
        χ h hh_pos t ht).symm
    exact twoPointDifferenceLift_timeShift_holomorphicValue_eq_of_positiveSupport
      (d := d) (OS := OS) h χ H H' hH_holo hH'_holo hH_os hH'_os
  · intro hall
    rcases hall χ₀ with ⟨H₀, hH₀_holo, hH₀_real, _huniq⟩
    exact ⟨H₀, hH₀_holo, hH₀_real⟩

/-- Canonical holomorphic continuation on the admissible positive-time
two-point center/difference shell. Once one normalized center cutoff `χ₀`
produces a holomorphic family, every center cutoff `χ` gets a holomorphic
continuation, and any two such continuations agree on the right half-plane. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_centerValue_unique
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (H₀ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1)))
    (χ : SchwartzSpacetime d) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h)))) ∧
      ∀ H' : ℂ → ℂ,
        DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
        (∀ t : ℝ, 0 < t →
          H' (t : ℂ) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ
                  (SCV.translateSchwartz (- timeShiftVec d t) h)))) →
        Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  rcases exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_centerValue
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀ H₀ hH₀_holo hH₀_real χ with ⟨H, hH_holo, hH_real⟩
  refine ⟨H, hH_holo, hH_real, ?_⟩
  intro H' hH'_holo hH'_real
  exact twoPointDifferenceLift_timeShift_holomorphicValue_eq_of_positiveSupport
    (d := d) (OS := OS) h χ H H' hH_holo hH'_holo hH_real hH'_real

/-- Exact `k = 2` reduction theorem on the admissible positive-time shell.
    For a fixed normalized center cutoff `χ₀`, constructing one holomorphic
    family for that single cutoff is equivalent to constructing, for every
    center cutoff `χ`, the canonical holomorphic continuation on the right
    half-plane. This isolates the remaining two-point `E -> R` gap precisely:
    only the normalized-center existence problem is still open. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_iff_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1) :
    (∃ H₀ : ℂ → ℂ,
      DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H₀ (t : ℂ) =
          ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (y 0) * h (y 1)))) ↔
    (∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ
                  (SCV.translateSchwartz (- timeShiftVec d t) h)))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              OS.S 2
                (ZeroDiagonalSchwartz.ofClassical
                  (twoPointDifferenceLift χ
                    (SCV.translateSchwartz (- timeShiftVec d t) h)))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re}) := by
  constructor
  · intro hcenter χ
    rcases hcenter with ⟨H₀, hH₀_holo, hH₀_real⟩
    exact exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_centerValue_unique
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀ H₀ hH₀_holo hH₀_real χ
  · intro hall
    rcases hall χ₀ with ⟨H₀, hH₀_holo, hH₀_real, _huniq⟩
    refine ⟨H₀, hH₀_holo, ?_⟩
    intro t ht
    rw [hH₀_real t ht]
    exact schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      χ₀ h hh_pos t ht

/-- Spectral/Laplace sufficient criterion for the normalized-center two-point
admissible witness shell. If one normalized center cutoff `χ₀` produces the
real-axis `ξ`-shift witness as the Laplace transform of a finite measure
supported in `[0, ∞)`, then the full canonical holomorphic continuation exists
on the admissible witness shell for every center cutoff `χ`, and is unique on
the right half-plane.

This is the blocker-facing spectral form of the remaining `k = 2` `E -> R`
gap: the missing input is no longer a vague holomorphic construction, but one
normalized admissible slice with a nonnegative Laplace representation. -/
theorem exists_twoPoint_xiShiftWitness_holomorphicValue_of_laplace_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    (hμ_supp : μ (Set.Iio 0) = 0)
    (hμ_real : ∀ t : ℝ, 0 < t →
      ∫ s : ℝ, Complex.exp (-(t : ℂ) * (s : ℂ)) ∂μ =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) :
    ∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            ∫ y : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                ((t : ℂ) * Complex.I)) *
                (χ (y 0) * h (y 1))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              ∫ y : NPointDomain d 2,
                Ψ (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                  ((t : ℂ) * Complex.I)) *
                  (χ (y 0) * h (y 1))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  have hcenter :
      ∃ H₀ : ℂ → ℂ,
        DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H₀ (t : ℂ) =
            ∫ y : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                ((t : ℂ) * Complex.I)) *
                (χ₀ (y 0) * h (y 1))) := by
    refine ⟨fun z : ℂ => ∫ s : ℝ, Complex.exp (-z * (s : ℂ)) ∂μ, ?_, ?_⟩
    · exact SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport μ hμ_supp
    · exact hμ_real
  exact
    (exists_twoPoint_xiShiftWitness_holomorphicValue_iff_centerValue
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀).mp hcenter

/-- Schwinger-side corollary of the previous spectral/Laplace criterion. A
nonnegative Laplace representation for one normalized admissible two-point
witness slice already yields the canonical right-half-plane continuation of the
shifted two-point Schwinger family for every center cutoff `χ`. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_laplace_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    (hμ_supp : μ (Set.Iio 0) = 0)
    (hμ_real : ∀ t : ℝ, 0 < t →
      ∫ s : ℝ, Complex.exp (-(t : ℂ) * (s : ℂ)) ∂μ =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) :
    ∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ
                  (SCV.translateSchwartz (- timeShiftVec d t) h)))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              OS.S 2
                (ZeroDiagonalSchwartz.ofClassical
                  (twoPointDifferenceLift χ
                    (SCV.translateSchwartz (- timeShiftVec d t) h)))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  have hcenter :
      ∃ H₀ : ℂ → ℂ,
        DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H₀ (t : ℂ) =
            ∫ y : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                ((t : ℂ) * Complex.I)) *
                (χ₀ (y 0) * h (y 1))) := by
    refine ⟨fun z : ℂ => ∫ s : ℝ, Complex.exp (-z * (s : ℂ)) ∂μ, ?_, ?_⟩
    · exact SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport μ hμ_supp
    · exact hμ_real
  exact
    (exists_twoPointDifferenceLift_timeShift_holomorphicValue_iff_centerValue
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀).mp hcenter

/-- Polarized spectral/Laplace sufficient criterion for the normalized-center
two-point admissible witness shell. This is the off-diagonal version of
`exists_twoPoint_xiShiftWitness_holomorphicValue_of_laplace_centerValue`: if a
single normalized center cutoff `χ₀` produces the real-axis `ξ`-shift witness
as the polarization combination of four nonnegative Laplace transforms, then
the full canonical right-half-plane continuation exists on the admissible
witness shell for every center cutoff `χ`.

This matches the actual semigroup spectral input more closely than a single
positive measure, since off-diagonal matrix elements arise by polarization of
diagonal positive spectral measures. -/
theorem exists_twoPoint_xiShiftWitness_holomorphicValue_of_polarizedLaplace_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (μ1 μ2 μ3 μ4 : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ1] [MeasureTheory.IsFiniteMeasure μ2]
    [MeasureTheory.IsFiniteMeasure μ3] [MeasureTheory.IsFiniteMeasure μ4]
    (hμ1_supp : μ1 (Set.Iio 0) = 0)
    (hμ2_supp : μ2 (Set.Iio 0) = 0)
    (hμ3_supp : μ3 (Set.Iio 0) = 0)
    (hμ4_supp : μ4 (Set.Iio 0) = 0)
    (hμ_real : ∀ t : ℝ, 0 < t →
      (1 / 4 : ℂ) * (
          ∫ s : ℝ, Complex.exp (-(t : ℂ) * (s : ℂ)) ∂μ1
            - ∫ s : ℝ, Complex.exp (-(t : ℂ) * (s : ℂ)) ∂μ2
            - Complex.I * ∫ s : ℝ, Complex.exp (-(t : ℂ) * (s : ℂ)) ∂μ3
            + Complex.I * ∫ s : ℝ, Complex.exp (-(t : ℂ) * (s : ℂ)) ∂μ4) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) :
    ∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            ∫ y : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                ((t : ℂ) * Complex.I)) *
                (χ (y 0) * h (y 1))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              ∫ y : NPointDomain d 2,
                Ψ (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                  ((t : ℂ) * Complex.I)) *
                  (χ (y 0) * h (y 1))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  have hcenter :
      ∃ H₀ : ℂ → ℂ,
        DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H₀ (t : ℂ) =
            ∫ y : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                ((t : ℂ) * Complex.I)) *
                (χ₀ (y 0) * h (y 1))) := by
    refine ⟨fun z : ℂ =>
      (1 / 4 : ℂ) * (
        (∫ s : ℝ, Complex.exp (-z * (s : ℂ)) ∂μ1)
          - (∫ s : ℝ, Complex.exp (-z * (s : ℂ)) ∂μ2)
          - Complex.I * (∫ s : ℝ, Complex.exp (-z * (s : ℂ)) ∂μ3)
          + Complex.I * (∫ s : ℝ, Complex.exp (-z * (s : ℂ)) ∂μ4)), ?_, ?_⟩
    · have h1 := SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport μ1 hμ1_supp
      have h2 := SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport μ2 hμ2_supp
      have h3 := SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport μ3 hμ3_supp
      have h4 := SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport μ4 hμ4_supp
      convert
        (DifferentiableOn.const_mul
          ((h1.add (DifferentiableOn.const_mul h2 (-1 : ℂ))).add
            ((DifferentiableOn.const_mul h3 (-Complex.I)).add
              (DifferentiableOn.const_mul h4 Complex.I)))
          (1 / 4 : ℂ)) using 1
      ext z
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    · exact hμ_real
  exact
    (exists_twoPoint_xiShiftWitness_holomorphicValue_iff_centerValue
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀).mp hcenter

/-- Schwinger-side corollary of the polarized spectral/Laplace criterion. A
polarization combination of four nonnegative Laplace transforms for one
normalized admissible two-point witness slice already yields the canonical
right-half-plane continuation of the shifted two-point Schwinger family for
every center cutoff `χ`. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_polarizedLaplace_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (μ1 μ2 μ3 μ4 : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ1] [MeasureTheory.IsFiniteMeasure μ2]
    [MeasureTheory.IsFiniteMeasure μ3] [MeasureTheory.IsFiniteMeasure μ4]
    (hμ1_supp : μ1 (Set.Iio 0) = 0)
    (hμ2_supp : μ2 (Set.Iio 0) = 0)
    (hμ3_supp : μ3 (Set.Iio 0) = 0)
    (hμ4_supp : μ4 (Set.Iio 0) = 0)
    (hμ_real : ∀ t : ℝ, 0 < t →
      (1 / 4 : ℂ) * (
          ∫ s : ℝ, Complex.exp (-(t : ℂ) * (s : ℂ)) ∂μ1
            - ∫ s : ℝ, Complex.exp (-(t : ℂ) * (s : ℂ)) ∂μ2
            - Complex.I * ∫ s : ℝ, Complex.exp (-(t : ℂ) * (s : ℂ)) ∂μ3
            + Complex.I * ∫ s : ℝ, Complex.exp (-(t : ℂ) * (s : ℂ)) ∂μ4) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) :
    ∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ
                  (SCV.translateSchwartz (- timeShiftVec d t) h)))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              OS.S 2
                (ZeroDiagonalSchwartz.ofClassical
                  (twoPointDifferenceLift χ
                    (SCV.translateSchwartz (- timeShiftVec d t) h)))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  have hcenter :
      ∃ H₀ : ℂ → ℂ,
        DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H₀ (t : ℂ) =
            ∫ y : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                ((t : ℂ) * Complex.I)) *
                (χ₀ (y 0) * h (y 1))) := by
    refine ⟨fun z : ℂ =>
      (1 / 4 : ℂ) * (
        (∫ s : ℝ, Complex.exp (-z * (s : ℂ)) ∂μ1)
          - (∫ s : ℝ, Complex.exp (-z * (s : ℂ)) ∂μ2)
          - Complex.I * (∫ s : ℝ, Complex.exp (-z * (s : ℂ)) ∂μ3)
          + Complex.I * (∫ s : ℝ, Complex.exp (-z * (s : ℂ)) ∂μ4)), ?_, ?_⟩
    · have h1 := SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport μ1 hμ1_supp
      have h2 := SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport μ2 hμ2_supp
      have h3 := SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport μ3 hμ3_supp
      have h4 := SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport μ4 hμ4_supp
      convert
        (DifferentiableOn.const_mul
          ((h1.add (DifferentiableOn.const_mul h2 (-1 : ℂ))).add
            ((DifferentiableOn.const_mul h3 (-Complex.I)).add
              (DifferentiableOn.const_mul h4 Complex.I)))
          (1 / 4 : ℂ)) using 1
      ext z
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    · exact hμ_real
  exact
    (exists_twoPointDifferenceLift_timeShift_holomorphicValue_iff_centerValue
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀).mp hcenter

/-- Semigroup spectral sufficient criterion for the normalized-center two-point
admissible witness shell. If one normalized center cutoff `χ₀` produces the
real-axis `ξ`-shift witness as the restriction of one explicit off-diagonal
spectral Laplace function attached to the OS time-shift semigroup, then the
full canonical right-half-plane continuation exists on the admissible witness
shell for every center cutoff `χ`.

This sharpens the remaining `k = 2` `E -> R` gap: the missing input can be
stated as matching one normalized admissible slice to a concrete semigroup
spectral object, rather than to an unspecified holomorphic function. -/
theorem exists_twoPoint_xiShiftWitness_holomorphicValue_of_semigroupSpectral_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (x y : OSHilbertSpace OS)
    (hmatch : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x y (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) :
    ∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            ∫ z : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
                ((t : ℂ) * Complex.I)) *
                (χ (z 0) * h (z 1))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              ∫ z : NPointDomain d 2,
                Ψ (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
                  ((t : ℂ) * Complex.I)) *
                  (χ (z 0) * h (z 1))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  have hcenter :
      ∃ H₀ : ℂ → ℂ,
        DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H₀ (t : ℂ) =
            ∫ z : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
                ((t : ℂ) * Complex.I)) *
                (χ₀ (z 0) * h (z 1))) := by
    refine ⟨fun z : ℂ =>
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        x y z, ?_, ?_⟩
    · exact ContinuousLinearMap.differentiableOn_selfAdjointSpectralLaplaceOffdiag
        (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
        (x := x) (y := y)
    · exact hmatch
  exact
    (exists_twoPoint_xiShiftWitness_holomorphicValue_iff_centerValue
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀).mp hcenter

/-- Schwinger-side corollary of the previous semigroup spectral criterion.
Matching one normalized admissible two-point witness slice with an explicit
off-diagonal spectral Laplace function already yields the canonical
right-half-plane continuation of the shifted two-point Schwinger family for
every center cutoff `χ`. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_semigroupSpectral_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (x y : OSHilbertSpace OS)
    (hmatch : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x y (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) :
    ∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ
                  (SCV.translateSchwartz (- timeShiftVec d t) h)))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              OS.S 2
                (ZeroDiagonalSchwartz.ofClassical
                  (twoPointDifferenceLift χ
                    (SCV.translateSchwartz (- timeShiftVec d t) h)))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  have hcenter :
      ∃ H₀ : ℂ → ℂ,
        DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H₀ (t : ℂ) =
            ∫ z : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
                ((t : ℂ) * Complex.I)) *
                (χ₀ (z 0) * h (z 1))) := by
    refine ⟨fun z : ℂ =>
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        x y z, ?_, ?_⟩
    · exact ContinuousLinearMap.differentiableOn_selfAdjointSpectralLaplaceOffdiag
        (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
        (x := x) (y := y)
    · exact hmatch
  exact
    (exists_twoPointDifferenceLift_timeShift_holomorphicValue_iff_centerValue
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀).mp hcenter

/-- Explicit witness-shell holomorphic continuation from the semigroup spectral
criterion. Once one normalized center cutoff `χ₀` matches an off-diagonal
spectral Laplace function, every center cutoff `χ` is handled by multiplying
that same spectral function by `∫ χ`. -/
theorem twoPoint_xiShiftWitness_holomorphicValue_semigroupSpectral_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ χ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (x y : OSHilbertSpace OS)
    (hmatch : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x y (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        (∫ u : SpacetimeDim d, χ u) *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            x y z)
      {z : ℂ | 0 < z.re} ∧
    ∀ t : ℝ, 0 < t →
      ((∫ u : SpacetimeDim d, χ u) *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            x y (t : ℂ)) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ (z 0) * h (z 1)) := by
  refine
    ⟨(ContinuousLinearMap.differentiableOn_selfAdjointSpectralLaplaceOffdiag
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (x := x) (y := y)).const_mul _, ?_⟩
  intro t ht
  calc
    (∫ u : SpacetimeDim d, χ u) *
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x y (t : ℂ)
      =
        (∫ u : SpacetimeDim d, χ u) *
          (∫ z : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (z 0) * h (z 1))) := by
          rw [hmatch t ht]
    _ =
        (∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) *
          ∫ u : SpacetimeDim d, χ u := by
          rw [mul_comm]
    _ =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ (z 0) * h (z 1)) := by
          symm
          exact schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            h hh_pos t ht χ₀ hχ₀ χ

/-- Explicit Schwinger-shell holomorphic continuation from the semigroup
spectral criterion. The shifted two-point Schwinger family is given by the same
off-diagonal spectral Laplace function multiplied by `∫ χ`. -/
theorem twoPointDifferenceLift_timeShift_holomorphicValue_semigroupSpectral_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ χ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (x y : OSHilbertSpace OS)
    (hmatch : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x y (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        (∫ u : SpacetimeDim d, χ u) *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            x y z)
      {z : ℂ | 0 < z.re} ∧
    ∀ t : ℝ, 0 < t →
      ((∫ u : SpacetimeDim d, χ u) *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            x y (t : ℂ)) =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
  refine
    ⟨(ContinuousLinearMap.differentiableOn_selfAdjointSpectralLaplaceOffdiag
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (x := x) (y := y)).const_mul _, ?_⟩
  intro t ht
  calc
    (∫ u : SpacetimeDim d, χ u) *
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x y (t : ℂ)
      =
        (∫ u : SpacetimeDim d, χ u) *
          (∫ z : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (z 0) * h (z 1))) := by
          rw [hmatch t ht]
    _ =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
          rw [mul_comm]
          symm
          exact schwinger_twoPointDifferenceLift_timeShift_eq_centerValue_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            h hh_pos t ht χ₀ hχ₀ χ

/-- Explicit witness-shell holomorphic continuation stated directly in terms of
the OS semigroup matrix element attached to two positive-time Borchers vectors.
If one normalized center cutoff `χ₀` matches the positive-real values of
`OSInnerProductTimeShiftHolomorphicValue F G`, then for every center cutoff
`χ` the canonical admissible-shell continuation is exactly `(∫ χ)` times that
same semigroup holomorphic matrix element. -/
theorem twoPoint_xiShiftWitness_holomorphicValue_semigroupMatrix_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ χ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (F G : PositiveTimeBorchersSequence d)
    (hmatch : ∀ t : ℝ, 0 < t →
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        (∫ u : SpacetimeDim d, χ u) *
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G z)
      {z : ℂ | 0 < z.re} ∧
    ∀ t : ℝ, 0 < t →
      ((∫ u : SpacetimeDim d, χ u) *
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G (t : ℂ)) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ (z 0) * h (z 1)) := by
  have hmatchSpec : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
          (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1)) := by
    intro t ht
    rw [← OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
      (d := d) (OS := OS) (lgc := lgc) F G (t : ℂ) (by simpa using ht)]
    exact hmatch t ht
  rcases twoPoint_xiShiftWitness_holomorphicValue_semigroupSpectral_centerValue
      (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ χ hχ₀
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
      (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
      hmatchSpec with ⟨hHspec_holo, hHspec_real⟩
  have hEqOn :
      Set.EqOn
        (fun z : ℂ =>
          (∫ u : SpacetimeDim d, χ u) *
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G z)
        (fun z : ℂ =>
          (∫ u : SpacetimeDim d, χ u) *
            ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
              (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
              (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)) z)
        {z : ℂ | 0 < z.re} := by
    intro z hz
    dsimp
    simpa using congrArg
      (fun w : ℂ => (∫ u : SpacetimeDim d, χ u) * w)
      (OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
        (d := d) (OS := OS) (lgc := lgc) F G z hz)
  refine ⟨hHspec_holo.congr hEqOn.symm, ?_⟩
  intro t ht
  calc
    (∫ u : SpacetimeDim d, χ u) *
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G (t : ℂ)
      =
        (∫ u : SpacetimeDim d, χ u) *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
            (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
            (t : ℂ) := by
          rw [OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
            (d := d) (OS := OS) (lgc := lgc) F G (t : ℂ) (by simpa using ht)]
    _ =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ (z 0) * h (z 1)) := hHspec_real t ht

/-- Schwinger-shell version of the previous semigroup matrix-element formula.
Matching one normalized admissible slice with the positive-real values of
`OSInnerProductTimeShiftHolomorphicValue F G` yields the canonical shifted
two-point Schwinger continuation for every center cutoff `χ`. -/
theorem twoPointDifferenceLift_timeShift_holomorphicValue_semigroupMatrix_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ χ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (F G : PositiveTimeBorchersSequence d)
    (hmatch : ∀ t : ℝ, 0 < t →
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        (∫ u : SpacetimeDim d, χ u) *
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G z)
      {z : ℂ | 0 < z.re} ∧
    ∀ t : ℝ, 0 < t →
      ((∫ u : SpacetimeDim d, χ u) *
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G (t : ℂ)) =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
  have hmatchSpec : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
          (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1)) := by
    intro t ht
    rw [← OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
      (d := d) (OS := OS) (lgc := lgc) F G (t : ℂ) (by simpa using ht)]
    exact hmatch t ht
  rcases twoPointDifferenceLift_timeShift_holomorphicValue_semigroupSpectral_centerValue
      (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ χ hχ₀
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
      (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
      hmatchSpec with ⟨hHspec_holo, hHspec_real⟩
  have hEqOn :
      Set.EqOn
        (fun z : ℂ =>
          (∫ u : SpacetimeDim d, χ u) *
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G z)
        (fun z : ℂ =>
          (∫ u : SpacetimeDim d, χ u) *
            ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
              (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
              (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)) z)
        {z : ℂ | 0 < z.re} := by
    intro z hz
    dsimp
    simpa using congrArg
      (fun w : ℂ => (∫ u : SpacetimeDim d, χ u) * w)
      (OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
        (d := d) (OS := OS) (lgc := lgc) F G z hz)
  refine ⟨hHspec_holo.congr hEqOn.symm, ?_⟩
  intro t ht
  calc
    (∫ u : SpacetimeDim d, χ u) *
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G (t : ℂ)
      =
        (∫ u : SpacetimeDim d, χ u) *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
            (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
            (t : ℂ) := by
          rw [OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
            (d := d) (OS := OS) (lgc := lgc) F G (t : ℂ) (by simpa using ht)]
    _ =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := hHspec_real t ht

/-- Canonicality of the explicit semigroup spectral formula on the admissible
two-point `ξ`-shift witness shell. Any holomorphic continuation with the
correct positive-real witness values must agree with the explicit spectral
off-diagonal function multiplied by `∫ χ`. -/
theorem twoPoint_xiShiftWitness_holomorphicValue_eq_semigroupSpectral_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ χ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (x y : OSHilbertSpace OS)
    (H : ℂ → ℂ)
    (hH_holo : DifferentiableOn ℂ H {z : ℂ | 0 < z.re})
    (hH_real : ∀ t : ℝ, 0 < t →
      H (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ (z 0) * h (z 1)))
    (hmatch : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x y (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) :
    Set.EqOn H
      (fun z : ℂ =>
        (∫ u : SpacetimeDim d, χ u) *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            x y z)
      {z : ℂ | 0 < z.re} := by
  rcases twoPoint_xiShiftWitness_holomorphicValue_semigroupSpectral_centerValue
      (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ χ hχ₀ x y hmatch with ⟨hHspec_holo, hHspec_real⟩
  exact twoPoint_xiShiftWitness_holomorphicValue_eq_of_positiveSupport
    (d := d) (Ψ := Ψ) h χ H
    (fun z : ℂ =>
      (∫ u : SpacetimeDim d, χ u) *
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x y z)
    hH_holo hHspec_holo hH_real hHspec_real

/-- Canonicality of the explicit semigroup spectral formula on the admissible
shifted two-point Schwinger shell. Any holomorphic continuation with the
correct positive-real Schwinger values must agree with the explicit spectral
off-diagonal function multiplied by `∫ χ`. -/
theorem twoPointDifferenceLift_timeShift_holomorphicValue_eq_semigroupSpectral_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ χ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (x y : OSHilbertSpace OS)
    (H : ℂ → ℂ)
    (hH_holo : DifferentiableOn ℂ H {z : ℂ | 0 < z.re})
    (hH_real : ∀ t : ℝ, 0 < t →
      H (t : ℂ) =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))))
    (hmatch : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x y (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) :
    Set.EqOn H
      (fun z : ℂ =>
        (∫ u : SpacetimeDim d, χ u) *
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            x y z)
      {z : ℂ | 0 < z.re} := by
  rcases twoPointDifferenceLift_timeShift_holomorphicValue_semigroupSpectral_centerValue
      (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ χ hχ₀ x y hmatch with ⟨hHspec_holo, hHspec_real⟩
  exact twoPointDifferenceLift_timeShift_holomorphicValue_eq_of_positiveSupport
    (d := d) (OS := OS) h χ H
    (fun z : ℂ =>
      (∫ u : SpacetimeDim d, χ u) *
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x y z)
    hH_holo hHspec_holo hH_real hHspec_real

/-- Concrete semigroup spectral sufficient criterion on the one-point/product
shell. If the explicit off-diagonal spectral Laplace function attached to the
OS time-shift semigroup and the product-shell pair `(χ₀, g)` matches the
normalized admissible center/difference `ξ`-shift witness for `(χ₀, h)` on the
positive real axis, then the canonical holomorphic continuation exists on the
admissible positive-time witness shell for every center cutoff `χ`.

This packages the new semigroup spectral bridge on the exact simple-tensor
shell already used by the OS holomorphic construction, so the remaining
`k = 2` gap is one fully explicit real-axis matching problem. -/
theorem exists_twoPoint_xiShiftWitness_holomorphicValue_of_semigroupProductShell_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (χ₀ g h : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hmatch : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                  hχ₀_pos⟧)) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (onePointToFin1CLM d g : SchwartzNPoint d 1)
                  hg_pos⟧)) : OSHilbertSpace OS))
          (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) :
    ∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            ∫ z : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
                ((t : ℂ) * Complex.I)) *
                (χ (z 0) * h (z 1))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              ∫ z : NPointDomain d 2,
                Ψ (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
                  ((t : ℂ) * Complex.I)) *
                  (χ (z 0) * h (z 1))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  exact
    exists_twoPoint_xiShiftWitness_holomorphicValue_of_semigroupSpectral_centerValue
      (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
              hχ₀_pos⟧)) : OSHilbertSpace OS))
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d g : SchwartzNPoint d 1)
              hg_pos⟧)) : OSHilbertSpace OS))
      hmatch

/-- Schwinger-side corollary of the previous one-point/product-shell semigroup
spectral criterion. Matching the spectral off-diagonal function for the simple
pair `(χ₀, g)` with the normalized admissible center/difference slice for
`(χ₀, h)` already yields the canonical right-half-plane continuation of the
shifted two-point Schwinger family for every center cutoff `χ`. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_semigroupProductShell_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (χ₀ g h : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hmatch : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                  hχ₀_pos⟧)) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (onePointToFin1CLM d g : SchwartzNPoint d 1)
                  hg_pos⟧)) : OSHilbertSpace OS))
          (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1))) :
    ∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ
                  (SCV.translateSchwartz (- timeShiftVec d t) h)))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              OS.S 2
                (ZeroDiagonalSchwartz.ofClassical
                  (twoPointDifferenceLift χ
                    (SCV.translateSchwartz (- timeShiftVec d t) h)))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  exact
    exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_semigroupSpectral_centerValue
      (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
              hχ₀_pos⟧)) : OSHilbertSpace OS))
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d g : SchwartzNPoint d 1)
              hg_pos⟧)) : OSHilbertSpace OS))
      hmatch

/-- Concrete sufficient criterion for the remaining two-point holomorphic
existence problem. If one can find a positive-time compact-support product-shell
test `g` whose semigroup-side holomorphic family has the same positive-real
values as the normalized admissible center/difference `ξ`-shift witness for a
single normalized center cutoff `χ₀`, then the full canonical holomorphic
continuation exists on the admissible positive-time shell for every center
cutoff `χ`. So the unresolved `k = 2` gap can be reduced to one explicit
real-axis matching problem. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_productShell_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (χ₀ g h : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hmatch : ∀ t : ℝ, 0 < t →
      ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (y i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * g (y 1)) =
      ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) :
    ∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ
                  (SCV.translateSchwartz (- timeShiftVec d t) h)))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
        (∀ t : ℝ, 0 < t →
          H' (t : ℂ) =
              OS.S 2
                (ZeroDiagonalSchwartz.ofClassical
                  (twoPointDifferenceLift χ
                    (SCV.translateSchwartz (- timeShiftVec d t) h)))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  have hmatchSpec : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                  hχ₀_pos⟧)) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (onePointToFin1CLM d g : SchwartzNPoint d 1)
                  hg_pos⟧)) : OSHilbertSpace OS))
          (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1)) := by
    intro t ht
    calc
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                  hχ₀_pos⟧)) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (onePointToFin1CLM d g : SchwartzNPoint d 1)
                  hg_pos⟧)) : OSHilbertSpace OS))
          (t : ℂ)
        = ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (y i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (y 0) * g (y 1)) := by
            exact selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
              (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
              χ₀ g hχ₀_pos hg_pos hg_compact t ht
      _ = ∫ z : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (z 0) * h (z 1)) := hmatch t ht
  exact
    exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_semigroupProductShell_centerValue
      (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      χ₀ g h hχ₀_pos hg_pos hh_pos hχ₀ hmatchSpec

/-- Witness-shell version of the previous sufficient criterion. If one
positive-time compact-support product-shell test matches the normalized
admissible `ξ`-shift witness on the real axis for a single normalized center
cutoff `χ₀`, then the canonical holomorphic continuation exists on the
admissible positive-time witness shell for every center cutoff `χ`, and is
unique on the right half-plane. -/
theorem exists_twoPoint_xiShiftWitness_holomorphicValue_of_productShell_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (χ₀ g h : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hmatch : ∀ t : ℝ, 0 < t →
      ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (y i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * g (y 1)) =
      ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) :
    ∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            ∫ y : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                ((t : ℂ) * Complex.I)) *
                (χ (y 0) * h (y 1))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              ∫ y : NPointDomain d 2,
                Ψ (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                  ((t : ℂ) * Complex.I)) *
                  (χ (y 0) * h (y 1))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  have hmatchSpec : ∀ t : ℝ, 0 < t →
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                  hχ₀_pos⟧)) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (onePointToFin1CLM d g : SchwartzNPoint d 1)
                  hg_pos⟧)) : OSHilbertSpace OS))
          (t : ℂ) =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (z 0) * h (z 1)) := by
    intro t ht
    calc
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                  hχ₀_pos⟧)) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (onePointToFin1CLM d g : SchwartzNPoint d 1)
                  hg_pos⟧)) : OSHilbertSpace OS))
          (t : ℂ)
        = ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (y i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (y 0) * g (y 1)) := by
            exact selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
              (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
              χ₀ g hχ₀_pos hg_pos hg_compact t ht
      _ = ∫ z : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (z 0) * h (z 1)) := hmatch t ht
  exact
    exists_twoPoint_xiShiftWitness_holomorphicValue_of_semigroupProductShell_centerValue
      (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      χ₀ g h hχ₀_pos hg_pos hh_pos hχ₀ hmatchSpec
