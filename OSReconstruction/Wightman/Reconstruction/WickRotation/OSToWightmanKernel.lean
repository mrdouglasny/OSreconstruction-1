 /-
 Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
 Released under Apache 2.0 license.
 Authors: Michael Douglas, ModularPhysics Contributors
 -/
import OSReconstruction.SCV.Polydisc
import OSReconstruction.vNA.MeasureTheory.SpectralIntegral
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.SCV.SeparatelyAnalytic

/-!
# OS to Wightman Kernel Assembly Infrastructure

This file begins the operator-valued kernel assembly route for the `E'→R'`
base-step blocker. The key input is the complex semigroup
`osTimeShiftHilbertComplex`, which extends the positive OS semigroup from real
times to the right half-plane.

The first substantive theorem here is the two-layer interleaved sandwich:

`(z₀, z₁) ↦ ⟪x, T(z₀) A T(z₁) y⟫`

It is jointly holomorphic on the product right half-plane once the scalar matrix
elements of `T(z)` are holomorphic and `T(z)` is operator-norm continuous.

This is the first production step toward the full interleaved kernel `G`
required by `schwinger_continuation_base_step`.
-/

open scoped Classical NNReal Topology
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The product right half-plane in `k` complex variables. -/
def productRightHalfPlane (k : ℕ) : Set (Fin k → ℂ) :=
  {z | ∀ i : Fin k, 0 < (z i).re}

theorem isOpen_productRightHalfPlane (k : ℕ) :
    IsOpen (productRightHalfPlane k) := by
  simp only [productRightHalfPlane, Set.setOf_forall]
  exact isOpen_iInter_of_finite (fun i : Fin k =>
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply i)))

private theorem sandwich_two_layer_continuousOn
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℂ → H →L[ℂ] H)
    (hG_cont : ContinuousOn G {z : ℂ | 0 < z.re})
    (A : H →L[ℂ] H) (x y : H) :
    ContinuousOn
      (fun w : Fin 2 → ℂ => @inner ℂ H _ x (G (w 0) (A (G (w 1) y))))
      (productRightHalfPlane 2) := by
  have hG1 : ContinuousOn (fun w : Fin 2 → ℂ => G (w 1)) (productRightHalfPlane 2) :=
    hG_cont.comp (continuous_apply 1).continuousOn (fun w hw => hw 1)
  have hG1y : ContinuousOn (fun w : Fin 2 → ℂ => G (w 1) y) (productRightHalfPlane 2) :=
    (ContinuousLinearMap.apply ℂ H y).continuous.comp_continuousOn hG1
  have hAG1y : ContinuousOn (fun w : Fin 2 → ℂ => A (G (w 1) y)) (productRightHalfPlane 2) :=
    A.continuous.comp_continuousOn hG1y
  have hG0 : ContinuousOn (fun w : Fin 2 → ℂ => G (w 0)) (productRightHalfPlane 2) :=
    hG_cont.comp (continuous_apply 0).continuousOn (fun w hw => hw 0)
  have heval : ContinuousOn
      (fun w : Fin 2 → ℂ => G (w 0) (A (G (w 1) y)))
      (productRightHalfPlane 2) := hG0.clm_apply hAG1y
  exact (innerSL ℂ x).continuous.comp_continuousOn heval

private theorem sandwich_two_layer_sep_holo_z0
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℂ → H →L[ℂ] H)
    (hG_holo : ∀ x y : H,
      DifferentiableOn ℂ (fun z => @inner ℂ H _ x (G z y)) {z : ℂ | 0 < z.re})
    (A : H →L[ℂ] H) (x y : H)
    (z₁ : ℂ) :
    DifferentiableOn ℂ
      (fun z₀ => @inner ℂ H _ x (G z₀ (A (G z₁ y))))
      {z : ℂ | 0 < z.re} :=
  hG_holo x (A (G z₁ y))

private theorem sandwich_two_layer_sep_holo_z1
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℂ → H →L[ℂ] H)
    (hG_holo : ∀ x y : H,
      DifferentiableOn ℂ (fun z => @inner ℂ H _ x (G z y)) {z : ℂ | 0 < z.re})
    (A : H →L[ℂ] H) (x y : H)
    (z₀ : ℂ) :
    DifferentiableOn ℂ
      (fun z₁ => @inner ℂ H _ x (G z₀ (A (G z₁ y))))
      {z : ℂ | 0 < z.re} := by
  let L : H →L[ℂ] ℂ := (innerSL ℂ x).comp ((G z₀).comp A)
  let u : H := (InnerProductSpace.toDual ℂ H).symm L
  have hEq :
      (fun z₁ => @inner ℂ H _ x (G z₀ (A (G z₁ y)))) =
        fun z₁ => @inner ℂ H _ u (G z₁ y) := by
    funext z₁
    have hdual :
        @inner ℂ H _ u (G z₁ y) = L (G z₁ y) := by
      simpa [u, L] using
        (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := H)
          (x := G z₁ y) (y := L))
    simpa [L] using hdual.symm
  rw [hEq]
  exact hG_holo u y

private theorem sandwich_two_layer_jointly_holomorphic
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℂ → H →L[ℂ] H)
    (hG_holo : ∀ x y : H,
      DifferentiableOn ℂ (fun z => @inner ℂ H _ x (G z y)) {z : ℂ | 0 < z.re})
    (hG_cont : ContinuousOn G {z : ℂ | 0 < z.re})
    (A : H →L[ℂ] H) (x y : H) :
    DifferentiableOn ℂ
      (fun w : Fin 2 → ℂ => @inner ℂ H _ x (G (w 0) (A (G (w 1) y))))
      (productRightHalfPlane 2) := by
  apply SCV.osgood_lemma (isOpen_productRightHalfPlane 2)
  · exact sandwich_two_layer_continuousOn G hG_cont A x y
  · intro w hw j
    fin_cases j
    · have hEq :
        (fun z => @inner ℂ H _ x
          (G (Function.update w ⟨0, by omega⟩ z 0)
            (A (G (Function.update w ⟨0, by omega⟩ z 1) y)))) =
          (fun z => @inner ℂ H _ x (G z (A (G (w 1) y)))) := by
            funext z
            simp [Function.update_self, Function.update_of_ne]
      rw [hEq]
      exact (sandwich_two_layer_sep_holo_z0 G hG_holo A x y (w 1)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hw 0))
    · have hEq :
        (fun z => @inner ℂ H _ x
          (G (Function.update w ⟨1, by omega⟩ z 0)
            (A (G (Function.update w ⟨1, by omega⟩ z 1) y)))) =
          (fun z => @inner ℂ H _ x (G (w 0) (A (G z y)))) := by
            funext z
            simp [Function.update_self, Function.update_of_ne]
      rw [hEq]
      exact (sandwich_two_layer_sep_holo_z1 G hG_holo A x y (w 0)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hw 1))

/-- The two-layer interleaved OS sandwich built from the complex semigroup is jointly
holomorphic on the product right half-plane. -/
theorem differentiableOn_osTimeShiftHilbertComplex_twoLayerSandwich
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (A : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS)
    (x y : OSHilbertSpace OS) :
    DifferentiableOn ℂ
      (fun w : Fin 2 → ℂ =>
        @inner ℂ (OSHilbertSpace OS) _ x
          ((osTimeShiftHilbertComplex (d := d) OS lgc (w 0))
            (A ((osTimeShiftHilbertComplex (d := d) OS lgc (w 1)) y))))
      (productRightHalfPlane 2) := by
  refine sandwich_two_layer_jointly_holomorphic
    (G := osTimeShiftHilbertComplex (d := d) OS lgc)
    ?_ ?_ A x y
  · intro u v
    exact differentiableOn_inner_osTimeShiftHilbertComplex (d := d) OS lgc u v
  · exact continuousOn_osTimeShiftHilbertComplex (d := d) OS lgc

/-- If the middle insertion is obtained from a bounded sesquilinear form by the
Riesz construction `sesquilinearToOperator`, the resulting two-layer OS sandwich
is jointly holomorphic on the product right half-plane.

This is the exact bridge needed for the direct operator-construction route in the
OS II base step: once the Schwinger product-test sesquilinear form is proved
bounded, the holomorphicity machinery is already available. -/
theorem differentiableOn_osTimeShiftHilbertComplex_twoLayerSandwich_of_boundedSesq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (B : OSHilbertSpace OS → OSHilbertSpace OS → ℂ)
    (hB_linear_right : ∀ x, IsLinearMap ℂ (B x))
    (hB_conj_linear_left :
      ∀ y c x₁ x₂, B (c • x₁ + x₂) y = starRingEnd ℂ c * B x₁ y + B x₂ y)
    (hB_bounded : ∃ C : ℝ, ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖)
    (x y : OSHilbertSpace OS) :
    DifferentiableOn ℂ
      (fun w : Fin 2 → ℂ =>
        @inner ℂ (OSHilbertSpace OS) _ x
          ((osTimeShiftHilbertComplex (d := d) OS lgc (w 0))
            ((sesquilinearToOperator B hB_linear_right hB_conj_linear_left hB_bounded)
              ((osTimeShiftHilbertComplex (d := d) OS lgc (w 1)) y))))
      (productRightHalfPlane 2) := by
  simpa using differentiableOn_osTimeShiftHilbertComplex_twoLayerSandwich
    (d := d) OS lgc
    (A := sesquilinearToOperator B hB_linear_right hB_conj_linear_left hB_bounded)
    x y

private theorem continuousOn_clm_apply_rightHalfPlane
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℂ → H →L[ℂ] H)
    (hG_cont : ContinuousOn G {z : ℂ | 0 < z.re})
    (y : H) :
    ContinuousOn (fun z : ℂ => G z y) {z : ℂ | 0 < z.re} :=
  (ContinuousLinearMap.apply ℂ H y).continuous.comp_continuousOn hG_cont

private theorem differentiableOn_clm_apply_rightHalfPlane
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℂ → H →L[ℂ] H)
    (hG_holo : DifferentiableOn ℂ G {z : ℂ | 0 < z.re})
    (y : H) :
    DifferentiableOn ℂ (fun z : ℂ => G z y) {z : ℂ | 0 < z.re} :=
  (ContinuousLinearMap.apply ℂ H y).differentiable.comp_differentiableOn hG_holo

/-- Recursively apply a CLM-valued semigroup `G` interleaved with bounded operators. -/
private def interleavedRightVec
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (G : ℂ → H →L[ℂ] H) :
    ∀ {n : ℕ}, (Fin n → H →L[ℂ] H) → (Fin (n + 1) → ℂ) → H → H
  | 0, _, z, y => G (z 0) y
  | n + 1, As, z, y =>
      G (z 0)
        (As 0
          (interleavedRightVec G (fun i : Fin n => As i.succ)
            (fun i : Fin (n + 1) => z i.succ) y))

/-- Scalar matrix element of the recursive interleaved sandwich. -/
private def interleavedSandwich
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (G : ℂ → H →L[ℂ] H) {n : ℕ} (As : Fin n → H →L[ℂ] H)
    (x y : H) (z : Fin (n + 1) → ℂ) : ℂ :=
  @inner ℂ H _ x (interleavedRightVec G As z y)

private theorem continuousOn_interleavedRightVec
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℂ → H →L[ℂ] H)
    (hG_cont : ContinuousOn G {z : ℂ | 0 < z.re}) :
    ∀ {n : ℕ} (As : Fin n → H →L[ℂ] H) (y : H),
      ContinuousOn (fun z : Fin (n + 1) → ℂ => interleavedRightVec G As z y)
        (productRightHalfPlane (n + 1))
  | 0, _, y => by
      have hG0 : ContinuousOn (fun z : Fin 1 → ℂ => G (z 0)) (productRightHalfPlane 1) :=
        hG_cont.comp (continuous_apply 0).continuousOn (fun z hz => hz 0)
      exact hG0.clm_apply continuousOn_const
  | n + 1, As, y => by
      let tailMap : (Fin (n + 2) → ℂ) → (Fin (n + 1) → ℂ) := fun z i => z i.succ
      have hTail :
          ContinuousOn
            (fun z : Fin (n + 2) → ℂ =>
              interleavedRightVec G (fun i : Fin n => As i.succ) (tailMap z) y)
            (productRightHalfPlane (n + 2)) :=
        (continuousOn_interleavedRightVec G hG_cont (fun i : Fin n => As i.succ) y).comp
          (continuous_pi fun i => continuous_apply i.succ).continuousOn
          (fun z hz i => hz i.succ)
      have hLeft :
          ContinuousOn
            (fun z : Fin (n + 2) → ℂ =>
              As 0
                (interleavedRightVec G (fun i : Fin n => As i.succ) (tailMap z) y))
            (productRightHalfPlane (n + 2)) :=
        (As 0).continuous.comp_continuousOn hTail
      have hG0 :
          ContinuousOn (fun z : Fin (n + 2) → ℂ => G (z 0))
            (productRightHalfPlane (n + 2)) :=
        hG_cont.comp (continuous_apply 0).continuousOn (fun z hz => hz 0)
      exact hG0.clm_apply hLeft

private theorem continuousOn_interleavedSandwich
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℂ → H →L[ℂ] H)
    (hG_cont : ContinuousOn G {z : ℂ | 0 < z.re})
    {n : ℕ} (As : Fin n → H →L[ℂ] H) (x y : H) :
    ContinuousOn (fun z : Fin (n + 1) → ℂ => interleavedSandwich G As x y z)
      (productRightHalfPlane (n + 1)) := by
  exact (innerSL ℂ x).continuous.comp_continuousOn
    (continuousOn_interleavedRightVec G hG_cont As y)

/-- A recursively interleaved sandwich built from a CLM-valued holomorphic semigroup is
jointly holomorphic on the product right half-plane. -/
private theorem differentiableOn_interleavedSandwich
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ℂ → H →L[ℂ] H)
    (hG_holo : ∀ x y : H,
      DifferentiableOn ℂ (fun z => @inner ℂ H _ x (G z y)) {z : ℂ | 0 < z.re})
    (hG_cont : ContinuousOn G {z : ℂ | 0 < z.re})
    : ∀ {n : ℕ} (As : Fin n → H →L[ℂ] H) (x y : H),
    DifferentiableOn ℂ (fun z : Fin (n + 1) → ℂ => interleavedSandwich G As x y z)
      (productRightHalfPlane (n + 1))
  | 0, As, x, y => by
      apply SCV.osgood_lemma (isOpen_productRightHalfPlane 1)
      · exact continuousOn_interleavedSandwich G hG_cont As x y
      · intro z hz j
        have hj : j = 0 := by
          apply Fin.ext
          omega
        subst hj
        let baseF : (Fin 1 → ℂ) → ℂ :=
          fun z' => @inner ℂ H _ x (@interleavedRightVec H _ _ G 0 As z' y)
        change DifferentiableAt ℂ (fun w => baseF (Function.update z 0 w)) (z 0)
        have hEq : (fun w => baseF (Function.update z 0 w)) = fun w => @inner ℂ H _ x (G w y) := by
          funext w
          simp [baseF, interleavedRightVec]
        rw [hEq]
        exact (hG_holo x y (z 0) (hz 0)).differentiableAt
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hz 0))
  | n + 1, As, x, y => by
      apply SCV.osgood_lemma (isOpen_productRightHalfPlane (n + 2))
      · exact continuousOn_interleavedSandwich G hG_cont As x y
      · intro z hz j
        let tailMap : (Fin (n + 2) → ℂ) → (Fin (n + 1) → ℂ) := fun w i => w i.succ
        let tailz : Fin (n + 1) → ℂ := tailMap z
        have htailz : tailz ∈ productRightHalfPlane (n + 1) := fun i => hz i.succ
        obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
        · let v : H :=
            As 0 (interleavedRightVec G (fun i : Fin n => As i.succ) tailz y)
          have hEq :
              (fun w =>
                interleavedSandwich G As x y (Function.update z 0 w)) =
                fun w => @inner ℂ H _ x (G w v) := by
            funext w
            simp [interleavedSandwich, interleavedRightVec, tailMap, tailz, v]
          rw [hEq]
          exact (hG_holo x v (z 0) (hz 0)).differentiableAt
            ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hz 0))
        · let L : H →L[ℂ] ℂ := (innerSL ℂ x).comp ((G (z 0)).comp (As 0))
          let u : H := (InnerProductSpace.toDual ℂ H).symm L
          let tailF : (Fin (n + 1) → ℂ) → ℂ :=
            fun w => interleavedSandwich G (fun j : Fin n => As j.succ) u y w
          have htail_holo :
              DifferentiableOn ℂ tailF (productRightHalfPlane (n + 1)) :=
            differentiableOn_interleavedSandwich G hG_holo hG_cont
              (fun j : Fin n => As j.succ) u y
          have htail_sep :
              SCV.SeparatelyDifferentiableOn tailF (productRightHalfPlane (n + 1)) :=
            SCV.DifferentiableOn.separatelyDifferentiableOn
              (isOpen_productRightHalfPlane (n + 1)) htail_holo
          have hEq :
              (fun w =>
                interleavedSandwich G As x y (Function.update z i.succ w)) =
                fun w => tailF (Function.update tailz i w) := by
            funext w
            have htail_update :
                (fun j : Fin (n + 1) => Function.update z i.succ w j.succ) =
                  Function.update tailz i w := by
              ext j
              by_cases hji : j = i
              · subst hji
                simp [tailz, tailMap]
              · have hsucc : j.succ ≠ i.succ := by
                  intro h
                  apply hji
                  apply Fin.ext
                  exact Nat.succ.inj (congrArg Fin.val h)
                calc
                  Function.update z i.succ w j.succ = z j.succ := by
                    simp [Function.update_of_ne, hsucc]
                  _ = tailz j := by rfl
                  _ = Function.update tailz i w j := by
                    symm
                    exact Function.update_of_ne hji w tailz
            have hdual :
                @inner ℂ H _ u
                    (interleavedRightVec G (fun j : Fin n => As j.succ)
                      (Function.update tailz i w) y) =
                  L (interleavedRightVec G (fun j : Fin n => As j.succ)
                    (Function.update tailz i w) y) := by
              simpa [u, L] using
                (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := H)
                  (x := interleavedRightVec G (fun j : Fin n => As j.succ)
                    (Function.update tailz i w) y) (y := L))
            have hzero : Function.update z i.succ w 0 = z 0 := by
              have hsucc0 : (0 : Fin (n + 2)) ≠ i.succ := by
                simpa using (Fin.succ_ne_zero i).symm
              simp [Function.update_of_ne, hsucc0]
            simp only [interleavedSandwich, interleavedRightVec, tailF]
            rw [hzero, htail_update]
            simpa [L] using hdual.symm
          rw [hEq]
          exact htail_sep i tailz htailz

/-- The OS interleaved sandwich built from `osTimeShiftHilbertComplex` is jointly
holomorphic on the product right half-plane for any finite sequence of bounded
interposed operators. -/
theorem differentiableOn_osTimeShiftHilbertComplex_interleavedSandwich
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} (As : Fin n → OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS)
    (x y : OSHilbertSpace OS) :
    DifferentiableOn ℂ
      (fun z : Fin (n + 1) → ℂ =>
        interleavedSandwich (osTimeShiftHilbertComplex (d := d) OS lgc) As x y z)
      (productRightHalfPlane (n + 1)) := by
  exact differentiableOn_interleavedSandwich
    (G := osTimeShiftHilbertComplex (d := d) OS lgc)
    (hG_holo := differentiableOn_inner_osTimeShiftHilbertComplex (d := d) OS lgc)
    (hG_cont := continuousOn_osTimeShiftHilbertComplex (d := d) OS lgc)
    As x y
