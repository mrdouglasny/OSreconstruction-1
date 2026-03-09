/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.SchwartzComplete
import OSReconstruction.SCV.TubeDistributions
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Distributional Uniqueness on Tube Domains (Weak Hypothesis Version)

This file proves distributional uniqueness for holomorphic functions on tube
domains using ONLY the weak distributional boundary-value hypothesis, without
requiring `HasFourierLaplaceReprRegular`.

The key technique is **mollification**: given G holomorphic on T(C) with
distributional BV → 0, we convolve G with a Schwartz test function ψ in the
real direction. The convolution G*ψ is holomorphic on T(C), has continuous
boundary values = 0 (from the distributional BV hypothesis), and therefore
vanishes identically by the proved `distributional_uniqueness_tube_of_regular`
machinery (specifically, the 1D EOW slicing argument). Taking ψ → δ gives G = 0.

## Main Results

* `distributional_uniqueness_tube_of_zero_bv`: If G is holomorphic on T(C) and
  its distributional boundary values vanish, then G = 0 on T(C).

## References

* Vladimirov, V.S. "Methods of the Theory of Generalized Functions" (2002), §25
* Classical mollification argument for distributional boundary values
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

variable {m : ℕ}

/-! ### Schwartz Translation -/

/-- Translate a Schwartz function: `(translateSchwartz t₀ f)(x) = f(x + t₀)`.
    This is Schwartz because translation by a fixed vector preserves rapid decay. -/
def translateSchwartz (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  ⟨fun x => f (x + t₀),
   f.smooth'.comp (contDiff_id.add contDiff_const),
   fun k n => by
     obtain ⟨Ck, hCk⟩ := f.decay' k n
     obtain ⟨C0, hC0⟩ := f.decay' 0 n
     -- Chain rule: D^n (f ∘ (· + t₀)) x = D^n f (x + t₀)
     have hderiv : ∀ x, iteratedFDeriv ℝ n (fun z => f.toFun (z + t₀)) x =
         iteratedFDeriv ℝ n f.toFun (x + t₀) :=
       fun x => iteratedFDeriv_comp_add_right n t₀ x
     -- From 0-th decay: ‖D^n f(y)‖ ≤ C0 for all y
     have hC0' : ∀ y, ‖iteratedFDeriv ℝ n f.toFun y‖ ≤ C0 := by
       intro y; have := hC0 y; simp [pow_zero] at this; linarith
     -- Bound: ‖x‖ ≤ ‖x+t₀‖ + ‖t₀‖ (triangle inequality)
     -- So ‖x‖^k ≤ (‖x+t₀‖ + ‖t₀‖)^k
     -- And (a+b)^k ≤ 2^k * (a^k + b^k) for a,b ≥ 0
     refine ⟨2 ^ (k - 1) * (Ck + ‖t₀‖ ^ k * C0), fun x => ?_⟩
     show ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => f.toFun (z + t₀)) x‖ ≤ _
     rw [hderiv]
     have hnorm_x : ‖x‖ ≤ ‖x + t₀‖ + ‖t₀‖ := by
       calc ‖x‖ = ‖(x + t₀) - t₀‖ := by ring_nf
         _ ≤ ‖x + t₀‖ + ‖t₀‖ := norm_sub_le _ _
     have hnn_deriv : 0 ≤ ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ := norm_nonneg _
     calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖
         ≤ (‖x + t₀‖ + ‖t₀‖) ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ := by
           gcongr
       _ ≤ (2 ^ (k - 1) * (‖x + t₀‖ ^ k + ‖t₀‖ ^ k)) *
           ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ := by
           gcongr; exact add_pow_le (norm_nonneg _) (norm_nonneg _) k
       _ = 2 ^ (k - 1) * (‖x + t₀‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖ +
           ‖t₀‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun (x + t₀)‖) := by ring
       _ ≤ 2 ^ (k - 1) * (Ck + ‖t₀‖ ^ k * C0) := by
           gcongr
           · exact hCk (x + t₀)
           · exact hC0' (x + t₀)⟩

/-- The translate of a Schwartz function evaluates as expected. -/
@[simp]
theorem translateSchwartz_apply (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) : translateSchwartz t₀ f x = f (x + t₀) := rfl

/-- Translation on Schwartz space as a continuous linear map. -/
noncomputable def translateSchwartzCLM (t₀ : Fin m → ℝ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ := by
  let g : (Fin m → ℝ) → Fin m → ℝ := fun x => x + t₀
  have hg : g.HasTemperateGrowth := by
    fun_prop
  have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k := by
    refine ⟨1, 1 + ‖t₀‖, ?_⟩
    intro x
    have htri : ‖x‖ ≤ ‖g x‖ + ‖t₀‖ := by
      calc
        ‖x‖ = ‖(x + t₀) - t₀‖ := by simp
        _ ≤ ‖g x‖ + ‖t₀‖ := by simpa [g] using norm_sub_le (x + t₀) t₀
    have hfac : ‖g x‖ + ‖t₀‖ ≤ (1 + ‖t₀‖) * (1 + ‖g x‖) := by
      nlinarith [norm_nonneg (g x), norm_nonneg t₀]
    have hpow : (1 + ‖g x‖) ^ (1 : ℕ) = 1 + ‖g x‖ := by simp
    rw [hpow]
    exact le_trans htri hfac
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

@[simp]
theorem translateSchwartzCLM_apply (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ) :
    translateSchwartzCLM t₀ f = translateSchwartz t₀ f := by
  ext x
  rfl

/-- Reflection of a Schwartz function in the real variables. -/
def reflectSchwartz (f : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ : (Fin m → ℝ) ≃ₗᵢ[ℝ] (Fin m → ℝ)).toContinuousLinearEquiv) f

/-- The reflected Schwartz function evaluates as expected. -/
@[simp]
theorem reflectSchwartz_apply (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) : reflectSchwartz f x = f (-x) := by
  simp [reflectSchwartz]

/-- The support of a translated Schwartz function is the pullback of the original
    support under the real translation `x ↦ x + t₀`. -/
theorem mem_support_translateSchwartz_iff (t₀ : Fin m → ℝ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (x : Fin m → ℝ) :
    x ∈ Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ↔
      x + t₀ ∈ Function.support (f : (Fin m → ℝ) → ℂ) := by
  simp [translateSchwartz_apply, Function.mem_support]

/-- Support transport for translated Schwartz functions. This is the exact support
    bookkeeping needed in the mollification step of distributional EOW: if `f` is
    supported in `U`, then `translateSchwartz t₀ f` is supported in the translated
    preimage `{x | x + t₀ ∈ U}`. -/
theorem support_translateSchwartz_subset_preimage (t₀ : Fin m → ℝ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (U : Set (Fin m → ℝ))
    (hU : Function.support (f : (Fin m → ℝ) → ℂ) ⊆ U) :
    Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ⊆
      {x | x + t₀ ∈ U} := by
  intro x hx
  exact hU ((mem_support_translateSchwartz_iff t₀ f x).mp hx)

/-- A convenient open-set version of support transport: if every support point `y`
    of `f` satisfies `y - t₀ ∈ U`, then the support of `translateSchwartz t₀ f`
    is contained in `U`. This is the form needed when a compactly supported mollifier
    is translated inside a fixed real neighborhood. -/
theorem support_translateSchwartz_subset (t₀ : Fin m → ℝ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (U : Set (Fin m → ℝ))
    (hU : ∀ y ∈ Function.support (f : (Fin m → ℝ) → ℂ), y - t₀ ∈ U) :
    Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ⊆ U := by
  intro x hx
  simpa using hU (x + t₀) ((mem_support_translateSchwartz_iff t₀ f x).mp hx)

/-- If the support of a Schwartz function is compact and its translate at `t₀`
    is contained in an open set `U`, then the translated support stays inside `U`
    for all nearby centers. This is the local support-stability input needed in
    the mollifier argument for distributional edge-of-the-wedge. -/
theorem exists_mem_nhds_support_translateSchwartz_subset_of_isCompactSupport
    (t₀ : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hK_compact : IsCompact (Function.support (f : (Fin m → ℝ) → ℂ)))
    (U : Set (Fin m → ℝ)) (hU_open : IsOpen U)
    (hU : Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) ⊆ U) :
    ∃ V ∈ 𝓝 t₀, ∀ t ∈ V,
      Function.support (translateSchwartz t f : (Fin m → ℝ) → ℂ) ⊆ U := by
  let K : Set (Fin m → ℝ) := Function.support (f : (Fin m → ℝ) → ℂ)
  have hbase : ∀ y ∈ K, y - t₀ ∈ U := by
    intro y hy
    have hyt : y - t₀ ∈ Function.support (translateSchwartz t₀ f : (Fin m → ℝ) → ℂ) := by
      rw [mem_support_translateSchwartz_iff]
      simpa
    exact hU hyt
  have hloc :
      ∀ x : K,
        ∃ Vx Wx : Set (Fin m → ℝ),
          Vx ∈ 𝓝 x.1 ∧ Wx ∈ 𝓝 t₀ ∧ IsOpen Vx ∧ x.1 ∈ Vx ∧
            Vx ×ˢ Wx ⊆ {p : (Fin m → ℝ) × (Fin m → ℝ) | p.1 - p.2 ∈ U} := by
    intro x
    have hprod_mem :
        {p : (Fin m → ℝ) × (Fin m → ℝ) | p.1 - p.2 ∈ U} ∈ 𝓝 (x.1, t₀) := by
      exact (continuous_fst.sub continuous_snd).continuousAt.preimage_mem_nhds
        (hU_open.mem_nhds (hbase x.1 x.2))
    rcases mem_nhds_prod_iff.mp hprod_mem with ⟨Vx0, hVx0, Wx, hWx, hsub⟩
    refine ⟨interior Vx0, Wx, ?_, hWx, isOpen_interior, ?_, ?_⟩
    · exact isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hVx0)
    · exact mem_interior_iff_mem_nhds.mpr hVx0
    · exact Set.Subset.trans (Set.prod_mono interior_subset (Subset.rfl)) hsub
  choose V W hV_nhds hW_nhds hV_open hxV hVW using hloc
  obtain ⟨s, hscover⟩ := hK_compact.elim_finite_subcover (fun x : K => V x)
    (fun x => hV_open x) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩)
  have hN_nhds_aux : ∀ s : Finset K, (⋂ x ∈ s, W x) ∈ 𝓝 t₀ := by
    classical
    intro s
    exact (biInter_finset_mem s).2 fun x hx => hW_nhds x
  have hN_nhds : (⋂ x ∈ s, W x) ∈ 𝓝 t₀ := hN_nhds_aux s
  let N : Set (Fin m → ℝ) := ⋂ x ∈ s, W x
  refine ⟨N, hN_nhds, ?_⟩
  intro t ht z hz
  have hy : z + t ∈ K := (mem_support_translateSchwartz_iff t f z).mp hz
  have hycover : z + t ∈ ⋃ x ∈ s, V x := hscover hy
  rcases mem_iUnion.mp hycover with ⟨x, hycover⟩
  rcases mem_iUnion.mp hycover with ⟨hxs, hzV⟩
  have htW : t ∈ W x := by
    have ht' : t ∈ N := ht
    simp [N] at ht'
    exact ht' x.1 x.2 hxs
  have hpair : ((z + t), t) ∈ V x ×ˢ W x := ⟨hzV, htW⟩
  have hsub : (z + t) - t ∈ U := hVW x hpair
  simpa using hsub

/-- If a continuous linear functional vanishes on all Schwartz functions
    supported in an open set `U`, then it also vanishes on all nearby translates
    of a compactly supported Schwartz function whose translate at `t₀` is
    contained in `U`. This is the local vanishing step needed for mollified
    boundary traces in the distributional EOW argument. -/
theorem map_translateSchwartz_eq_zero_nhds_of_support_subset
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (U : Set (Fin m → ℝ)) (hT_zero : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      Function.support (φ : (Fin m → ℝ) → ℂ) ⊆ U → T φ = 0)
    (t₀ : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    (hU_open : IsOpen U)
    (hsub : Function.support (translateSchwartz t₀ ψ : (Fin m → ℝ) → ℂ) ⊆ U) :
    ∃ V ∈ 𝓝 t₀, ∀ t ∈ V, T (translateSchwartz t ψ) = 0 := by
  obtain ⟨V, hV, hVsub⟩ :=
    exists_mem_nhds_support_translateSchwartz_subset_of_isCompactSupport
      t₀ ψ hψ_compact U hU_open hsub
  refine ⟨V, hV, ?_⟩
  intro t ht
  exact hT_zero (translateSchwartz t ψ) (hVsub t ht)

private theorem iteratedFDeriv_sub_schwartz (f g : SchwartzMap (Fin m → ℝ) ℂ)
    (n : ℕ) (x : Fin m → ℝ) :
    iteratedFDeriv ℝ n (⇑(f - g)) x =
      iteratedFDeriv ℝ n (⇑f) x - iteratedFDeriv ℝ n (⇑g) x := by
  have hf : ContDiff ℝ n (⇑f) := f.smooth n
  have hg : ContDiff ℝ n (⇑g) := g.smooth n
  have hfg : (⇑(f - g) : (Fin m → ℝ) → ℂ) = (⇑f) + fun x => -(⇑g x) := by
    ext y
    simp [sub_eq_add_neg]
  have hneg : (fun x => -(⇑g x)) = -⇑g := rfl
  rw [hfg, iteratedFDeriv_add_apply hf.contDiffAt hg.neg.contDiffAt, hneg, iteratedFDeriv_neg_apply]
  simp [sub_eq_add_neg]

/-- Translation by `t • η` is continuous in the Schwartz topology when the
    translated test function has compact support. This is the exact moving-mollifier
    input needed for weak boundary-value uniqueness arguments. -/
theorem tendsto_translateSchwartz_smul_nhds_of_isCompactSupport
    (η : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    (t₀ : ℝ) :
    Tendsto (fun t : ℝ => translateSchwartz (t • η) ψ) (𝓝 t₀)
      (𝓝 (translateSchwartz (t₀ • η) ψ)) := by
  let K : Set (Fin m → ℝ) := Function.support (ψ : (Fin m → ℝ) → ℂ)
  have hK_closed : IsClosed K := hψ_compact.isClosed
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
  intro ⟨k, n⟩ ε hε
  let J : Set ℝ := Set.Icc (t₀ - 1) (t₀ + 1)
  have ht₀J : t₀ ∈ J := by
    constructor <;> linarith
  let Ktrans : Set (Fin m → ℝ) :=
    (fun p : (Fin m → ℝ) × ℝ => p.1 - p.2 • η) '' (K ×ˢ J)
  have hKtrans_compact : IsCompact Ktrans := by
    refine (hψ_compact.prod isCompact_Icc).image ?_
    exact continuous_fst.sub (continuous_snd.smul continuous_const)
  let q : (Fin m → ℝ) → ℝ := fun x => ‖x‖ ^ k
  have hq_cont : Continuous q := by
    exact continuous_norm.pow k
  obtain ⟨B, hB⟩ := hKtrans_compact.exists_bound_of_continuousOn (f := q) hq_cont.continuousOn
  let M : ℝ := max 1 B
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let H : (Fin m → ℝ) × ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun p => iteratedFDeriv ℝ n (⇑ψ) (p.1 + p.2 • η)
  have hH_cont : Continuous H := by
    let A : (Fin m → ℝ) × ℝ → Fin m → ℝ := fun p => p.1 + p.2 • η
    have hA : Continuous A := by
      exact continuous_fst.add (continuous_snd.smul continuous_const)
    exact ((ψ.smooth n).continuous_iteratedFDeriv le_rfl).comp hA
  have hH_uc : UniformContinuousOn H (Ktrans ×ˢ J) :=
    (hKtrans_compact.prod isCompact_Icc).uniformContinuousOn_of_continuous hH_cont.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp hH_uc (ε / (2 * M)) (by positivity) with
    ⟨δ, hδ, hHδ⟩
  have hJ_nhds : J ∈ 𝓝 t₀ := by
    refine Icc_mem_nhds ?_ ?_
    · linarith
    · linarith
  have hball_nhds : Metric.ball t₀ δ ∈ 𝓝 t₀ := Metric.ball_mem_nhds _ hδ
  filter_upwards [inter_mem hJ_nhds hball_nhds] with t ht
  have htJ : t ∈ J := ht.1
  have htdist : dist t t₀ < δ := ht.2
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ k n
      (translateSchwartz (t • η) ψ - translateSchwartz (t₀ • η) ψ)
      (by positivity) ?_
  intro x
  by_cases hx : x ∈ Ktrans
  · have hpair_t : (x, t) ∈ Ktrans ×ˢ J := ⟨hx, htJ⟩
    have hpair_t₀ : (x, t₀) ∈ Ktrans ×ˢ J := ⟨hx, ht₀J⟩
    have hpair_dist : dist (x, t) (x, t₀) < δ := by
      simpa [Prod.dist_eq] using htdist
    have hderiv_close :
        ‖H (x, t) - H (x, t₀)‖ < ε / (2 * M) := by
      simpa [H, dist_eq_norm] using hHδ _ hpair_t _ hpair_t₀ hpair_dist
    have hnormx : ‖x‖ ^ k ≤ M := by
      have hBx : ‖q x‖ ≤ B := hB x hx
      have hqx : ‖q x‖ = ‖x‖ ^ k := by
        simp [q]
      rw [hqx] at hBx
      exact le_trans hBx (le_max_right _ _)
    have hEq :
        iteratedFDeriv ℝ n
            (⇑(translateSchwartz (t • η) ψ - translateSchwartz (t₀ • η) ψ)) x =
          H (x, t) - H (x, t₀) := by
      have htrans_t :
          iteratedFDeriv ℝ n (⇑(translateSchwartz (t • η) ψ)) x = H (x, t) := by
        simpa [H, translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n (t • η) x)
      have htrans_t₀ :
          iteratedFDeriv ℝ n (⇑(translateSchwartz (t₀ • η) ψ)) x = H (x, t₀) := by
        simpa [H, translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n (t₀ • η) x)
      rw [iteratedFDeriv_sub_schwartz]
      rw [htrans_t, htrans_t₀]
    rw [hEq]
    have hhalf : M * (ε / (2 * M)) = ε / 2 := by
      field_simp [hMpos.ne']
    calc
      ‖x‖ ^ k * ‖H (x, t) - H (x, t₀)‖
          ≤ ‖x‖ ^ k * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_left (le_of_lt hderiv_close) (by positivity)
      _ ≤ M * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_right hnormx (by positivity)
      _ = ε / 2 := hhalf
  · have hsupport_deriv :
        Function.support (iteratedFDeriv ℝ n (⇑ψ)) ⊆ K := by
      intro y hy
      have hy' := support_iteratedFDeriv_subset (𝕜 := ℝ) (n := n) (f := ⇑ψ) hy
      simpa [K, tsupport, hK_closed.closure_eq] using hy'
    have hx_not_t : x + t • η ∉ K := by
      intro hxt
      exact hx ⟨(x + t • η, t), ⟨hxt, htJ⟩, by
        ext i
        simp⟩
    have hx_not_t₀ : x + t₀ • η ∉ K := by
      intro hxt
      exact hx ⟨(x + t₀ • η, t₀), ⟨hxt, ht₀J⟩, by
        ext i
        simp⟩
    have hzero_t :
        iteratedFDeriv ℝ n (⇑ψ) (x + t • η) = 0 := by
      by_contra hne
      exact hx_not_t (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hzero_t₀ :
        iteratedFDeriv ℝ n (⇑ψ) (x + t₀ • η) = 0 := by
      by_contra hne
      exact hx_not_t₀ (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hEq :
        iteratedFDeriv ℝ n
            (⇑(translateSchwartz (t • η) ψ - translateSchwartz (t₀ • η) ψ)) x = 0 := by
      rw [iteratedFDeriv_sub_schwartz]
      rw [show iteratedFDeriv ℝ n (⇑(translateSchwartz (t • η) ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + t • η) by
              simpa [translateSchwartz] using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n (t • η) x)]
      rw [show iteratedFDeriv ℝ n (⇑(translateSchwartz (t₀ • η) ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + t₀ • η) by
              simpa [translateSchwartz] using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n (t₀ • η) x)]
      simp [hzero_t, hzero_t₀]
    rw [hEq]
    have : (0 : ℝ) ≤ ε / 2 := by positivity
    simpa using this

/-- If `T` is a continuous linear functional on Schwartz space and `ψ` has compact
    support, then the moving-mollifier pairing `t ↦ T(translateSchwartz (t • η) ψ)`
    is continuous. This is the boundary-trace continuity input needed in the
    mollifier proof of distributional edge-of-the-wedge. -/
theorem continuous_apply_translateSchwartz_smul_of_isCompactSupport
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (η : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ))) :
    Continuous (fun t : ℝ => T (translateSchwartz (t • η) ψ)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t₀
  show Tendsto (fun t : ℝ => T (translateSchwartz (t • η) ψ)) (𝓝 t₀)
    (𝓝 (T (translateSchwartz (t₀ • η) ψ)))
  exact T.continuous.continuousAt.tendsto.comp
    (tendsto_translateSchwartz_smul_nhds_of_isCompactSupport η ψ hψ_compact t₀)

/-- Sequence-version payoff for the moving-mollifier route: if `Tₙ → 0` pointwise
    on Schwartz space and the translation centers `tₙ → t₀`, then the paired values
    `Tₙ(translateSchwartz (tₙ • η) ψ)` also tend to `0`. This is the exact way the
    Banach-Steinhaus theorem in `SchwartzComplete.lean` enters the distributional
    edge-of-the-wedge proof. -/
theorem tendsto_apply_translateSchwartz_smul_zero_of_tendsto
    {T : ℕ → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    (hT : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun n => T n f) atTop (nhds 0))
    (η : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    {u : ℕ → ℝ} {t₀ : ℝ}
    (hu : Tendsto u atTop (nhds t₀)) :
    Tendsto (fun n => T n (translateSchwartz (u n • η) ψ)) atTop (nhds 0) := by
  apply SchwartzMap.tempered_apply_tendsto_zero_of_tendsto hT
  exact (tendsto_translateSchwartz_smul_nhds_of_isCompactSupport η ψ hψ_compact t₀).comp hu

/-- Filter-version moving-mollifier payoff for the zero-limit case.

If `Tᵢ → 0` pointwise on Schwartz space along a countably generated filter `l`,
and the translation centers `uᵢ → t₀`, then the paired values
`Tᵢ(translateSchwartz (uᵢ • η) ψ)` also tend to `0`. This is the form needed
for weak boundary-value limits indexed by `nhdsWithin 0 (Set.Ioi 0)`. -/
theorem tendsto_apply_translateSchwartz_smul_zero_of_tendsto_filter
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {T : α → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    (hT : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun a => T a f) l (nhds 0))
    (η : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    {u : α → ℝ} {t₀ : ℝ}
    (hu : Tendsto u l (nhds t₀)) :
    Tendsto (fun a => T a (translateSchwartz (u a • η) ψ)) l (nhds 0) := by
  apply SchwartzMap.tempered_apply_tendsto_zero_of_tendsto_filter hT
  exact (tendsto_translateSchwartz_smul_nhds_of_isCompactSupport η ψ hψ_compact t₀).comp hu

/-- Full real-translation continuity in the Schwartz topology for compactly
    supported test functions. This is the version needed for real-direction
    tube convolution, not just the scalar `t • η` specialization. -/
theorem tendsto_translateSchwartz_nhds_of_isCompactSupport
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    (t₀ : Fin m → ℝ) :
    Tendsto (fun t : Fin m → ℝ => translateSchwartz t ψ) (𝓝 t₀)
      (𝓝 (translateSchwartz t₀ ψ)) := by
  let K : Set (Fin m → ℝ) := Function.support (ψ : (Fin m → ℝ) → ℂ)
  have hK_closed : IsClosed K := hψ_compact.isClosed
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
  intro ⟨k, n⟩ ε hε
  let J : Set (Fin m → ℝ) := Metric.closedBall t₀ 1
  have ht₀J : t₀ ∈ J := Metric.mem_closedBall_self (by positivity)
  have hJ_compact : IsCompact J := isCompact_closedBall _ _
  let Ktrans : Set (Fin m → ℝ) :=
    (fun p : (Fin m → ℝ) × (Fin m → ℝ) => p.1 - p.2) '' (K ×ˢ J)
  have hKtrans_compact : IsCompact Ktrans := by
    refine (hψ_compact.prod hJ_compact).image ?_
    exact continuous_fst.sub continuous_snd
  let q : (Fin m → ℝ) → ℝ := fun x => ‖x‖ ^ k
  have hq_cont : Continuous q := continuous_norm.pow k
  obtain ⟨B, hB⟩ :=
    hKtrans_compact.exists_bound_of_continuousOn (f := q) hq_cont.continuousOn
  let M : ℝ := max 1 B
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let H : (Fin m → ℝ) × (Fin m → ℝ) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun p => iteratedFDeriv ℝ n (⇑ψ) (p.1 + p.2)
  have hH_cont : Continuous H := by
    let A : (Fin m → ℝ) × (Fin m → ℝ) → Fin m → ℝ := fun p => p.1 + p.2
    have hA : Continuous A := continuous_fst.add continuous_snd
    exact ((ψ.smooth n).continuous_iteratedFDeriv le_rfl).comp hA
  have hH_uc : UniformContinuousOn H (Ktrans ×ˢ J) :=
    (hKtrans_compact.prod hJ_compact).uniformContinuousOn_of_continuous hH_cont.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp hH_uc (ε / (2 * M)) (by positivity) with
    ⟨δ, hδ, hHδ⟩
  have hJ_nhds : J ∈ 𝓝 t₀ := Metric.closedBall_mem_nhds _ (by positivity)
  have hball_nhds : Metric.ball t₀ δ ∈ 𝓝 t₀ := Metric.ball_mem_nhds _ hδ
  filter_upwards [inter_mem hJ_nhds hball_nhds] with t ht
  have htJ : t ∈ J := ht.1
  have htdist : dist t t₀ < δ := ht.2
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ k n (translateSchwartz t ψ - translateSchwartz t₀ ψ)
      (by positivity) ?_
  intro x
  by_cases hx : x ∈ Ktrans
  · have hpair_t : (x, t) ∈ Ktrans ×ˢ J := ⟨hx, htJ⟩
    have hpair_t₀ : (x, t₀) ∈ Ktrans ×ˢ J := ⟨hx, ht₀J⟩
    have hpair_dist : dist (x, t) (x, t₀) < δ := by
      simpa [Prod.dist_eq] using htdist
    have hderiv_close : ‖H (x, t) - H (x, t₀)‖ < ε / (2 * M) := by
      simpa [H, dist_eq_norm] using hHδ _ hpair_t _ hpair_t₀ hpair_dist
    have hnormx : ‖x‖ ^ k ≤ M := by
      have hBx : ‖q x‖ ≤ B := hB x hx
      have hqx : ‖q x‖ = ‖x‖ ^ k := by simp [q]
      rw [hqx] at hBx
      exact le_trans hBx (le_max_right _ _)
    have hEq :
        iteratedFDeriv ℝ n (⇑(translateSchwartz t ψ - translateSchwartz t₀ ψ)) x =
          H (x, t) - H (x, t₀) := by
      have htrans_t :
          iteratedFDeriv ℝ n (⇑(translateSchwartz t ψ)) x = H (x, t) := by
        simpa [H, translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n t x)
      have htrans_t₀ :
          iteratedFDeriv ℝ n (⇑(translateSchwartz t₀ ψ)) x = H (x, t₀) := by
        simpa [H, translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n t₀ x)
      rw [iteratedFDeriv_sub_schwartz, htrans_t, htrans_t₀]
    rw [hEq]
    have hhalf : M * (ε / (2 * M)) = ε / 2 := by
      field_simp [hMpos.ne']
    calc
      ‖x‖ ^ k * ‖H (x, t) - H (x, t₀)‖
          ≤ ‖x‖ ^ k * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_left (le_of_lt hderiv_close) (by positivity)
      _ ≤ M * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_right hnormx (by positivity)
      _ = ε / 2 := hhalf
  · have hsupport_deriv :
        Function.support (iteratedFDeriv ℝ n (⇑ψ)) ⊆ K := by
      intro y hy
      have hy' := support_iteratedFDeriv_subset (𝕜 := ℝ) (n := n) (f := ⇑ψ) hy
      simpa [K, tsupport, hK_closed.closure_eq] using hy'
    have hx_not_t : x + t ∉ K := by
      intro hxt
      exact hx ⟨(x + t, t), ⟨hxt, htJ⟩, by ext i; simp⟩
    have hx_not_t₀ : x + t₀ ∉ K := by
      intro hxt
      exact hx ⟨(x + t₀, t₀), ⟨hxt, ht₀J⟩, by ext i; simp⟩
    have hzero_t : iteratedFDeriv ℝ n (⇑ψ) (x + t) = 0 := by
      by_contra hne
      exact hx_not_t (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hzero_t₀ : iteratedFDeriv ℝ n (⇑ψ) (x + t₀) = 0 := by
      by_contra hne
      exact hx_not_t₀ (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hEq :
        iteratedFDeriv ℝ n (⇑(translateSchwartz t ψ - translateSchwartz t₀ ψ)) x = 0 := by
      rw [iteratedFDeriv_sub_schwartz]
      rw [show iteratedFDeriv ℝ n (⇑(translateSchwartz t ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + t) by
              simpa [translateSchwartz] using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n t x)]
      rw [show iteratedFDeriv ℝ n (⇑(translateSchwartz t₀ ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + t₀) by
              simpa [translateSchwartz] using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n t₀ x)]
      simp [hzero_t, hzero_t₀]
    rw [hEq]
    have : (0 : ℝ) ≤ ε / 2 := by positivity
    simpa using this

/-- If `T` is a continuous linear functional on Schwartz space and `ψ` has compact
    support, then the full real-translation pairing `t ↦ T(translateSchwartz t ψ)`
    is continuous. -/
theorem continuous_apply_translateSchwartz_of_isCompactSupport
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ))) :
    Continuous (fun t : Fin m → ℝ => T (translateSchwartz t ψ)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t₀
  exact T.continuous.continuousAt.tendsto.comp
    (tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ_compact t₀)

/-- Nonzero-limit Banach-Steinhaus payoff for translated compactly supported
    Schwartz tests. This is the exact form needed when a mollified boundary trace
    converges to a continuous boundary functional, not just to `0`. -/
theorem tendsto_apply_translateSchwartz_of_tendsto
    {Tseq : ℕ → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    {T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    (hT : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun n => Tseq n f) atTop (nhds (T f)))
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    {u : ℕ → Fin m → ℝ} {t₀ : Fin m → ℝ}
    (hu : Tendsto u atTop (nhds t₀)) :
    Tendsto (fun n => Tseq n (translateSchwartz (u n) ψ)) atTop
      (nhds (T (translateSchwartz t₀ ψ))) := by
  apply SchwartzMap.tempered_apply_tendsto_of_tendsto hT
  exact (tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ_compact t₀).comp hu

/-- Filter-version Banach-Steinhaus payoff for translated compactly supported
    Schwartz tests with a nonzero pointwise limit. -/
theorem tendsto_apply_translateSchwartz_of_tendsto_filter
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {Tseq : α → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    {T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    (hT : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun a => Tseq a f) l (nhds (T f)))
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : (Fin m → ℝ) → ℂ)))
    {u : α → Fin m → ℝ} {t₀ : Fin m → ℝ}
    (hu : Tendsto u l (nhds t₀)) :
    Tendsto (fun a => Tseq a (translateSchwartz (u a) ψ)) l
      (nhds (T (translateSchwartz t₀ ψ))) := by
  apply SchwartzMap.tempered_apply_tendsto_of_tendsto_filter hT
  exact (tendsto_translateSchwartz_nhds_of_isCompactSupport ψ hψ_compact t₀).comp hu

/-- Weak boundary-value zero is stable under translating a compactly supported
    Schwartz test function in the real directions.

    This is the direct mollifier input: the boundary-zero hypothesis for `G`
    against a fixed translated test function is exactly the boundary trace of the
    real-direction mollification centered at the corresponding real point. -/
theorem tendsto_boundary_pairing_translate_zero_of_zero_bv
    {C : Set (Fin m → ℝ)} {G : (Fin m → ℂ) → ℂ}
    (h_bv_zero : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Tendsto
        (fun ε : ℝ => ∫ x : Fin m → ℝ,
          G (fun i => (x i : ℂ) + ε * (η i : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0))
    (η : Fin m → ℝ) (hη : η ∈ C)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) (x₀ : Fin m → ℝ) :
    Tendsto
      (fun ε : ℝ => ∫ x : Fin m → ℝ,
        G (fun i => ((x₀ i + x i : ℝ) : ℂ) + ε * (η i : ℂ) * Complex.I) * ψ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have h := h_bv_zero (translateSchwartz (-x₀) ψ) η hη
  refine Tendsto.congr' ?_ h
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simpa [translateSchwartz_apply, add_assoc, add_left_comm, add_comm] using
    (MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure (Fin m → ℝ)))
      (fun t : Fin m → ℝ =>
        G (fun i => (t i : ℂ) + ε * (η i : ℂ) * Complex.I) *
          translateSchwartz (-x₀) ψ t)
      x₀).symm

/-! ### Real-direction mollification on the upper half-plane -/

/-- Real-direction mollification of an upper-half-plane holomorphic function is
continuous on the upper half-plane when the Schwartz kernel has compact support.

This is the first analytic step in the weak-BV uniqueness route: continuity comes
for free from compact support, before proving holomorphicity by Morera. -/
theorem continuousOn_realMollify_upperHalfPlane
    {g : ℂ → ℂ}
    (hg : ContinuousOn g EOW.UpperHalfPlane)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : ℝ → ℂ))) :
    ContinuousOn
      (fun z : ℂ => ∫ t : ℝ, g (z + t) * ψ t)
      EOW.UpperHalfPlane := by
  let k : Set ℝ := Function.support (ψ : ℝ → ℂ)
  have hk : IsCompact k := hψ_compact
  let f : ℂ → ℝ → ℂ := fun z t => g (z + t) * ψ t
  have hf : ContinuousOn f.uncurry (EOW.UpperHalfPlane ×ˢ univ) := by
    intro p hp
    rcases hp with ⟨hpU, -⟩
    have hp_shift : p.1 + (p.2 : ℂ) ∈ EOW.UpperHalfPlane := by
      change 0 < (p.1 + (p.2 : ℂ)).im
      simpa using hpU
    have hg_at : ContinuousAt g (p.1 + (p.2 : ℂ)) :=
      (hg (p.1 + (p.2 : ℂ)) hp_shift).continuousAt
        (EOW.upperHalfPlane_isOpen.mem_nhds hp_shift)
    have hleft : ContinuousAt (fun q : ℂ × ℝ => g (q.1 + (q.2 : ℂ))) p :=
      ContinuousAt.comp hg_at <|
        (continuous_fst.add (Complex.continuous_ofReal.comp continuous_snd)).continuousAt
    have hright : ContinuousAt (fun q : ℂ × ℝ => ψ q.2) p :=
      ContinuousAt.comp ψ.continuous.continuousAt continuous_snd.continuousAt
    simpa [f] using (hleft.mul hright).continuousWithinAt
  have hfs : ∀ p, ∀ x, p ∈ EOW.UpperHalfPlane → x ∉ k → f p x = 0 := by
    intro p x _ hx
    simp [k] at hx
    simp [f, hx]
  simpa [f] using
    continuousOn_integral_of_compact_support
      (μ := volume) hk hf hfs

/-- Real-direction mollification of an upper-half-plane holomorphic function is
holomorphic on the upper half-plane when the Schwartz kernel has compact support.

This is the analytic core of the mollifier route to distributional uniqueness:
compact support of `ψ` makes differentiation under the integral sign local and
reduces the needed bound to continuity of `deriv g` on a translated compact set. -/
theorem differentiableOn_realMollify_upperHalfPlane
    {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g EOW.UpperHalfPlane)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ_compact : IsCompact (Function.support (ψ : ℝ → ℂ))) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∫ t : ℝ, g (z + t) * ψ t)
      EOW.UpperHalfPlane := by
  intro z hz
  obtain ⟨R, hRpos, hRsub⟩ :=
    Metric.isOpen_iff.mp EOW.upperHalfPlane_isOpen z hz
  let r : ℝ := R / 2
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  let s : Set ℂ := Metric.ball z r
  have hs : s ∈ 𝓝 z := Metric.ball_mem_nhds z hrpos
  have hs_sub : s ⊆ EOW.UpperHalfPlane := by
    intro x hx
    apply hRsub
    have hxR : dist x z < R := by
      calc
        dist x z < r := hx
        _ < R := by
          dsimp [r]
          linarith
    simpa [Metric.mem_ball] using hxR
  let F : ℂ → ℝ → ℂ := fun w t => g (w + (t : ℂ)) * ψ t
  let F' : ℂ → ℝ → ℂ := fun w t => deriv g (w + (t : ℂ)) * ψ t
  have hψ_cs : HasCompactSupport (ψ : ℝ → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact hψ_compact (by intro t ht; exact ht)
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) volume := by
    filter_upwards [hs] with w hw
    have hwU : w ∈ EOW.UpperHalfPlane := hs_sub hw
    have hshiftU : ∀ t : ℝ, w + (t : ℂ) ∈ EOW.UpperHalfPlane := by
      intro t
      change 0 < (w + (t : ℂ)).im
      simpa using hwU
    have hcont_shift : Continuous fun t : ℝ => g (w + (t : ℂ)) := by
      refine continuous_iff_continuousAt.2 ?_
      intro t
      have hgw : ContinuousAt g (w + (t : ℂ)) :=
        ((hg (w + (t : ℂ)) (hshiftU t)).differentiableAt
          (EOW.upperHalfPlane_isOpen.mem_nhds (hshiftU t))).continuousAt
      have hadd_t : ContinuousAt (fun s : ℝ => w + (s : ℂ)) t := by
        simpa using
          (continuous_const.add (Complex.continuous_ofReal.comp continuous_id)).continuousAt
      exact ContinuousAt.comp_of_eq hgw hadd_t rfl
    have hcont_w : Continuous fun t : ℝ => g (w + (t : ℂ)) * ψ t :=
      hcont_shift.mul ψ.continuous
    exact hcont_w.aestronglyMeasurable
  have hF_int : Integrable (F z) volume := by
    have hshiftU : ∀ t : ℝ, z + (t : ℂ) ∈ EOW.UpperHalfPlane := by
      intro t
      change 0 < (z + (t : ℂ)).im
      simpa using hz
    have hcont_shift : Continuous fun t : ℝ => g (z + (t : ℂ)) := by
      refine continuous_iff_continuousAt.2 ?_
      intro t
      have hgz : ContinuousAt g (z + (t : ℂ)) :=
        ((hg (z + (t : ℂ)) (hshiftU t)).differentiableAt
          (EOW.upperHalfPlane_isOpen.mem_nhds (hshiftU t))).continuousAt
      have hadd_t : ContinuousAt (fun s : ℝ => z + (s : ℂ)) t := by
        simpa using
          (continuous_const.add (Complex.continuous_ofReal.comp continuous_id)).continuousAt
      exact ContinuousAt.comp_of_eq hgz hadd_t rfl
    have hz_cont : Continuous fun t : ℝ => g (z + (t : ℂ)) * ψ t :=
      hcont_shift.mul ψ.continuous
    have hF_support_subset : Function.support (F z) ⊆ Function.support (ψ : ℝ → ℂ) := by
      intro t ht
      by_contra hnot
      have hψt : ψ t = 0 := by
        simpa [Function.mem_support] using hnot
      have hFt : F z t = 0 := by
        simp [F, hψt]
      exact ht (by simp [hFt])
    have hF_support : HasCompactSupport (F z) :=
      HasCompactSupport.of_support_subset_isCompact hψ_compact hF_support_subset
    exact hz_cont.integrable_of_hasCompactSupport hF_support
  have hg_deriv_cont : ContinuousOn (deriv g) EOW.UpperHalfPlane :=
    (hg.deriv EOW.upperHalfPlane_isOpen).continuousOn
  let K : Set ℂ :=
    (Metric.closedBall z r ×ˢ Function.support (ψ : ℝ → ℂ)).image
      (fun p : ℂ × ℝ => p.1 + (p.2 : ℂ))
  have hK_compact : IsCompact K := by
    exact
      ((isCompact_closedBall z r).prod hψ_compact).image <|
        (continuous_fst.add (Complex.continuous_ofReal.comp continuous_snd))
  have hK_sub : K ⊆ EOW.UpperHalfPlane := by
    intro w hw
    rcases hw with ⟨⟨x, t⟩, hx, rfl⟩
    rcases hx with ⟨hxball, _⟩
    have hxU : x ∈ EOW.UpperHalfPlane := by
      apply hRsub
      have hxR : dist x z < R := by
        calc
          dist x z ≤ r := hxball
          _ < R := by
            dsimp [r]
            linarith
      simpa [Metric.mem_ball] using hxR
    change 0 < (x + (t : ℂ)).im
    simpa using hxU
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn (hg_deriv_cont.mono hK_sub)
  let bound : ℝ → ℝ := fun t => C * ‖ψ t‖
  have hF'_meas : AEStronglyMeasurable (F' z) volume := by
    have hz_shift : ∀ t : ℝ, z + (t : ℂ) ∈ EOW.UpperHalfPlane := by
      intro t
      change 0 < (z + (t : ℂ)).im
      simpa using hz
    have hderiv_shift : Continuous fun t : ℝ => deriv g (z + (t : ℂ)) := by
      refine continuous_iff_continuousAt.2 ?_
      intro t
      have hderiv_at : ContinuousAt (deriv g) (z + (t : ℂ)) :=
        (hg_deriv_cont (z + (t : ℂ)) (hz_shift t)).continuousAt
          (EOW.upperHalfPlane_isOpen.mem_nhds (hz_shift t))
      have hadd_t : ContinuousAt (fun s : ℝ => z + (s : ℂ)) t := by
        simpa using
          (continuous_const.add (Complex.continuous_ofReal.comp continuous_id)).continuousAt
      exact ContinuousAt.comp_of_eq hderiv_at hadd_t rfl
    have hz_cont : Continuous fun t : ℝ => deriv g (z + (t : ℂ)) * ψ t :=
      hderiv_shift.mul ψ.continuous
    exact hz_cont.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂volume, ∀ w ∈ s, ‖F' w t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall ?_
    intro t w hw
    by_cases hψt : ψ t = 0
    · simp [F', bound, hψt]
    · have hwK : w + (t : ℂ) ∈ K := by
        refine ⟨⟨w, t⟩, ?_, rfl⟩
        refine ⟨?_, by simp [Function.mem_support, hψt]⟩
        simpa [s, Metric.mem_ball, Metric.mem_closedBall] using le_of_lt hw
      have hderiv_bound : ‖deriv g (w + t)‖ ≤ C := hC _ hwK
      calc
        ‖F' w t‖ = ‖deriv g (w + t)‖ * ‖ψ t‖ := by
          simp [F']
        _ ≤ C * ‖ψ t‖ := by
          exact mul_le_mul_of_nonneg_right hderiv_bound (norm_nonneg _)
        _ = bound t := by simp [bound]
  have hbound_cont : Continuous bound := continuous_const.mul ψ.continuous.norm
  have hbound_support_subset : Function.support bound ⊆ Function.support (ψ : ℝ → ℂ) := by
    intro t ht
    by_contra hnot
    have hψt : ψ t = 0 := by
      simpa [Function.mem_support] using hnot
    have hbt : bound t = 0 := by simp [bound, hψt]
    exact ht (by simp [hbt])
  have hbound_compact : HasCompactSupport bound :=
    HasCompactSupport.of_support_subset_isCompact hψ_compact hbound_support_subset
  have hbound_int : Integrable bound volume :=
    hbound_cont.integrable_of_hasCompactSupport hbound_compact
  have h_diff : ∀ᵐ t ∂volume, ∀ w ∈ s, HasDerivAt (F · t) (F' w t) w := by
    refine Filter.Eventually.of_forall ?_
    intro t w hw
    have hwU : w ∈ EOW.UpperHalfPlane := hs_sub hw
    have hshiftU : w + (t : ℂ) ∈ EOW.UpperHalfPlane := by
      change 0 < (w + (t : ℂ)).im
      simpa using hwU
    have hderiv_g : HasDerivAt g (deriv g (w + (t : ℂ))) (w + (t : ℂ)) :=
      ((hg (w + (t : ℂ)) hshiftU).differentiableAt
        (EOW.upperHalfPlane_isOpen.mem_nhds hshiftU)).hasDerivAt
    have htrans : HasDerivAt (fun u : ℂ => u + (t : ℂ)) 1 w := by
      simpa using (hasDerivAt_id w).add_const (t : ℂ)
    have hcomp : HasDerivAt (fun u : ℂ => g ((fun v : ℂ => v + (t : ℂ)) u))
        (deriv g (w + (t : ℂ))) w :=
      by simpa [one_mul] using hderiv_g.comp w htrans
    simpa [F, F', mul_comm, mul_left_comm, mul_assoc] using hcomp.mul_const (ψ t)
  have hderiv :
      HasDerivAt
        (fun w : ℂ => ∫ t : ℝ, F w t)
        (∫ t : ℝ, F' z t)
        z := by
    exact
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  simpa [F] using hderiv.differentiableAt.differentiableWithinAt

/-- Local distribution-theory lemma: if a continuous function pairs to zero against every
    compactly supported Schwartz test function supported in an open set `U`, then it vanishes
    pointwise on `U`. -/
theorem eq_zero_on_open_of_compactSupport_schwartz_integral_zero {m : ℕ}
    {g : (Fin m → ℝ) → ℂ} (hg : Continuous g)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    (hint : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      HasCompactSupport (f : (Fin m → ℝ) → ℂ) →
      Function.support (f : (Fin m → ℝ) → ℂ) ⊆ U →
      ∫ x : Fin m → ℝ, g x * f x = 0) :
    ∀ x ∈ U, g x = 0 := by
  intro x hx
  obtain ⟨χ, hχ_tsupport, hχ_compact, hχ_smooth, _, hχx⟩ :=
    exists_contDiff_tsupport_subset (s := U) (x := x) (n := (⊤ : ℕ∞)) (hU.mem_nhds hx)
  have hχC_smooth : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun y => (χ y : ℂ)) := by
    rw [contDiff_infty] at hχ_smooth
    rw [contDiff_infty]
    intro n
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp (hχ_smooth n)
  have hχC_compact : HasCompactSupport (fun y => (χ y : ℂ)) :=
    hχ_compact.comp_left Complex.ofReal_zero
  have hχC_support : Function.support (fun y => (χ y : ℂ)) = Function.support χ := by
    ext y
    simp [Function.mem_support]
  let χS : SchwartzMap (Fin m → ℝ) ℂ := hχC_compact.toSchwartzMap hχC_smooth
  have hχS_apply : ∀ y, χS y = (χ y : ℂ) :=
    HasCompactSupport.toSchwartzMap_toFun hχC_compact hχC_smooth
  have hχ_temp : (fun y => (χ y : ℂ)).HasTemperateGrowth := by
    simpa [χS, hχS_apply] using χS.hasTemperateGrowth
  have hprod_zero :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
        ∫ y : Fin m → ℝ, ((χ y : ℂ) * g y) * φ y = 0 := by
    intro φ hφ_compact
    let φχ : SchwartzMap (Fin m → ℝ) ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun y => (χ y : ℂ)) φ
    have hφχ_compact : HasCompactSupport (φχ : (Fin m → ℝ) → ℂ) := by
      rw [HasCompactSupport]
      have htsub :
          tsupport (φχ : (Fin m → ℝ) → ℂ) ⊆ tsupport (fun y => (χ y : ℂ)) := by
        intro z hz
        exact (SchwartzMap.tsupport_smulLeftCLM_subset (F := ℂ) (g := fun y => (χ y : ℂ))
          (f := φ) hz).2
      exact IsCompact.of_isClosed_subset hχC_compact (isClosed_tsupport _) htsub
    have hφχ_support : Function.support (φχ : (Fin m → ℝ) → ℂ) ⊆ U := by
      intro y hy
      have hy_support_prod : y ∈ Function.support (fun z => (χ z : ℂ) * φ z) := by
        simpa [φχ, SchwartzMap.smulLeftCLM_apply_apply, hχ_temp] using hy
      have hy_supportC : y ∈ Function.support (fun y => (χ y : ℂ)) :=
        Function.support_mul_subset_left (fun y => (χ y : ℂ)) (fun y => φ y) hy_support_prod
      have hy_support : y ∈ Function.support χ := by
        rwa [hχC_support] at hy_supportC
      have hy_tsupport : y ∈ tsupport χ := subset_closure hy_support
      exact hχ_tsupport hy_tsupport
    have hzero := hint φχ hφχ_compact hφχ_support
    simpa [φχ, SchwartzMap.smulLeftCLM_apply_apply, hχ_temp, mul_assoc, mul_left_comm, mul_comm]
      using hzero
  have hχg_cont : Continuous (fun y => (χ y : ℂ) * g y) :=
    (Complex.ofRealCLM.continuous.comp hχ_smooth.continuous).mul hg
  have hχg_locInt : LocallyIntegrableOn (fun y => (χ y : ℂ) * g y) univ volume :=
    (hχg_cont.locallyIntegrable).locallyIntegrableOn univ
  have hχg_ae_zero : ∀ᵐ y, ((χ y : ℂ) * g y) = 0 := by
    have hχg_ae_zero' :
        ∀ᵐ y, y ∈ univ → ((χ y : ℂ) * g y) = 0 := by
      refine isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hχg_locInt ?_
      intro ρ hρ_smooth hρ_compact _
      have hρC_smooth : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun y => (ρ y : ℂ)) := by
        rw [contDiff_infty] at hρ_smooth
        rw [contDiff_infty]
        intro n
        exact (Complex.ofRealCLM.contDiff.of_le le_top).comp (hρ_smooth n)
      have hρC_compact : HasCompactSupport (fun y => (ρ y : ℂ)) :=
        hρ_compact.comp_left Complex.ofReal_zero
      let ρS : SchwartzMap (Fin m → ℝ) ℂ := hρC_compact.toSchwartzMap hρC_smooth
      have hρS_compact : HasCompactSupport (ρS : (Fin m → ℝ) → ℂ) :=
        by simpa [ρS] using hρC_compact
      have hzero := hprod_zero ρS hρS_compact
      simpa [ρS, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
        using hzero
    filter_upwards [hχg_ae_zero'] with y hy
    exact hy (by simp)
  have hχg_support_null : volume (Function.support fun y => (χ y : ℂ) * g y) = 0 := by
    rw [show Function.support (fun y => (χ y : ℂ) * g y) = {y | ((χ y : ℂ) * g y) ≠ 0} by
      ext y; simp [Function.mem_support]]
    rw [← MeasureTheory.ae_iff]
    filter_upwards [hχg_ae_zero] with y hy
    simp [hy]
  have hx_eq : ((χ x : ℂ) * g x) = 0 := by
    by_contra hneq
    have hx_support : x ∈ Function.support fun y => (χ y : ℂ) * g y := by
      simpa [Function.mem_support] using hneq
    have hpos :
        0 < volume (Function.support fun y => (χ y : ℂ) * g y) :=
      IsOpen.measure_pos volume hχg_cont.isOpen_support ⟨x, hx_support⟩
    exact (ne_of_gt hpos) hχg_support_null
  rw [show (χ x : ℂ) = 1 by simp [hχx]] at hx_eq
  simpa using hx_eq

/-- Local equality version of
    `eq_zero_on_open_of_compactSupport_schwartz_integral_zero`. -/
theorem eqOn_open_of_compactSupport_schwartz_integral_eq {m : ℕ}
    {g h : (Fin m → ℝ) → ℂ} (hg : Continuous g) (hh : Continuous h)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    (hint : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      HasCompactSupport (f : (Fin m → ℝ) → ℂ) →
      Function.support (f : (Fin m → ℝ) → ℂ) ⊆ U →
      ∫ x : Fin m → ℝ, g x * f x = ∫ x : Fin m → ℝ, h x * f x) :
    Set.EqOn g h U := by
  intro x hx
  have hzero :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (f : (Fin m → ℝ) → ℂ) →
        Function.support (f : (Fin m → ℝ) → ℂ) ⊆ U →
        ∫ y : Fin m → ℝ, (g y - h y) * f y = 0 := by
    intro f hf_compact hf_support
    have hEq := hint f hf_compact hf_support
    have hg_li : MeasureTheory.LocallyIntegrable g := hg.locallyIntegrable
    have hh_li : MeasureTheory.LocallyIntegrable h := hh.locallyIntegrable
    have hg_int : Integrable (fun y : Fin m → ℝ => g y * f y) := by
      simpa [mul_comm] using
        hg_li.integrable_smul_right_of_hasCompactSupport f.continuous hf_compact
    have hh_int : Integrable (fun y : Fin m → ℝ => h y * f y) := by
      simpa [mul_comm] using
        hh_li.integrable_smul_right_of_hasCompactSupport f.continuous hf_compact
    have hfun :
        (fun y : Fin m → ℝ => (g y - h y) * f y) =
          fun y : Fin m → ℝ => g y * f y - h y * f y := by
      funext y
      ring
    have hcalc :
        ∫ y : Fin m → ℝ, (g y - h y) * f y
          = (∫ x : Fin m → ℝ, g x * f x) - ∫ x : Fin m → ℝ, h x * f x := by
      rw [hfun, integral_sub hg_int hh_int]
    exact hcalc.trans <| sub_eq_zero.mpr hEq
  have hdiff_cont : Continuous (fun y => g y - h y) := hg.sub hh
  have hpoint :=
    eq_zero_on_open_of_compactSupport_schwartz_integral_zero hdiff_cont hU hzero x hx
  exact sub_eq_zero.mp hpoint

/-! ### Uniqueness from Boundary Zero + ContinuousWithinAt

This is the 1D EOW slicing argument factored out from
`distributional_uniqueness_tube_of_regular`. It requires:
1. G holomorphic on T(C)
2. G = 0 on the real boundary (pointwise)
3. ContinuousWithinAt G (TubeDomain C) (realEmbed x) for all x

No `HasFourierLaplaceReprRegular` is needed. -/

/-- If G is holomorphic on T(C), vanishes on the real boundary, and is
    continuous within the tube at each boundary point, then G vanishes
    identically on T(C). Uses 1D EOW slicing. -/
theorem uniqueness_of_boundary_zero {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (_hconv : Convex ℝ C) (_hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {G : (Fin m → ℂ) → ℂ}
    (hG_diff : DifferentiableOn ℂ G (TubeDomain C))
    (hG_boundary : ∀ x : Fin m → ℝ, G (realEmbed x) = 0)
    (hG_cont : ∀ x : Fin m → ℝ,
      ContinuousWithinAt G (TubeDomain C) (realEmbed x)) :
    ∀ z ∈ TubeDomain C, G z = 0 := by
  intro z hz
  -- 1D slice: φ(w) = x₀ + w * y₀ maps UHP → T(C)
  let y₀ : Fin m → ℝ := fun i => (z i).im
  let x₀ : Fin m → ℝ := fun i => (z i).re
  have hy₀ : y₀ ∈ C := hz
  let φ : ℂ → (Fin m → ℂ) := fun w i => ↑(x₀ i) + w * ↑(y₀ i)
  let g : ℂ → ℂ := G ∘ φ
  have hg_real : ∀ t : ℝ, g (t : ℂ) = 0 := by
    intro t
    show G (φ (t : ℂ)) = 0
    have hφ_real : φ (t : ℂ) = realEmbed (fun i => x₀ i + t * y₀ i) := by
      ext i; simp [φ, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
    rw [hφ_real]; exact hG_boundary _
  have hz_eq : φ I = z := by
    ext i; simp [φ, x₀, y₀, mul_comm I, Complex.re_add_im]
  suffices h : g I = 0 by
    show G z = 0; rw [show G z = g I from by simp [g, hz_eq]]; exact h
  have hφ_UHP : ∀ w : ℂ, w.im > 0 → φ w ∈ TubeDomain C := by
    intro w hw
    show (fun i => (φ w i).im) ∈ C
    have him : (fun i => (φ w i).im) = w.im • y₀ := by
      ext i; simp [φ, x₀, y₀, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [him]; exact hcone w.im hw y₀ hy₀
  have hφ_cont : Continuous φ :=
    continuous_pi fun i =>
      (continuous_const.add (continuous_id.mul continuous_const))
  have hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane := by
    show DifferentiableOn ℂ (G ∘ φ) EOW.UpperHalfPlane
    exact hG_diff.comp (fun w _ => by
      apply DifferentiableAt.differentiableWithinAt
      exact differentiableAt_pi.mpr fun i =>
        (differentiableAt_const _).add
          (differentiableAt_id.mul (differentiableAt_const _)))
      (fun w hw => hφ_UHP w hw)
  have hφ_real_embed : ∀ t : ℝ, φ (↑t) = realEmbed (fun i => x₀ i + t * y₀ i) := by
    intro t; ext i; simp [φ, x₀, y₀, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
  have hcont_plus : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
      Filter.Tendsto g (nhdsWithin (↑x₁ : ℂ) EOW.UpperHalfPlane) (nhds (g ↑x₁)) := by
    intro x₁ _ _
    show ContinuousWithinAt (G ∘ φ) EOW.UpperHalfPlane ↑x₁
    have h := hG_cont (fun i => x₀ i + x₁ * y₀ i)
    rw [show realEmbed (fun i => x₀ i + x₁ * y₀ i) = φ ↑x₁ from
      (hφ_real_embed x₁).symm] at h
    exact h.comp hφ_cont.continuousAt.continuousWithinAt (fun w hw => hφ_UHP w hw)
  have hbv_cont : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
      Filter.Tendsto g (nhdsWithin (↑x₁ : ℂ) {c : ℂ | c.im = 0})
        (nhds (g ↑x₁)) := by
    intro x₁ _ _
    rw [hg_real x₁]
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with w (hw : w.im = 0)
    have : w = (w.re : ℂ) := Complex.ext rfl (by simp [hw])
    rw [this]; exact (hg_real w.re).symm
  obtain ⟨U, F, hU_open, hU_conv, _, _, hF_diff, hF_plus, hF_minus, hU_ball⟩ :=
    edge_of_the_wedge_1d (-3) 3 (by norm_num : (-3 : ℝ) < 3)
      g 0
      hg_diff
      (differentiableOn_const 0)
      hcont_plus
      (fun _ _ _ => tendsto_const_nhds)
      (fun x₁ _ _ => by show g ↑x₁ = 0; exact hg_real x₁)
      hbv_cont
  have hI_in_U : I ∈ U :=
    hU_ball (by simp [Metric.mem_ball, Complex.norm_I])
  have h_neg_I_in_U : -I ∈ U :=
    hU_ball (by simp [Metric.mem_ball, norm_neg, Complex.norm_I])
  have hF_zero_on_U : ∀ w ∈ U, F w = 0 := by
    have hU_conn : IsConnected U :=
      ⟨⟨I, hI_in_U⟩, hU_conv.isPreconnected⟩
    have h_neg_I_LHP : (-I).im < 0 := by simp [Complex.neg_im, Complex.I_im]
    have h_freq : ∃ᶠ w in nhdsWithin (-I) {(-I)}ᶜ, F w = (0 : ℂ → ℂ) w := by
      apply Filter.Eventually.frequently
      have hmem : U ∩ EOW.LowerHalfPlane ∈ nhdsWithin (-I) {(-I)}ᶜ :=
        nhdsWithin_le_nhds ((hU_open.inter EOW.lowerHalfPlane_isOpen).mem_nhds
          ⟨h_neg_I_in_U, h_neg_I_LHP⟩)
      filter_upwards [hmem] with w ⟨hwU, hwLHP⟩
      simp [hF_minus w ⟨hwU, hwLHP⟩]
    exact fun w hw => identity_theorem_connected hU_open hU_conn F 0
      hF_diff (differentiableOn_const 0) (-I) h_neg_I_in_U h_freq hw
  have hI_UHP : I.im > 0 := by simp [Complex.I_im]
  rw [← hF_plus I ⟨hI_in_U, hI_UHP⟩]
  exact hF_zero_on_U I hI_in_U

/-- If a holomorphic function on a tube domain has zero boundary trace in the
    distributional/limit sense, then it vanishes identically on the tube.

    Unlike `uniqueness_of_boundary_zero`, this theorem does not assume the
    ambient total function is already defined correctly on the real boundary.
    It is the theorem shape needed for mollified weak boundary-value arguments. -/
theorem uniqueness_of_boundary_trace_zero {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (_hconv : Convex ℝ C) (_hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {G : (Fin m → ℂ) → ℂ}
    (hG_diff : DifferentiableOn ℂ G (TubeDomain C))
    (hG_trace : ∀ x : Fin m → ℝ,
      Filter.Tendsto G (nhdsWithin (realEmbed x) (TubeDomain C)) (nhds 0)) :
    ∀ z ∈ TubeDomain C, G z = 0 := by
  intro z hz
  let y₀ : Fin m → ℝ := fun i => (z i).im
  let x₀ : Fin m → ℝ := fun i => (z i).re
  have hy₀ : y₀ ∈ C := hz
  let φ : ℂ → (Fin m → ℂ) := fun w i => ↑(x₀ i) + w * ↑(y₀ i)
  let g : ℂ → ℂ := G ∘ φ
  let gPlus : ℂ → ℂ := fun w => if w.im = 0 then 0 else g w
  have hz_eq : φ I = z := by
    ext i
    simp [φ, x₀, y₀, mul_comm I, Complex.re_add_im]
  suffices h : gPlus I = 0 by
    have hI : gPlus I = g I := by simp [gPlus]
    show G z = 0
    rw [show G z = g I from by simp [g, hz_eq], ← hI]
    exact h
  have hφ_UHP : ∀ w : ℂ, w.im > 0 → φ w ∈ TubeDomain C := by
    intro w hw
    show (fun i => (φ w i).im) ∈ C
    have him : (fun i => (φ w i).im) = w.im • y₀ := by
      ext i
      simp [φ, x₀, y₀, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [him]
    exact hcone w.im hw y₀ hy₀
  have hφ_cont : Continuous φ :=
    continuous_pi fun i =>
      (continuous_const.add (continuous_id.mul continuous_const))
  have hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane := by
    show DifferentiableOn ℂ (G ∘ φ) EOW.UpperHalfPlane
    exact hG_diff.comp
      (fun w _ => by
        apply DifferentiableAt.differentiableWithinAt
        exact differentiableAt_pi.mpr fun i =>
          (differentiableAt_const _).add
            (differentiableAt_id.mul (differentiableAt_const _)))
      (fun w hw => hφ_UHP w hw)
  have hgPlus_diff : DifferentiableOn ℂ gPlus EOW.UpperHalfPlane := by
    intro w hw
    refine (hg_diff w hw).congr ?_ ?_
    · intro z hz
      have hz' : z.im > 0 := by
        simpa [EOW.UpperHalfPlane] using hz
      simp [gPlus, ne_of_gt hz']
    · have hw' : w.im > 0 := by
        simpa [EOW.UpperHalfPlane] using hw
      simp [gPlus, ne_of_gt hw']
  have hφ_real_embed : ∀ t : ℝ, φ (↑t) = realEmbed (fun i => x₀ i + t * y₀ i) := by
    intro t
    ext i
    simp [φ, x₀, y₀, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
  have hcont_plus : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
      Filter.Tendsto gPlus (nhdsWithin (↑x₁ : ℂ) EOW.UpperHalfPlane) (nhds (gPlus ↑x₁)) := by
    intro x₁ _ _
    have htrace := hG_trace (fun i => x₀ i + x₁ * y₀ i)
    rw [show realEmbed (fun i => x₀ i + x₁ * y₀ i) = φ ↑x₁ from
      (hφ_real_embed x₁).symm] at htrace
    have hφ_tendsto :
        Tendsto φ (nhdsWithin (↑x₁ : ℂ) EOW.UpperHalfPlane)
          (nhdsWithin (φ ↑x₁) (TubeDomain C)) :=
      (hφ_cont.continuousAt.continuousWithinAt.tendsto_nhdsWithin
        (fun w hw => hφ_UHP w hw))
    have hcomp := htrace.comp hφ_tendsto
    have hval : gPlus ↑x₁ = 0 := by simp [gPlus]
    rw [hval]
    refine Tendsto.congr' ?_ hcomp
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : w.im > 0 := by
      simpa [EOW.UpperHalfPlane] using hw
    simp [gPlus, g, ne_of_gt hw']
  have hbv_cont : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
      Filter.Tendsto gPlus (nhdsWithin (↑x₁ : ℂ) {c : ℂ | c.im = 0})
        (nhds (gPlus ↑x₁)) := by
    intro x₁ _ _
    have hval : gPlus ↑x₁ = 0 := by simp [gPlus]
    rw [hval]
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with w (hw : w.im = 0)
    simp [gPlus, hw]
  obtain ⟨U, F, hU_open, hU_conv, _, _, hF_diff, hF_plus, hF_minus, hU_ball⟩ :=
    edge_of_the_wedge_1d (-3) 3 (by norm_num : (-3 : ℝ) < 3)
      gPlus 0
      hgPlus_diff
      (differentiableOn_const 0)
      hcont_plus
      (fun _ _ _ => tendsto_const_nhds)
      (fun x₁ _ _ => by simp [gPlus])
      hbv_cont
  have hI_in_U : I ∈ U :=
    hU_ball (by simp [Metric.mem_ball, Complex.norm_I])
  have h_neg_I_in_U : -I ∈ U :=
    hU_ball (by simp [Metric.mem_ball, norm_neg, Complex.norm_I])
  have hF_zero_on_U : ∀ w ∈ U, F w = 0 := by
    have hU_conn : IsConnected U :=
      ⟨⟨I, hI_in_U⟩, hU_conv.isPreconnected⟩
    have h_neg_I_LHP : (-I).im < 0 := by
      simp [Complex.neg_im, Complex.I_im]
    have h_freq : ∃ᶠ w in nhdsWithin (-I) {(-I)}ᶜ, F w = (0 : ℂ → ℂ) w := by
      apply Filter.Eventually.frequently
      have hmem : U ∩ EOW.LowerHalfPlane ∈ nhdsWithin (-I) {(-I)}ᶜ :=
        nhdsWithin_le_nhds ((hU_open.inter EOW.lowerHalfPlane_isOpen).mem_nhds
          ⟨h_neg_I_in_U, h_neg_I_LHP⟩)
      filter_upwards [hmem] with w ⟨hwU, hwLHP⟩
      simp [hF_minus w ⟨hwU, hwLHP⟩]
    exact fun w hw => identity_theorem_connected hU_open hU_conn F 0
      hF_diff (differentiableOn_const 0) (-I) h_neg_I_in_U h_freq hw
  have hI_UHP : I.im > 0 := by simp [Complex.I_im]
  rw [← hF_plus I ⟨hI_in_U, hI_UHP⟩]
  exact hF_zero_on_U I hI_in_U

/-- A local 1D uniqueness theorem for holomorphic functions on the upper
    half-plane with zero continuous boundary values on an interval.

    This is the exact local endpoint needed in mollifier-based distributional
    edge-of-the-wedge arguments: once the mollified boundary trace vanishes on
    an interval `(a,b)`, the holomorphic function vanishes on the canonical ball
    produced by `edge_of_the_wedge_1d`. -/
theorem uniqueness_of_boundary_zero_on_interval (a b : ℝ) (hab : a < b)
    {g : ℂ → ℂ}
    (hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane)
    (hg_boundary : ∀ x : ℝ, a < x → x < b → g (x : ℂ) = 0)
    (hcont_plus : ∀ x : ℝ, a < x → x < b →
      Filter.Tendsto g (nhdsWithin (x : ℂ) EOW.UpperHalfPlane) (nhds (g x)))
    (hbv_cont : ∀ x₀ : ℝ, a < x₀ → x₀ < b →
      Filter.Tendsto g (nhdsWithin (x₀ : ℂ) {c : ℂ | c.im = 0})
        (nhds (g x₀))) :
    ∀ z ∈ Metric.ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2), z.im > 0 → g z = 0 := by
  obtain ⟨U, F, hU_open, hU_conv, _, _, hF_diff, hF_plus, hF_minus, hU_ball⟩ :=
    edge_of_the_wedge_1d a b hab g 0
      hg_diff
      (differentiableOn_const 0)
      hcont_plus
      (fun _ _ _ => tendsto_const_nhds)
      hg_boundary
      hbv_cont
  let mid : ℂ := (((a + b) / 2 : ℝ) : ℂ)
  let rad : ℝ := (b - a) / 2
  have hrad : 0 < rad := by
    dsimp [rad]
    linarith
  let w0 : ℂ := mid - ((rad / 2 : ℝ) : ℂ) * Complex.I
  have hw0_ball : w0 ∈ Metric.ball mid rad := by
    rw [Metric.mem_ball, Complex.dist_eq]
    dsimp [w0, mid, rad]
    have hnorm : ‖(((b - a) / 4 : ℝ) : ℂ) * Complex.I‖ = (b - a) / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
      have : 0 ≤ (b - a) / 4 := by linarith
      simp [abs_of_nonneg this]
    have hsub : w0 - mid = -((((b - a) / 4 : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext
      · simp [w0, mid, rad]
      · simp [w0, mid, rad]
        ring_nf
    rw [hsub, norm_neg, hnorm]
    linarith
  have hw0_U : w0 ∈ U := hU_ball hw0_ball
  have hw0_LHP : w0 ∈ EOW.LowerHalfPlane := by
    change w0.im < 0
    simp [w0, mid, rad]
    linarith
  have hU_conn : IsConnected U := by
    refine ⟨?_, hU_conv.isPreconnected⟩
    exact ⟨w0, hw0_U⟩
  have hF_zero_on_U : ∀ w ∈ U, F w = 0 := by
    have h_freq : ∃ᶠ w in nhdsWithin w0 ({w0}ᶜ), F w = (0 : ℂ → ℂ) w := by
      apply Filter.Eventually.frequently
      have hmem : U ∩ EOW.LowerHalfPlane ∈ nhdsWithin w0 ({w0}ᶜ) := by
        exact nhdsWithin_le_nhds
          ((hU_open.inter EOW.lowerHalfPlane_isOpen).mem_nhds ⟨hw0_U, hw0_LHP⟩)
      filter_upwards [hmem] with w hw
      exact hF_minus w hw
    intro w hw
    exact (identity_theorem_connected hU_open hU_conn F 0
      hF_diff (differentiableOn_const 0) w0 hw0_U h_freq) hw
  intro z hz hzUHP
  have hzU : z ∈ U := hU_ball hz
  calc
    g z = F z := (hF_plus z ⟨hzU, hzUHP⟩).symm
    _ = 0 := hF_zero_on_U z hzU

end SCV

end
