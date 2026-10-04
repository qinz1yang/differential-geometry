import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspProductLowerLength
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspMetricEquivalence

/-!
# Lower length bound for images of cusp paths in the carrier (consumer of F-f.P, lower half)

`CuspEmbedding.frozen_le_pathELength_comp`: for a cusp embedding `e` and a `C¹` path `c` of the cusp
domain in the slab `|z - z₀| ≤ a`, the `g`-length of `e ∘ c` is at least
`√(1 - δ) e^{-a/2} √(Δz² + e^{-z₀} d_q²)` (F-f.P lower half and
`CuspEmbedding.one_sub_mul_le_pullback_inner`). This is the length estimate that the lower
distortion F-f.L applies to lifts of short curves of the carrier (the lifting itself needs the
repaired finite interior patch).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The `g`-length of the image of a slab path of the cusp domain is at least
`√(1 - δ) e^{-a/2} √(Δz² + e^{-z₀} d_q²)`. -/
theorem CuspEmbedding.frozen_le_pathELength_comp {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {c : ℝ → CuspHalfSpace}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) halfCollarModel 1 c (Icc 0 1))
    (hdom : ∀ r ∈ Icc (0 : ℝ) 1, c r ∈ cuspDomain) {z₀ a : ℝ}
    (hslab : ∀ r ∈ Icc (0 : ℝ) 1, |(c r).2.val 0 - z₀| ≤ a) :
    letI : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) :=
      ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal (Real.sqrt (1 - δ) * (Real.exp (-a / 2) *
        Real.sqrt (((c 1).2.val 0 - (c 0).2.val 0) ^ 2 +
          Real.exp (-z₀) * (riemannianEDistOf e.cusp.torusMetric (c 0).1 (c 1).1).toReal ^ 2))) ≤
      pathELength W.model (e.toFun ∘ c) 0 1 := by
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : CuspHalfSpace => TangentSpace halfCollarModel x) :=
    ⟨e.cusp.metric.toRiemannianMetric⟩
  have hP := HyperbolicCusp.frozen_le_pathELength e.cusp hc hslab
  have hopen : IsOpen cuspDomain := by
    change IsOpen ((fun q : CuspHalfSpace => q.2.val 0) ⁻¹' Iio cuspDepth)
    apply isOpen_Iio.preimage
    fun_prop
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (1 - δ)) *
      ‖mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1‖ₑ ≤
        ‖mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ c) t 1‖ₑ := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel c t :=
      (hc.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
    have hed : MDifferentiableAt halfCollarModel W.model e.toFun (c t) :=
      (e.contMDiffOn.contMDiffAt (hopen.mem_nhds (hdom t htI))).mdifferentiableAt
        (by simp)
    rw [mfderiv_comp t hed hcd]
    set v := mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1 with hv
    have hlow := e.one_sub_mul_le_pullback_inner (hdom t htI) v
    rw [← ofReal_norm, ← ofReal_norm, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    change Real.sqrt (1 - δ) * Real.sqrt (e.cusp.metric.inner (c t) v v) ≤
      Real.sqrt (g.inner (e.toFun (c t)) (mfderiv halfCollarModel W.model e.toFun (c t) v)
        (mfderiv halfCollarModel W.model e.toFun (c t) v))
    rcases le_or_gt 0 (1 - δ) with hδ | hδ
    · rw [← Real.sqrt_mul hδ]
      exact Real.sqrt_le_sqrt hlow
    · rw [Real.sqrt_eq_zero'.mpr hδ.le, zero_mul]
      exact Real.sqrt_nonneg _
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  calc _ ≤ ENNReal.ofReal (Real.sqrt (1 - δ)) * pathELength halfCollarModel c 0 1 := by
        gcongr
    _ = ENNReal.ofReal (Real.sqrt (1 - δ)) *
        ∫⁻ t in Ioo (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1‖ₑ := by
        rw [pathELength_eq_lintegral_mfderiv_Ioo]
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (1 - δ)) *
        ‖mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1‖ₑ := lintegral_const_mul_le _ _
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ c) t 1‖ₑ :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = pathELength W.model (e.toFun ∘ c) 0 1 := by
        rw [pathELength_eq_lintegral_mfderiv_Ioo]

end DifferentialGeometry.Geometry.Collapse
