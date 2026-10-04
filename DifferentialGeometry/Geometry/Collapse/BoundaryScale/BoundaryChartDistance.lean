import DifferentialGeometry.Geometry.Metric.EuclideanChart
import DifferentialGeometry.Geometry.Metric.CurveSpeed

/-!
# Straight chart paths in manifolds with boundary

The inverse chart is differentiated within the model range, including the boundary.
A genuine tangent transport bound along a chart segment bounds its Riemannian length.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem riemannianEDistOf_chart_segment_le
    (g : SmoothRiemannianMetric I M) (p : M) (w : E) {K : ℝ}
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1,
      extChartAt I p p + t • w ∈ (extChartAt I p).target)
    (htransport : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace I p,
      let e := trivializationAt E (TangentSpace I) p
      let x := (extChartAt I p).symm (extChartAt I p p + t • w)
      Real.sqrt (g.inner x (e.symmL ℝ x (e.continuousLinearMapAt ℝ p v))
        (e.symmL ℝ x (e.continuousLinearMapAt ℝ p v))) ≤
          K * Real.sqrt (g.inner p v v)) :
    riemannianEDistOf g p ((extChartAt I p).symm (extChartAt I p p + w)) ≤
      ENNReal.ofReal (K * ‖metricChartEuclideanEquiv g p w‖) := by
  let f : ℝ → E := fun t => extChartAt I p p + t • w
  let γ : ℝ → M := fun t => (extChartAt I p).symm (f t)
  have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 f :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm p).comp hf.contMDiffOn hsegment
  have hspeed (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      mfderiv 𝓘(ℝ, ℝ) I γ t 1 =
        (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t) w := by
    have htt : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hft : f t ∈ (extChartAt I p).target := hsegment t htt
    have hfi : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I p).symm
        (range I) (f t) := mdifferentiableWithinAt_extChartAt_symm hft
    have hfd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) f t
        ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
      have hh : HasFDerivAt f ((1 : ℝ →L[ℝ] ℝ).smulRight w) t := by
        convert (((hasDerivAt_id t).smul_const w).const_add
          (extChartAt I p p)).hasFDerivAt using 1
        · rfl
        · ext
          simp
      exact hh.hasMFDerivAt
    have hcomp := hfi.hasMFDerivWithinAt.comp t hfd.hasMFDerivWithinAt
      (fun s hs => extChartAt_target_subset_range p (hsegment s hs))
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) 1) t :=
      ((uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) t htt).uniqueMDiffWithinAt
    have hd := hcomp.mfderivWithin hu
    change mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc 0 1) t =
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) (f t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight w) at hd
    rw [mfderivWithin_eq_mfderiv hu
      ((hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by decide))] at hd
    have hxs : γ t ∈ (chartAt H p).source := by
      simpa only [γ, extChartAt_source] using (extChartAt I p).map_target hft
    have hsymm := TangentBundle.symmL_trivializationAt (I := I) hxs
    rw [(extChartAt I p).right_inv hft] at hsymm
    rw [← hsymm] at hd
    have hv := DFunLike.congr_fun hd 1
    change mfderiv 𝓘(ℝ, ℝ) I γ t 1 =
      (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t)
        (((1 : ℝ →L[ℝ] ℝ).smulRight w) 1) at hv
    simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using hv
  have hspeedBound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) ≤ K * ‖metricChartEuclideanEquiv g p w‖ := by
    rw [hspeed t ht]
    let e := trivializationAt E (TangentSpace I) p
    have hb := htransport t ⟨ht.1.le, ht.2.le⟩ (e.symmL ℝ p w)
    have he : e.continuousLinearMapAt ℝ p (e.symmL ℝ p w) = w := by
      exact e.continuousLinearMapAt_symmL (mem_baseSet_trivializationAt E (TangentSpace I) p) w
    change Real.sqrt (g.inner (γ t) (e.symmL ℝ (γ t)
      (e.continuousLinearMapAt ℝ p (e.symmL ℝ p w)))
      (e.symmL ℝ (γ t) (e.continuousLinearMapAt ℝ p (e.symmL ℝ p w)))) ≤
        K * Real.sqrt (g.inner p (e.symmL ℝ p w) (e.symmL ℝ p w)) at hb
    rw [he] at hb
    simpa only [metricChartEuclideanEquiv_norm, e] using hb
  have hdist := Geometry.riemannianEDistOf_le_of_curve_speed_bound g
    (by norm_num : (0 : ℝ) ≤ 1) hγ hspeedBound
  simpa only [γ, f, zero_smul, add_zero, (extChartAt I p).left_inv
    (mem_extChartAt_source p), one_smul, sub_zero, ENNReal.ofReal_one, mul_one] using hdist

end DifferentialGeometry.Geometry.Metric
