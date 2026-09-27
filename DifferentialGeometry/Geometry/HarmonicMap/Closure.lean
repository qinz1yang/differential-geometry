import DifferentialGeometry.Geometry.HarmonicMap.ConformalSource
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

noncomputable section
open Set Filter Bundle Manifold InnerProductSpace
open scoped Topology ContDiff Manifold
namespace DifferentialGeometry.Geometry
open Riemannian.Geodesic Riemannian.AlongCurve

private theorem mem_closure_inter_of_nhds {s r : Set ℂ} {z : ℂ}
    (hz : z ∈ closure s) (hr : r ∈ 𝓝 z) : z ∈ closure (s ∩ r) := by
  rw [mem_closure_iff_nhds] at hz ⊢
  intro t ht
  obtain ⟨w, ⟨hwt, hwr⟩, hws⟩ := hz (t ∩ r) (inter_mem ht hr)
  exact ⟨w, hwt, hws, hwr⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

theorem planarTension_eq_zero_of_mem_closure (g : SmoothRiemannianMetric I M)
    {U : ℂ → M} {s : Set ℂ} {z : ℂ} (hz : z ∈ closure s)
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) I 2 U z)
    (hH : ∀ w ∈ s, planarTension g U w = 0) : planarTension g U z = 0 := by
  let a := U z
  let X : ℂ → E := (extChartAt I a) ∘ U
  have hsrc : U z ∈ (chartAt H a).source := mem_chart_source H a
  have hX : ContDiffAt ℝ 2 X z :=
    ((contMDiffAt_extChartAt' (I := I) (n := 2) hsrc).comp z hU).contDiffAt
  have hDX (v : ℂ) : ContinuousAt (fun q => fderiv ℝ X q v) z :=
    ((hX.fderiv_right (m := 1) (by norm_num)).continuousAt).clm_apply continuousAt_const
  have hx : X z ∈ interior (extChartAt I a).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      a ((extChartAt I a).map_source (by simpa only [extChartAt_source] using hsrc))
  have hΓ (v : ℂ) : ContinuousAt (fun q => chartChristoffelContraction g a
      (fderiv ℝ X q v) (fderiv ℝ X q v) (X q)) z :=
    (contDiffAt_chartChristoffelContraction g a _ _ _ hx).continuousAt.comp
      (f := fun q => (fderiv ℝ X q v, fderiv ℝ X q v, X q))
      ((hDX v).prodMk ((hDX v).prodMk hX.continuousAt))
  let J : ℂ → E := fun q => Laplacian.laplacian X q +
    chartChristoffelContraction g a (fderiv ℝ X q 1) (fderiv ℝ X q 1) (X q) +
    chartChristoffelContraction g a (fderiv ℝ X q Complex.I) (fderiv ℝ X q Complex.I) (X q)
  have hJ : ContinuousAt J z := (hX.continuousAt_laplacian.add (hΓ 1)).add (hΓ Complex.I)
  let r := {q : ℂ | ContMDiffAt 𝓘(ℝ, ℂ) I 2 U q ∧ U q ∈ (chartAt H a).source}
  have hr : r ∈ 𝓝 z :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hU).and
      (hU.continuousAt.preimage_mem_nhds ((chartAt H a).open_source.mem_nhds hsrc))
  have hJzero : J z = 0 := hJ.continuousWithinAt.eq_const_of_mem_closure
    (mem_closure_inter_of_nhds hz hr) (by
      intro q hq
      have h := chart_planarTension g hq.2.1 hq.2.2
      change (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ (U q)
        (planarTension g U q) = J q at h
      rw [hH q hq.1, map_zero] at h
      exact h.symm)
  have h := chart_planarTension g hU hsrc
  change (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ (U z)
    (planarTension g U z) = J z at h
  rw [hJzero] at h
  have hb : U z ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hsrc
  have he := Trivialization.symmL_continuousLinearMapAt
    (trivializationAt E (TangentSpace I) a) (R := ℝ) hb (planarTension g U z)
  rw [h, map_zero] at he
  exact he.symm

omit [FiniteDimensional ℝ E] in
private theorem continuousAt_metric_mfderiv_pair
    (g : SmoothRiemannianMetric I M) {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) I 1 U z) (v w : ℂ) :
    ContinuousAt (fun q => g.inner (U q) (mfderiv 𝓘(ℝ, ℂ) I U q v)
      (mfderiv 𝓘(ℝ, ℂ) I U q w)) z := by
  let Φ := (extChartAtPartialDiffeomorph I ∞ (U z)).symm
  let X : ℂ → E := Φ.symm ∘ U
  have hsrc : U z ∈ Φ.target := by
    change U z ∈ (extChartAt I (U z)).source
    simpa only [extChartAt_source] using mem_chart_source H (U z)
  have hX : ContDiffAt ℝ 1 X z :=
    (((Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hsrc)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).comp z hU).contDiffAt
  have hx : X z ∈ Φ.source := Φ.toOpenPartialHomeomorph.map_target hsrc
  have hB : ContinuousAt (pullbackMetricCoefficients g Φ) (X z) :=
    (contDiffOn_pullback_metric_coefficients g Φ.open_source Φ.contMDiffOn_toFun).continuousOn.continuousAt
      (Φ.open_source.mem_nhds hx)
  have hDX (v : ℂ) : ContinuousAt (fun q => fderiv ℝ X q v) z :=
    (hX.fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply continuousAt_const
  have hc : ContinuousAt (fun q => pullbackMetricCoefficients g Φ (X q)
      (fderiv ℝ X q v) (fderiv ℝ X q w)) z :=
    ((hB.comp hX.continuousAt).clm_apply (hDX v)).clm_apply (hDX w)
  apply hc.congr_of_eventuallyEq
  filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hU,
    hU.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hsrc)] with q hq hs
  exact (pullbackMetricCoefficients_fderiv_symm g Φ (hq.mdifferentiableAt (by norm_num)) hs v w).symm

omit [FiniteDimensional ℝ E] in
theorem conformal_mfderiv_of_mem_closure (g : SmoothRiemannianMetric I M)
    {U : ℂ → M} {s : Set ℂ} {z : ℂ} (hz : z ∈ closure s)
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) I 1 U z)
    (ho : ∀ q ∈ s, g.inner (U q) (mfderiv 𝓘(ℝ, ℂ) I U q (1 : ℂ))
      (mfderiv 𝓘(ℝ, ℂ) I U q Complex.I) = 0)
    (he : ∀ q ∈ s, g.inner (U q) (mfderiv 𝓘(ℝ, ℂ) I U q (1 : ℂ))
      (mfderiv 𝓘(ℝ, ℂ) I U q (1 : ℂ)) =
      g.inner (U q) (mfderiv 𝓘(ℝ, ℂ) I U q Complex.I) (mfderiv 𝓘(ℝ, ℂ) I U q Complex.I)) :
    g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) = 0 ∧
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) =
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) := by
  refine ⟨(continuousAt_metric_mfderiv_pair g hU 1 Complex.I).continuousWithinAt.eq_const_of_mem_closure hz ho, ?_⟩
  apply sub_eq_zero.mp
  exact ((continuousAt_metric_mfderiv_pair g hU 1 1).sub
    (continuousAt_metric_mfderiv_pair g hU Complex.I Complex.I)).continuousWithinAt.eq_const_of_mem_closure hz
    (fun q hq => sub_eq_zero.mpr (he q hq))

end DifferentialGeometry.Geometry
