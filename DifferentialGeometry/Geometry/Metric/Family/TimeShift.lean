import DifferentialGeometry.Geometry.Metric.Family.Basic

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem MetricFamilySmoothOn.timeShift
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (τ : ℝ) :
    MetricFamilySmoothOn (D.timeShift τ) (fun t => g (t + τ)) where
  coeff x X Y := by
    exact (hg.coeff x X Y).comp
      (contDiff_id.add contDiff_const).contDiffOn (fun _ hs => hs)
  coeff_cont x X Y := by
    exact (hg.coeff_cont x X Y).comp
      (continuous_id.add continuous_const).continuousOn (fun _ hs => hs)
  metricTensor_cont := by
    exact tensor0SFamilyContinuousOnSet.comp_time hg.metricTensor_cont
      (show Continuous (fun s : ℝ => s + τ) from continuous_id.add continuous_const)
      (fun _ hs => hs)
  frameCompSmooth := by
    intro Idx _ frame u hframe i j
    have hmap :
        ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
          (fun p : ℝ × M => (p.1 + τ, p.2)) :=
      (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
    exact (hg.frameCompSmooth frame hframe i j).comp hmap.contMDiffOn
      (fun _ hp => ⟨hp.1, hp.2⟩)

end DifferentialGeometry.Geometry.Curvature
