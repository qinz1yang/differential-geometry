import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private theorem contMDiffAt_zero_source_mfderiv {f : V → M} {x : V}
    (hf : ContMDiffAt 𝓘(ℝ, V) I 1 f x) :
    ContMDiffAt 𝓘(ℝ, V) (I.prod 𝓘(ℝ, V →L[ℝ] E)) 0
      (fun y => (⟨f y, mfderiv 𝓘(ℝ, V) I f y⟩ :
        TotalSpace (V →L[ℝ] E)
          (fun m => Bundle.Trivial M V m →L[ℝ] TangentSpace I m))) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf.of_le (by norm_num), ?_⟩
  have hd := hf.mfderiv_const (m := 0) (by norm_num)
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with y
  ext v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def]
  rfl

theorem continuousOn_pullback_metric_coefficients_of_contMDiffOn_one
    (g : SmoothRiemannianMetric I M)
    {f : V → M} {U : Set V} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, V) I 1 f U) :
    ContinuousOn (pullbackMetricCoefficients g f) U := by
  suffices h : ContDiffOn ℝ 0 (pullbackMetricCoefficients g f) U from h.continuousOn
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro x hx
  have hfx := (hf x hx).contMDiffAt (hU.mem_nhds hx)
  have hD := contMDiffAt_zero_source_mfderiv hfx
  have hG := (g.contMDiff.of_le (by norm_num : (0 : ℕ∞ω) ≤ ∞)).contMDiffAt.comp x
    (hfx.of_le (by norm_num))
  have hB := hG.clm_bundle_bilinearComp
    (U₁ := TangentSpace I) (U₂ := TangentSpace I) (U₃ := Bundle.Trivial M ℝ)
    (U₄ := Bundle.Trivial M V) (U₅ := Bundle.Trivial M V) hD hD
  have h := (contMDiffAt_totalSpace.mp hB).2.contDiffAt
  refine (h.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [] with y
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, Trivialization.continuousLinearMapAt_apply]
  rfl

end DifferentialGeometry.Geometry

end
