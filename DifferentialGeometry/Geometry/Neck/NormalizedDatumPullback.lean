import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum

private abbrev Model := (𝓡 2).prod 𝓘(ℝ)
variable {E F H H' M V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace V] [ChartedSpace H' V] [IsManifold J ∞ V] [T2Space V]
  {g : SmoothRiemannianMetric I M} {δ : ℝ} {k : ℕ} {x₀ : M}

theorem pullback_normalized_metric
    (d : normalizedDatum g x₀ δ k)
    (f : V → M) (hf : IsLocalDiffeomorph J I ∞ f)
    (Phi : bufferedCylinder δ → V) (hPhi : IsLocalDiffeomorph Model J ∞ Phi)
    (hmap : f ∘ Phi = d.map) :
    localPullMetric (scaleMetric (metricScalarAt g x₀) d.scalar_pos (localPullMetric g f hf)) Phi hPhi = d.normalizedMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner,scaleMetric_inner,localPullMetric_inner,normalizedDatum.normalizedMetric_inner]
  have hd := mfderiv_comp x ((hf (Phi x)).mdifferentiableAt (by simp))
    ((hPhi x).mdifferentiableAt (by simp))
  have hx : f (Phi x) = d.map x := congrFun hmap x
  have hdv : mfderiv J I f (Phi x) (mfderiv Model J Phi x v) =
      mfderiv Model I d.map x v := by
    rw [← ContinuousLinearMap.comp_apply,← hd,hmap]
    rfl
  have hdw : mfderiv J I f (Phi x) (mfderiv Model J Phi x w) =
      mfderiv Model I d.map x w := by
    rw [← ContinuousLinearMap.comp_apply,← hd,hmap]
    rfl
  congr 1
  exact congrArg₂ (fun V W => g.inner (f (Phi x)) V W) hdv hdw |>.trans (by rw [hx])

end DifferentialGeometry.Geometry.Neck.normalizedDatum
