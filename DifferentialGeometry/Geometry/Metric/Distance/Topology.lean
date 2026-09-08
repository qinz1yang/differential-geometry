import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.SmoothRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M]

@[reducible] def toPseudoMetricSpace (g : SmoothRiemannianMetric I M) : PseudoMetricSpace M :=
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  PseudoEMetricSpace.toPseudoMetricSpace fun x y => (Manifold.riemannianEDist_lt_top (I := I) x y).ne

@[simp] theorem toPseudoMetricSpace_toTopologicalSpace (g : SmoothRiemannianMetric I M) :
    g.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M› := rfl

theorem toPseudoMetricSpace_edist (g : SmoothRiemannianMetric I M) (x y : M) :
    @edist M g.toPseudoMetricSpace.toEDist x y = riemannianEDistOf g x y := rfl

end DifferentialGeometry.SmoothRiemannianMetric
