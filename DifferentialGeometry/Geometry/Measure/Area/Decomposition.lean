import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz



noncomputable section

open Manifold DifferentialGeometry MeasureTheory Set
open scoped ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem riemannianArea_finite_decomposition (g : SmoothRiemannianMetric I M)
    (u : ℂ → M) {ι : Type*} [Fintype ι] (s : ι → Set ℂ)
    (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => AEDisjoint volume (s i) (s j)))
    (hu : IntegrableOn (riemannianAreaDensity g u) (⋃ i, s i)) :
    riemannianArea g u (⋃ i, s i) = ∑ i, riemannianArea g u (s i) := by
  simpa only [riemannianArea, tsum_fintype] using
    integral_iUnion_ae (fun i => (hs i).nullMeasurableSet) hd hu

end DifferentialGeometry.Geometry
