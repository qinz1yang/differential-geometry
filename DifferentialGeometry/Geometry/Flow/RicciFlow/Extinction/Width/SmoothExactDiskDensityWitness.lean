import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Plateau

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

variable [FiniteDimensional ℝ E]

theorem smooth_exact_disk_density_witness [I.Boundaryless] [T2Space Q] [CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (gamma : RegularLoop I Q)
    (u : SmoothDisk (I := I) (Q := Q))
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma theta) :
    ∃ v : DiskCompetitor g gamma.toContinuousLoop, ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j theta, (w j).map (diskBoundary theta) = gamma theta) ∧
        Filter.Tendsto (fun j => diskArea g (w j).map) Filter.atTop (𝓝 (diskArea g v.1.map)) := by
  obtain ⟨ul, hul⟩ := u.exists_lipschitz g
  refine ⟨⟨ul, fun theta => ?_⟩, fun _ => u, fun j theta => htrace theta, ?_⟩
  · rw [hul]
    exact htrace theta
  · have hconst : Filter.Tendsto (fun _ : ℕ => diskArea g u.map) Filter.atTop
        (𝓝 (diskArea g u.map)) := tendsto_const_nhds
    simpa only [hul] using hconst

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
