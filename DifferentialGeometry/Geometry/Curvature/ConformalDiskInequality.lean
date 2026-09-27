import DifferentialGeometry.Geometry.Curvature.DiskCurvatureInequality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDiskNonconstant



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]






theorem IsConformalMinimizingDisk.exists_curvature_inequality
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (hu : IsConformalMinimizingDisk g γ u σ U)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ Monotone φ ∧
      (∀ θ, φ (θ + 2 * Real.pi) = φ θ + 1) ∧
      (∀ θ, (φ θ : loopCircle) = σ ((θ / (2 * Real.pi) : ℝ) : loopCircle)) ∧
      U ∘ circleMap 0 1 = (fun t : ℝ => γ (t : loopCircle)) ∘ φ ∧
      IntegrableOn (diskMapSectionalDensity g U) (Metric.closedBall 0 1) ∧
      IntervalIntegrable (diskMapTraceBoundaryDensity g U (fun t : ℝ => γ (t : loopCircle)) φ)
        volume (-Real.pi) Real.pi ∧
      2 * Real.pi ≤
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapSectionalDensity g U z) +
        (∫ θ in -Real.pi..Real.pi,
          diskMapTraceBoundaryDensity g U (fun t : ℝ => γ (t : loopCircle)) φ θ) := by
  obtain ⟨φ, hφ, hm, hp, hl⟩ := hu.positiveTrace.exists_angle_parameter
  have ht := hu.extension.angle_trace hu.trace hl
  obtain ⟨_, s, hs, hDs, hU⟩ := hu.extension
  exact ⟨φ, hφ, hm, hp, hl, ht,
    integrableOn_diskMapSectionalDensity g hs hU (isCompact_closedBall _ _) hDs hu.conformal,
    intervalIntegrable_diskMapTraceBoundaryDensity g hs hU hDs hu.conformal
      hγ.smooth hγ.immersed hφ ht (-Real.pi) Real.pi,
    hu.extension.curvature_inequality g hu.conformal
      (fun q hq => hu.harmonic q (Metric.ball_subset_closedBall hq)) (hu.nonconstant hγ)
      hγ.smooth hγ.immersed hφ hm ht⟩

end DifferentialGeometry.Geometry
