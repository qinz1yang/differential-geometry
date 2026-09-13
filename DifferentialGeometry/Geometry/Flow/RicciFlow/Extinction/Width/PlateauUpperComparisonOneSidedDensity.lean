import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonAttainment

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem diskCompetitor_areaUpperApproximation_of_density
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hdensity : ∀ v : DiskCompetitor g γ.toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = γ.toContinuousLoop theta) ∧
          Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map))) :
    ∀ v : DiskCompetitor g γ.toContinuousLoop, ∀ ε : ℝ, 0 < ε →
      ∃ w : SmoothDisk (I := I) (Q := Q),
        (∀ theta, w.map (diskBoundary theta) = γ.toContinuousLoop theta) ∧
          diskArea g w.map ≤ diskArea g v.1.map + ε := by
  intro v ε hε
  obtain ⟨w, hw, ht⟩ := hdensity v
  have hball : ∀ᶠ j in atTop, dist (diskArea g (w j).map) (diskArea g v.1.map) < ε :=
    ht.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨j, hj⟩ := hball.exists
  refine ⟨w j, hw j, ?_⟩
  rw [Real.dist_eq] at hj
  linarith [(abs_le.mp hj.le).2]

theorem diskArea_le_of_minimizingSmoothDisk_of_areaUpperApproximation
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q) (u : SmoothDisk (I := I) (Q := Q))
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = γ.toContinuousLoop theta) →
        diskArea g u.map ≤ diskArea g v.map)
    (hupper : ∀ v : DiskCompetitor g γ.toContinuousLoop, ∀ ε : ℝ, 0 < ε →
      ∃ w : SmoothDisk (I := I) (Q := Q),
        (∀ theta, w.map (diskBoundary theta) = γ.toContinuousLoop theta) ∧
          diskArea g w.map ≤ diskArea g v.1.map + ε) :
    ∀ v : DiskCompetitor g γ.toContinuousLoop, diskArea g u.map ≤ diskArea g v.1.map := by
  intro v
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨w, hw, hle⟩ := hupper v ε hε
  exact (hmin w hw).trans hle

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
