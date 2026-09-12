import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskSmoothLipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap MeasureTheory
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem DiskWeakJordanTrace.of_diskTrace_eq {γ : freeLoop M} {u : C(closedDisk, M)}
    (h : diskTrace u = γ) : DiskWeakJordanTrace γ u :=
  ⟨ContinuousMap.id loopCircle,
    ⟨fun t : ℝ => t, continuous_id, fun _ => rfl,
      Or.inl ⟨monotone_id, fun _ => rfl⟩⟩,
    h.trans (ContinuousMap.comp_id γ).symm⟩

theorem isMorreyDisk_of_minimizesLipschitz (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hsmoothInterior : DiskSmoothInterior (E := E) u)
    (hconformal : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z)
    (hharmonic : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension u) z = 0)
    (hfiniteEnergy : IntegrableOn (diskMapEnergyDensity g (diskExtension u))
      (Metric.closedBall (0 : ℂ) 1))
    (htrace : DiskWeakJordanTrace γ u)
    (hminimizesLipschitz : ∀ v : C(closedDisk, M), DiskWeakJordanTrace γ v →
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) →
      riemannianDiskArea g u ≤ riemannianDiskArea g v) :
    IsMorreyDisk g γ u :=
  ⟨hsmoothInterior, hconformal, hharmonic, hfiniteEnergy, htrace, hminimizesLipschitz,
    fun v hv htracev => hminimizesLipschitz v (DiskWeakJordanTrace.of_diskTrace_eq htracev)
      (hv.exists_lipschitz g)⟩

end DifferentialGeometry.Geometry
