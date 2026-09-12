import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential



noncomputable section

open Bundle Manifold DifferentialGeometry MeasureTheory Set
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem DiskMapConformalAt.areaDensity_eq_energy
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (h : DiskMapConformalAt g U z) :
    riemannianAreaDensity g U z = diskMapEnergyDensity g U z := by
  have ha : riemannianAreaDensity g U z =
      g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) :=
    tangentTwoJacobian_of_conformal g h.1 h.2
  rw [ha]
  unfold diskMapEnergyDensity
  rw [← h.2]
  ring



theorem diskAreaDensity_ae_eq_energy_of_conformal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z) :
    riemannianAreaDensity g (diskExtension u) =ᵐ[volume.restrict (Metric.closedBall 0 1)]
      diskMapEnergyDensity g (diskExtension u) := by
  filter_upwards [ae_disk_interior] with z hz
  exact (h z hz).areaDensity_eq_energy



theorem diskArea_integrable_iff_energy_of_conformal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z) :
    IntegrableOn (riemannianAreaDensity g (diskExtension u)) (Metric.closedBall 0 1) ↔
      IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall 0 1) :=
  integrable_congr (diskAreaDensity_ae_eq_energy_of_conformal g u h)

theorem diskArea_integrable_of_conformal_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z)
    (he : IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall 0 1)) :
    IntegrableOn (riemannianAreaDensity g (diskExtension u)) (Metric.closedBall 0 1) :=
  (diskArea_integrable_iff_energy_of_conformal g u h).2 he


theorem riemannianDiskArea_eq_energy_of_conformal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z) :
    riemannianDiskArea g u =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z :=
  integral_congr_ae (diskAreaDensity_ae_eq_energy_of_conformal g u h)

end DifferentialGeometry.Geometry
