import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence

section

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem diskMapEnergyDensity_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U W : ℂ → M} {z : ℂ}
    (h : U =ᶠ[𝓝 z] W) : diskMapEnergyDensity g U z = diskMapEnergyDensity g W z := by
  unfold diskMapEnergyDensity diskMapPartial
  erw [h.mfderiv_eq, h.eq_of_nhds]

theorem riemannianDiskEnergy_eq_integral_of_eqOn_openDisk
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {U : ℂ → M}
    (heq : EqOn (diskExtension u) U (Metric.ball (0 : ℂ) 1)) :
    riemannianDiskEnergy g u = ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g U z := by
  unfold riemannianDiskEnergy
  apply integral_congr_ae
  filter_upwards [ae_disk_interior] with z hz
  apply diskMapEnergyDensity_congr_of_eventuallyEq g
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact heq hw


theorem riemannianDiskEnergy_comp_eq_of_extensions
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : ∀ z : closedDisk, U z = u z) (φ : C(closedDisk, closedDisk)) {Φ : ℂ → ℂ}
    (hφ : ∀ z (hz : z ∈ Metric.ball (0 : ℂ) 1),
      (φ ⟨z, Metric.ball_subset_closedBall hz⟩ : ℂ) = Φ z) :
    riemannianDiskEnergy g (u.comp φ) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (U ∘ Φ) z := by
  apply riemannianDiskEnergy_eq_integral_of_eqOn_openDisk g
  intro z hz
  rw [show diskExtension (u.comp φ) z = u (φ ⟨z, Metric.ball_subset_closedBall hz⟩) from
    diskExtension_coe (u.comp φ) ⟨z, Metric.ball_subset_closedBall hz⟩]
  rw [← hu (φ ⟨z, Metric.ball_subset_closedBall hz⟩), hφ z hz]
  rfl

end DifferentialGeometry.Geometry

end

end
