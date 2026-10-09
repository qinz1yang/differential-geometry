import DifferentialGeometry.Geometry.Measure.Area.ImmersionPullback
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

private theorem diskMapPartial_comp_of_mdifferentiableAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (p : M → N) (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    {U : ℂ → M} {z : ℂ} (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (v : ℂ) :
    diskMapPartial (p ∘ U) z v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p (U z) (diskMapPartial U z v) := by
  exact congrArg (fun L : ℂ →L[ℝ] F => L v)
    (mfderiv_comp z (hp.mdifferentiableAt (by simp)) hU)


variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- An immersion preserves energy density for its literal pullback metric at
any point where the parametrization is differentiable. -/
theorem diskMapEnergyDensity_pullback_immersion
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (p : M → N)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    {U : ℂ → M} {z : ℂ} (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :
    diskMapEnergyDensity (g.pullback p hp himm) U z =
      diskMapEnergyDensity g (p ∘ U) z := by
  have hinner (v w : ℂ) :
      (g.pullback p hp himm).inner (U z)
        (diskMapPartial U z v) (diskMapPartial U z w) =
      g.inner ((p ∘ U) z)
        (diskMapPartial (p ∘ U) z v) (diskMapPartial (p ∘ U) z w) := by
    rw [SmoothRiemannianMetric.pullback_inner,
      ← diskMapPartial_comp_of_mdifferentiableAt p hp hU v,
      ← diskMapPartial_comp_of_mdifferentiableAt p hp hU w]
    rfl
  simp only [diskMapEnergyDensity, hinner]

/-- Interior smoothness suffices to preserve the area of the same continuous
disk under an immersion with the pullback metric. -/
theorem riemannianDiskArea_pullback_immersion_of_smoothInterior
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (p : M → N)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (u : C(closedDisk, M)) (hu : DiskSmoothInterior (E := E) u) :
    riemannianDiskArea (g.pullback p hp himm) u =
      riemannianDiskArea g (p ∘ u) := by
  apply integral_congr_ae
  filter_upwards [ae_disk_interior] with z hz
  exact riemannianAreaDensity_pullback_immersion g p hp himm
    ((hu.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp))

/-- The energy densities of the same smooth-interior disk and its projection
agree almost everywhere on the closed disk. -/
theorem diskMapEnergyDensity_pullback_immersion_ae_of_smoothInterior
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (p : M → N)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (u : C(closedDisk, M)) (hu : DiskSmoothInterior (E := E) u) :
    diskMapEnergyDensity (g.pullback p hp himm) (diskExtension u) =ᵐ[
      volume.restrict (Metric.closedBall (0 : ℂ) 1)]
      diskMapEnergyDensity g (diskExtension (p ∘ u)) := by
  filter_upwards [ae_disk_interior] with z hz
  exact diskMapEnergyDensity_pullback_immersion g p hp himm
    ((hu.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp))

/-- Finite energy transfers between the same smooth-interior disk and its
projection without a Lipschitz hypothesis on that disk. -/
theorem integrableOn_diskMapEnergyDensity_pullback_immersion_iff_of_smoothInterior
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (p : M → N)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (u : C(closedDisk, M)) (hu : DiskSmoothInterior (E := E) u) :
    IntegrableOn (diskMapEnergyDensity (g.pullback p hp himm) (diskExtension u))
        (Metric.closedBall (0 : ℂ) 1) ↔
      IntegrableOn (diskMapEnergyDensity g (diskExtension (p ∘ u)))
        (Metric.closedBall (0 : ℂ) 1) :=
  integrable_congr (diskMapEnergyDensity_pullback_immersion_ae_of_smoothInterior
    g p hp himm u hu)

end DifferentialGeometry.Geometry
