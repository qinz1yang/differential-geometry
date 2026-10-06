import DifferentialGeometry.Analysis.Calculus.Interpolation.ForwardPhaseAnnulus
import DifferentialGeometry.Geometry.Measure.Area.LocalReparametrization

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual forward phase annulus preserves the area of the same smooth
original disk in the same metric. Its inverse need not be Lipschitz near the
inner circle. This is the annular term needed by the MY-2 splice. -/
theorem riemannianArea_forwardPhaseAnnulus
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : C(closedDisk, M))
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q)
      (Metric.ball (0 : ℂ) 1))
    {r b : ℝ} (hr : 0 < r) (hb : b < 1)
    (φ : ℝ ≃ₜ ℝ) (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t))
    (hm : StrictMono φ) (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1) :
    riemannianArea g (diskExtension q ∘ ForwardPhaseAnnulus.map r b hφ hp)
        {z : ℂ | r < ‖z‖ ∧ ‖z‖ < b} =
      riemannianArea g (diskExtension q) {z : ℂ | r < ‖z‖ ∧ ‖z‖ < b} := by
  let A : Set ℂ := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < b}
  let H := ForwardPhaseAnnulus.map r b hφ hp
  have hA : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  obtain ⟨K, hK⟩ := ForwardPhaseAnnulus.exists_lipschitzOnWith_map hr hφ hp (b := b)
  have hKA : LipschitzOnWith K H A := hK.mono (fun z hz => ⟨hz.1.le, hz.2.le⟩)
  obtain ⟨Φ, hΦ, heΦ⟩ := hKA.extend_finite_dimension
  have hBij : BijOn H A A :=
    ForwardPhaseAnnulus.bijOn_map_radial r b φ hφ hm hp (Ioo r b)
  have hΦinj : InjOn Φ A := by
    intro x hx y hy heq
    exact hBij.injOn hx hy ((heΦ hx).trans (heq.trans (heΦ hy).symm))
  have hΦimage : Φ '' A = A := heΦ.image_eq.symm.trans hBij.image_eq
  have hqdiff (z : ℂ) (hz : z ∈ A) :
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (Φ z) := by
    have hzA : Φ z ∈ A := by
      rw [← heΦ hz]
      exact hBij.mapsTo hz
    have hzball : Φ z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hzA.2.trans hb
    exact (hq.contMDiffAt (Metric.isOpen_ball.mem_nhds hzball)).mdifferentiableAt (by simp)
  change riemannianArea g (diskExtension q ∘ H) A = riemannianArea g (diskExtension q) A
  calc
    _ = riemannianArea g (diskExtension q ∘ Φ) A :=
      riemannianArea_congr_on_open g hA (fun z hz => congrArg (diskExtension q) (heΦ hz))
    _ = riemannianArea g (diskExtension q) (Φ '' A) := by
      rw [riemannianArea, riemannianArea,
        integral_image_eq_integral_abs_det_of_lipschitz hΦ hA.measurableSet hΦinj]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hA.measurableSet,
        ae_restrict_of_ae (hΦ.ae_differentiableAt (μ := volume))] with z hz hzd
      exact riemannianAreaDensity_precomp g (hqdiff z hz) hzd
    _ = riemannianArea g (diskExtension q) A := by rw [hΦimage]

end DifferentialGeometry.Geometry
