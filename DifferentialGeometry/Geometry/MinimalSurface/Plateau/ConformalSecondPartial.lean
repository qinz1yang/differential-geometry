import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskCovariantCoordinates



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem diskMapCovariantPartial_tangent_components
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    {z : ℂ} (hz : z ∈ s) :
    g.inner (U z) (diskMapCovariantPartial g U z 1 1) (diskMapPartial U z 1) =
        fderiv ℝ (diskMapConformalCoefficient g U) z 1 / 2 ∧
    g.inner (U z) (diskMapCovariantPartial g U z 1 1) (diskMapPartial U z Complex.I) =
        -fderiv ℝ (diskMapConformalCoefficient g U) z Complex.I / 2 ∧
    g.inner (U z) (diskMapCovariantPartial g U z Complex.I 1) (diskMapPartial U z 1) =
        fderiv ℝ (diskMapConformalCoefficient g U) z Complex.I / 2 ∧
    g.inner (U z) (diskMapCovariantPartial g U z Complex.I 1) (diskMapPartial U z Complex.I) =
        fderiv ℝ (diskMapConformalCoefficient g U) z 1 / 2 := by
  have hx := fderiv_diskMapConformalCoefficient g hs hU hz 1
  have hy := fderiv_diskMapConformalCoefficient g hs hU hz Complex.I
  have horth : (fun q => g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q Complex.I)) =ᶠ[𝓝 z]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hs.mem_nhds hz] with q hq
    exact (hconf q hq).1
  have hdiag : (fun q => g.inner (U q) (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)) =ᶠ[𝓝 z]
      diskMapConformalCoefficient g U := by
    filter_upwards [hs.mem_nhds hz] with q hq
    exact (hconf q hq).2.symm
  have horthd := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) horth.fderiv_eq
  rw [fderiv_diskMapMetricPairing g hs hU hz] at horthd
  have hdiagD := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) hdiag.fderiv_eq
  rw [fderiv_diskMapMetricPairing g hs hU hz] at hdiagD
  rw [diskMapCovariantPartial_symm g hs hU hz 1 Complex.I] at horthd hdiagD
  rw [g.symm (U z) (diskMapPartial U z 1)] at horthd
  rw [g.symm (U z) (diskMapPartial U z Complex.I)] at hdiagD
  have hzero : fderiv ℝ (fun _ : ℂ => (0 : ℝ)) z (1 : ℂ) = 0 := by simp
  rw [hzero] at horthd
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end DifferentialGeometry.Geometry
