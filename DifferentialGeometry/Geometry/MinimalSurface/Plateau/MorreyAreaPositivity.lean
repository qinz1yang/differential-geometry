import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ExistenceReduction
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import DifferentialGeometry.Geometry.Metric.ZeroDerivative
import DifferentialGeometry.Geometry.Measure.Area.Positivity

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

/-- A Morrey disk spanning a smooth embedded loop has strictly positive area.
Only interior smoothness and the finite area supplied by the Morrey conditions
are used; no regularity or injectivity of its differential at the boundary is needed. -/
theorem IsMorreyDisk.area_pos
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) :
    0 < riemannianDiskArea g u := by
  have hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u)
      (Metric.ball (0 : ℂ) 1) := hu.smoothInterior.of_le (by simp)
  have hpos : ∃ z ∈ Metric.ball (0 : ℂ) 1,
      0 < diskMapConformalCoefficient g (diskExtension u) z := by
    by_contra hpos
    push Not at hpos
    have hder : ∀ z ∈ Metric.ball (0 : ℂ) 1,
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z = 0 := by
      intro z hz
      exact (hu.conformal z hz).coefficient_eq_zero_iff.mp
        (le_antisymm (hpos z hz)
          (diskMapConformalCoefficient_nonneg g (diskExtension u) z))
    have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
    have hconst : EqOn (diskExtension u) (fun _ => diskExtension u 0)
        (Metric.ball (0 : ℂ) 1) := by
      intro z hz
      exact eq_of_mfderiv_eq_zero_on_convex g Metric.isOpen_ball hU
        (Subset.refl _) (convex_ball (0 : ℂ) 1) hder hz h0
    have hcontinuous : Continuous (diskExtension u) :=
      u.continuous.comp diskRetraction_lipschitz.continuous
    have hclosed : EqOn (diskExtension u) (fun _ => diskExtension u 0)
        (Metric.closedBall (0 : ℂ) 1) :=
      hconst.of_subset_closure hcontinuous.continuousOn continuousOn_const
        Metric.ball_subset_closedBall
        (by rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)])
    have hcu : u = ContinuousMap.const closedDisk (diskExtension u 0) := by
      apply ContinuousMap.ext
      intro z
      simpa only [diskExtension_coe, ContinuousMap.const_apply] using hclosed z.property
    apply not_isMorreyDisk_const_of_isSmoothEmbeddedLoop hγ (diskExtension u 0)
    exact hcu ▸ hu
  obtain ⟨z, hz, hpos⟩ := hpos
  have hdensity : 0 < riemannianAreaDensity g (diskExtension u) z := by
    rw [(hu.conformal z hz).areaDensity_eq_energy,
      ← (hu.conformal z hz).coefficient_eq_energy]
    exact hpos
  have hcont : ContinuousAt (riemannianAreaDensity g (diskExtension u)) z :=
    (continuousOn_riemannianAreaDensity g Metric.isOpen_ball hU).continuousAt
      (Metric.isOpen_ball.mem_nhds hz)
  change 0 < ∫ w in Metric.closedBall (0 : ℂ) 1,
    riemannianAreaDensity g (diskExtension u) w
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun w => riemannianAreaDensity_nonneg g (diskExtension u) w)
    hu.integrableArea).2
  exact Measure.measure_pos_of_mem_nhds volume
    (inter_mem (hcont.eventually_ne hdensity.ne')
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall))

end DifferentialGeometry.Geometry
