import DifferentialGeometry.Geometry.Curvature.RegularizedDiskComparison
import DifferentialGeometry.Geometry.Curvature.DiskSectionalDensity
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianRegularity
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Integrability



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in




theorem integral_regularizedDisk_curvatureDensity_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ Metric.ball 0 1, diskMapTension g U q = 0)
    {a f : ℂ → ℝ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    (haeq : ∀ z ∈ Metric.closedBall 0 1, a =ᶠ[𝓝 z] diskMapConformalCoefficient g U)
    {ε : ℝ} (hε : ε ≠ 0) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I) ≤
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      regularizedConformalWeight a f ε z * diskMapSectionalDensity g U z) +
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      (1 - regularizedConformalWeight a f ε z) * (-Laplacian.laplacian f z)) := by
  let D := Metric.closedBall (0 : ℂ) 1
  have hD : IsCompact D := isCompact_closedBall _ _
  have hB : IntegrableOn (diskMapSectionalDensity g U) D :=
    integrableOn_diskMapSectionalDensity g hs hU hD hDs hconf
  have hL : IntegrableOn (fun z => -Laplacian.laplacian f z) D :=
    (continuous_laplacian (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).neg.continuousOn.integrableOn_compact hD
  have hwB := integrable_regularizedConformalWeight_comp_mul (c := id) measurable_id
    ha.continuous.measurable hf.continuous.measurable (Eventually.of_forall han) hB ε
  have hwL := integrable_regularizedConformalWeight_comp_mul (c := id) measurable_id
    ha.continuous.measurable hf.continuous.measurable (Eventually.of_forall han) hL ε
  have hcL : IntegrableOn (fun z => (1 - regularizedConformalWeight a f ε z) *
      (-Laplacian.laplacian f z)) D := by
    convert hL.sub hwL using 1
    funext z
    simp only [Pi.sub_apply, id_eq]
    ring
  have hlog := contDiff_regularizedConformalLogFactor ha hf han hε
  have hK : IntegrableOn (fun z =>
      planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I) D := by
    have hcont : Continuous (fun z =>
        planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
          tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
            (x := z) (1 : ℂ) Complex.I) := by
      have heq : (fun z =>
          planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
            tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
              (x := z) (1 : ℂ) Complex.I) =
          (fun z : ℂ => -Laplacian.laplacian (regularizedConformalLogFactor a f ε) z) := by
        funext z
        exact planeGaussianCurvature_mul_areaDensity hlog z
      rw [heq]
      exact (continuous_laplacian (hlog.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).neg
    exact hcont.continuousOn.integrableOn_compact hD
  erw [← integral_add hwB hcL]
  apply integral_mono_ae hK (hwB.add hcL)
  have hsphere : ∀ᵐ z : ℂ, z ∉ Metric.sphere (0 : ℂ) 1 := by
    apply ae_iff.mpr
    convert Measure.addHaar_sphere volume (0 : ℂ) (1 : ℝ) using 1
    congr 1
    ext z
    simp
  filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae hsphere] with z hz hn
  have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
    have hle : ‖z‖ ≤ 1 := by simpa [D, Metric.mem_closedBall, dist_zero_right] using hz
    have hne : ‖z‖ ≠ 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hn
    simpa [Metric.mem_ball, dist_zero_right] using lt_of_le_of_ne hle hne
  exact regularizedDisk_curvatureDensity_le_sectional g Metric.isOpen_ball
    (hU.mono (Metric.ball_subset_closedBall.trans hDs))
    (fun q hq => hconf q (Metric.ball_subset_closedBall hq)) hharm ha hf han hε hzball (haeq z hz)

end DifferentialGeometry.Geometry
