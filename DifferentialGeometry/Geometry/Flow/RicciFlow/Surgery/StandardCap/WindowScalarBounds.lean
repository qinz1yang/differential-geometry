import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.ScalarPerturbation
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private local instance (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

theorem exists_uniform_window_scalar_bounds_of_metric_close
    (D R : ℝ) (hRD : R < D + 1) :
    ∃ ε C : ℝ, 0 < ε ∧ 1 ≤ C ∧
      ∀ g : SmoothRiemannianMetric ThreeModel (standardCapWindow D),
        metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ R} 2
          g (metric.restrictOpen (standardCapWindow D))
          (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε →
        ∀ x : standardCapWindow D, ‖x.val‖ ≤ R →
          1/2 < metricScalarAt g x ∧ metricScalarAt g x < C := by
  let K : Set (standardCapWindow D) := {x | ‖x.val‖ ≤ R}
  let gRef := metric.restrictOpen (standardCapWindow D)
  have hK : IsCompact K := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ R} := by
      simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) R
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      refine ⟨⟨x,?_⟩,rfl⟩
      change ‖x‖ < D+1
      change ‖x‖ ≤ R at hx
      linarith)
  obtain ⟨B,hB⟩ := hK.bddAbove_image (metricScalar_smooth gRef).continuous.continuousOn
  obtain ⟨ε,hε,hclose⟩ := exists_abs_metricScalarAt_sub_lt gRef hK (c := 1/2) (by norm_num)
  refine ⟨ε,max 1 (B+1),hε,le_max_left _ _,?_⟩
  intro g hg x hx
  have herr := hclose g (fun y hy j hj =>
    (metricDerivNorm_lt_of_sup_lt K 2 g gRef gRef hg hj hy).le) x hx
  have hsc : metricScalarAt gRef x = metricScalarAt metric x.val :=
    metricScalarAt_restrictOpen metric (standardCapWindow D) x
  have hlower : 1 ≤ metricScalarAt gRef x := hsc.symm ▸ one_le_metricScalarAt x.val
  have hupper : metricScalarAt gRef x ≤ B := hB (mem_image_of_mem _ hx)
  constructor
  · linarith [(abs_lt.mp herr).1]
  · have hh : metricScalarAt g x < B+1 := by linarith [(abs_lt.mp herr).2]
    exact hh.trans_le (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
