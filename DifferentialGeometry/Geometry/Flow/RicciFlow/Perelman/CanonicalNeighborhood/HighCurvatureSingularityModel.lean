import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimInstance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
theorem scalarAtBase_one_and_notFlat_of_blowupLimit {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (o : TangentOrientationSection M)
    {kappa : ℝ} {x : ℕ → M} {t : ℕ → ℝ} (L : BlowupLimit S o kappa x t) :
    L.model.S.scalar 0 L.model.basepoint = 1 ∧ PointedFlowNotFlat (I := I3) L.model :=
  ⟨by simpa only [PointedFlowScalarAtBase] using L.normalized, L.ancient.notFlat⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem not_nonempty_blowupLimit_of_scalar_eq_zero {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (o : TangentOrientationSection M)
    (kappa : ℝ) (x : ℕ → M) (t : ℕ → ℝ)
    (hscalar : ∀ (s : ℝ) (y : M), S.scalar s y = 0) :
    ¬ Nonempty (BlowupLimit S o kappa x t) := by
  rintro ⟨L⟩
  have hpos : (0 : ℝ) < 0 := by simpa only [hscalar] using L.scale_pos 0
  exact (lt_irrefl (0 : ℝ)) hpos

theorem not_nonempty_blowupLimit_euclideanConstant {D : RealTimeInterval}
    (o : TangentOrientationSection ThreeSpace) (kappa : ℝ) (x : ℕ → ThreeSpace)
    (t : ℕ → ℝ) :
    ¬ Nonempty (BlowupLimit (M := ThreeSpace)
      (SolutionOn.const (euclideanMetric (E := ThreeSpace)) D) o kappa x t) := by
  refine not_nonempty_blowupLimit_of_scalar_eq_zero _ o kappa x t ?_
  intro s y
  simp only [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.const_metric]
  exact metricScalarAt_eq_zero_of_ricciTensor_eq_zero (euclideanMetric (E := ThreeSpace)) y
    (fun v w => DifferentialGeometry.Geometry.euclideanMetric_ricciTensor y v w)

theorem not_isAncientKappaSolution_euclideanFlatFlow (kappa : ℝ) :
    ¬ IsAncientKappaSolution (I := I3) kappa KappaSolutions.euclideanFlatFlow :=
  fun hK => KappaSolutions.euclideanFlatFlow_not_notFlat hK.notFlat

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
