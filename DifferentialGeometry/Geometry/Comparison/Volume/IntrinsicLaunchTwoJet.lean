import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicLaunchResidual
import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicLaunchResidualCurvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunchJet_two_zero_of_residual
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (a b : E) :
    (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
      -(1 / 3 : ℝ) •
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
          (show TangentSpace I p from b)
          (show TangentSpace I p from a)
          (show TangentSpace I p from a) := by
  let X : E :=
    (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E)
  let R : E := show E from
    (DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
      (show TangentSpace I p from b)
      (show TangentSpace I p from a)
      (show TangentSpace I p from a)
  change X = -(1 / 3 : ℝ) • R
  have hsix : (6 : ℝ) • X = (-2 : ℝ) • R :=
    (intrJetResidual_two_zero_eq_six (I := I) g hEnorm p a b).symm.trans
      (intrJetResidual_two_zero_eq_curvature (I := I) g hEnorm p a b)
  linear_combination (norm := module) (1 / 6 : ℝ) • hsix

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
