import DifferentialGeometry.Geometry.Geodesic.Flow.ParallelField
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isMIntegralCurve_intrinsicGeodesic_of_parallel
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hX : ∀ y : M, (LeviCivita g).toFun (fun z : M => X z) y = 0) (x : M) :
    IsMIntegralCurve (intrinsicGeodesic g hEnorm x (X x)) (fun y : M => X y) := by
  apply (intrinsicGeodesic_isGeodesic g hEnorm x (X x)).isMIntegralCurve_of_parallel
    (intrinsicGeodesic_continuous g hEnorm x (X x)) X hX (t₀ := 0)
  rw [intrinsicGeodesic_zero]
  exact intrinsicGeodesic_mfderiv_zero g hEnorm x (X x)

end DifferentialGeometry.Geometry.Riemannian.Exponential
