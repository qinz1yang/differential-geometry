import DifferentialGeometry.Geometry.Comparison.Busemann.Eikonal
import DifferentialGeometry.Geometry.Comparison.Busemann.Line.Harmonic
import DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.Rigidity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian

open Geometry.Connection Geometry.Curvature Geometry.Operator BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsMinimizingLine.covariantDerivative_gradFun_busemann_eq_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (x : M) :
    (LeviCivita (I := I) g).toFun
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y) x = 0 := by
  have hb := hγ.busemann_contMDiff (I := I) hEnorm hd hRic
  apply covariantDerivative_gradFun_eq_zero_of_harmonic_of_locally_constant_norm g hb x
    (c := 1)
  · apply Filter.Eventually.of_forall
    intro y
    simpa only [normGradSqFun_def, gradient_eq_gradFun] using
      normGradSqFun_busemann_eq_one (I := I) g hEnorm hγ.positive_ray y
        (hb.contMDiffAt.mdifferentiableAt (by simp))
  · exact Filter.Eventually.of_forall (hγ.busemann_laplacian_eq_zero hEnorm hd hRic)
  · simpa only [zero_mul] using hRic x (gradFun g (busemann (I := I) γ) x)

end DifferentialGeometry.Geometry.Riemannian
