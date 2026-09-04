import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth

noncomputable section

open Bundle Manifold
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciSharp_chart
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I x) :
    trivToE (I := I) α x (ricciSharp (I := I) g x v) =
      ∑ i : Fin (Module.finrank ℝ E),
        (∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i j *
            ∑ k : Fin (Module.finrank ℝ E),
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) k *
                ricciTensor (I := I) g x
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x)
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)) •
          DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i := by
  classical
  let cv : ∀ y : M, TangentSpace I y →ₗ[ℝ] ℝ := fun y ↦
    (ricciTensor (I := I) g y
      (trivFromE (I := I) α y (trivToE (I := I) α x v))).toLinearMap
  have hsharp := trivToE_metricSharp (I := I) g α cv hx
  rw [ricciSharp_apply]
  change trivToE (I := I) α x
      (metricSharp (I := I) g x ((ricciTensor (I := I) g x v).toLinearMap)) = _
  have hv : trivFromE (I := I) α x (trivToE (I := I) α x v) = v :=
    trivFromE_trivToE (I := I) α hx v
  have hcvx : cv x = (ricciTensor (I := I) g x v).toLinearMap := by
    simp only [cv, hv]
  rw [← hcvx]
  rw [hsharp]
  have hrec := chartBasisVecFiber_recompose (I := I) α hx v
  have hcomponent (j : Fin (Module.finrank ℝ E)) :
      ricciTensor (I := I) g x v (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x) =
        ∑ k : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) k *
            ricciTensor (I := I) g x
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x) := by
    conv_lhs => rw [hrec]
    rw [map_sum, sum_apply]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [map_smul, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  congr 1
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  congr 1
  rw [hcvx]
  exact hcomponent j

end Curvature
end Geometry
end DifferentialGeometry
