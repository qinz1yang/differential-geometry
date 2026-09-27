import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentity



noncomputable section

open Set Bundle Manifold DifferentialGeometry
open scoped Topology Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem sectionalCurvatureNumerator_eq_inner_chartRiemann
    (g : SmoothRiemannianMetric I M) (p : M) (v w : TangentSpace I p) :
    sectionalCurvatureNumerator g p v w = g.inner p v (chartRiemannCLM g p v w w) := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) p
  have hrepr (X : TangentSpace I p) : b.repr X =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr X := by
    simp [b, tangentSpaceModelContinuousLinearEquiv_apply]
  have hgram (l m : Fin (Module.finrank ℝ E)) :
      chartGramOnE g p l m (extChartAt I p p) = g.inner p (b l) (b m) := by
    rw [chartGramOnE_def, (extChartAt I p).left_inv (mem_extChartAt_source p),
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
      chartBasisVecFiber_self, chartBasisVecFiber_self]
  have hin (m : Fin (Module.finrank ℝ E)) :
      g.inner p v (b m) = ∑ l, b.repr v l * g.inner p (b l) (b m) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, _root_.sum_apply, map_smul, _root_.smul_apply, smul_eq_mul]
  rw [chartRiemannCLM_apply]
  change sectionalCurvatureNumerator g p v w = g.inner p v
    (∑ i, ∑ j, ∑ k, ∑ m, (b.repr w i * b.repr v j * b.repr w k *
      chartRiemannTensor g p i j k m (extChartAt I p p)) • b m)
  simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [hin, Finset.mul_sum]
  rw [sectionalCurvatureNumerator_def]
  simp only [chartRiemannLower, Finset.mul_sum, hrepr]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  rw [hgram]
  ring




theorem sectionalCurvature_eq_riemann [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (p : M) (v w : TangentSpace I p) :
    sectionalCurvature g p v w =
      g.inner p v (riemannOp (LeviCivita g) p v w w) /
        (g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2) := by
  rw [sectionalCurvature_def, sectionalCurvatureNumerator_eq_inner_chartRiemann,
    sectionalCurvatureDenominator_def, riemannOp_eq_chartRiemannCLM_apply]

end DifferentialGeometry.Geometry
