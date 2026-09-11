import DifferentialGeometry.Geometry.Curvature.ConformalOperator

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff InnerProductSpace BigOperators
namespace DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [I.Boundaryless] [BoundarylessManifold I M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem ricci_eq_sum_rm (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt g x B)
    (v w : TangentSpace I x) :
    ricciTensor g x v w = ∑ i : Fin 3, metricRm04StandardAt g x (B i) v w (B i) := by
  classical
  have hd : Module.finrank ℝ E = 3 := by
    change Module.finrank ℝ (TangentSpace I x) = 3
    simpa using Module.finrank_eq_card_basis B
  let e : Fin (Module.finrank ℝ E) ≃ Fin 3 := finCongr hd
  have hB' (i j : Fin (Module.finrank ℝ E)) :
      g.inner x (B (e i)) (B (e j)) = if i = j then (1 : ℝ) else 0 := by
    rw [hB]
    simp only [delta3, Equiv.apply_eq_iff_eq]
  rw [ricciTensor_eq_orthonormal_trace g x v w (fun i => B (e i)) hB']
  calc
    _ = ∑ i, metricRm04StandardAt g x (B (e i)) v w (B (e i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (g.symm x _ _).trans (rm04_eq_inner_riem g x (B (e i)) v w (B (e i))).symm
    _ = _ := e.sum_comp (fun i => metricRm04StandardAt g x (B i) v w (B i))

theorem inner_traceNormalizedCurvatureOperatorAt_eq_scalar_sub_two_ricci
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt g x B)
    (c : EuclideanSpace ℝ (Fin 3)) :
    ⟪traceNormalizedCurvatureOperatorAt g x B c, c⟫_ℝ =
      metricScalarAt g x * ‖c‖ ^ 2 -
        2 * ricciTensor g x (bivectorNormalAt x B c) (bivectorNormalAt x B c) := by
  let R := fun i j k l : Fin 3 => metricRm04StandardAt g x (B i) (B j) (B k) (B l)
  have hR : IsAlgCurvForm (metricRm04StandardAt g x) :=
    mem_algebraicCurvatureTensorSubmodule.mp (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  have hzeroF (i k l : Fin 3) : R i i k l = 0 := by
    have hz := hR.anti_first (B i) (B i) (B k) (B l)
    change R i i k l = -R i i k l at hz
    linarith
  have hzeroL (i j k : Fin 3) : R i j k k = 0 := by
    have hz := hR.anti_last (B i) (B j) (B k) (B k)
    change R i j k k = -R i j k k at hz
    linarith
  have hpair (i j k l : Fin 3) : R i j k l = R k l i j :=
    hR.pair_swap (B i) (B j) (B k) (B l)
  have hfirst (i j k l : Fin 3) : R i j k l = -R j i k l :=
    hR.anti_first (B i) (B j) (B k) (B l)
  have hlast (i j k l : Fin 3) : R i j k l = -R i j l k :=
    hR.anti_last (B i) (B j) (B k) (B l)
  have htranspose (i j k l : Fin 3) : R i j k l = R l k j i := by
    rw [hpair i j k l, hfirst k l i j, hlast l k i j, neg_neg]
  rw [traceNormalizedCurvatureOperatorAt_inner_self,
    ← trace_traceNormalizedCurvatureOperatorMatrixAt g x B hB,
    EuclideanSpace.real_norm_sq_eq]
  simp only [bivectorNormalAt, map_add, map_sub, map_smul, add_apply, sub_apply,
    smul_apply, smul_eq_mul]
  simp_rw [ricci_eq_sum_rm g x B hB]
  simp only [Matrix.trace, Matrix.diag, traceNormalizedCurvatureOperatorMatrixAt_apply,
    Fin.sum_univ_three, bivectorIndex3, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hEval (i j k l : Fin 3) : metricRm04StandardAt g x (B i) (B j) (B k) (B l) = R i j k l := rfl
  simp only [hEval, hzeroF, hzeroL]
  rw [hpair 1 0 0 1, hpair 2 0 0 2, hpair 2 1 1 2,
    htranspose 0 2 1 0, htranspose 1 2 1 0, htranspose 1 2 2 0,
    hpair 2 1 0 2, hpair 1 2 0 1, hfirst 1 0 2 1, hfirst 2 0 1 2,
    hlast 0 1 1 2, hlast 0 2 1 2]
  ring

end DifferentialGeometry.Geometry.Curvature
