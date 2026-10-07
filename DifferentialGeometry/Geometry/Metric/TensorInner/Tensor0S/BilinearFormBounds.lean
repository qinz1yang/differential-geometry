import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem bilinear_apply_bounds_of_tensor0SFiberNorm_sub_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) {ε : ℝ}
    (herror : tensor0SFiberNorm g x 2
      (((continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ).symm.toContinuousLinearMap.comp
        (B - g.inner x)).uncurryLeft) ≤ ε)
    (v : TangentSpace I x) :
    (1 - ε) * g.inner x v v ≤ B v v ∧ B v v ≤ (1 + ε) * g.inner x v v := by
  let T : Tensor0SSpace 2 I x :=
    ((continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ).symm.toContinuousLinearMap.comp
      (B - g.inner x)).uncurryLeft
  have heval := abs_apply_le_norm0S g x 2 T (fun _ => v)
  have hnn := metric_inner_self_nonneg g x v
  have hprod : (∏ _a : Fin 2, Real.sqrt (g.inner x v v)) = g.inner x v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt hnn]
  change |B v v - g.inner x v v| ≤
    tensor0SFiberNorm g x 2 T * ∏ _a : Fin 2, Real.sqrt (g.inner x v v) at heval
  rw [hprod] at heval
  have habs : |B v v - g.inner x v v| ≤ ε * g.inner x v v :=
    heval.trans (mul_le_mul_of_nonneg_right herror hnn)
  constructor <;> nlinarith [(abs_le.mp habs).1, (abs_le.mp habs).2]

end DifferentialGeometry.Tensor0SBundle
