import DifferentialGeometry.Geometry.Operator.MetricComparison
import DifferentialGeometry.Geometry.Connection.Convergence.DifferenceDerivativeBound
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self

noncomputable section
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricUniformEquivalentOn_of_metricDerivNorm_le_half
    (K : Set M) (g h : SmoothRiemannianMetric I M)
    (hsmall : ∀ x ∈ K, metricDerivNorm 0 h g g x ≤ 1 / 2) :
    MetricUniformEquivalentOn K g h 2 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have heq := metricUniformEquivalentOn_of_quadFormDiff
    (K := K) (g := g) (h := h) (δ := 1 / 2)
    (by norm_num) (by norm_num) ?_
  · norm_num only at heq
    exact heq
  · intro x hx v
    have hnn : 0 ≤ g.inner x v v := metric_inner_self_nonneg g x v
    have hb := metricDifference_abs_le h g g x v v
    rw [mul_assoc, Real.mul_self_sqrt hnn] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (hsmall x hx) hnn)

theorem inner_gradFun_le_two_of_metricDerivNorm_le_half
    (g h : SmoothRiemannianMetric I M) (F : M → ℝ) (x : M)
    (hsmall : metricDerivNorm 0 h g g x ≤ 1 / 2) :
    h.inner x (gradFun h F x) (gradFun h F x) ≤
      2 * g.inner x (gradFun g F x) (gradFun g F x) := by
  have heq : MetricUniformEquivalentOn {x} g h 2 :=
    metricUniformEquivalentOn_of_metricDerivNorm_le_half {x} g h (by
      intro y hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact hsmall)
  exact inner_gradFun_le_of_metricUniformEquivalentOn g h heq F (Set.mem_singleton x)

variable [I.Boundaryless] [BoundarylessManifold I M]

theorem abs_hessFun_sub_le_of_small_metric_derivatives
    (g h : SmoothRiemannianMetric I M) (F : M → ℝ)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) (x : M) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 1 → metricDerivNorm k h g g x ≤ ε)
    (v w : TangentSpace I x) :
    |hessFun h F x v w - hessFun g F x v w| ≤
      12 * ε * Real.sqrt (g.inner x (gradFun g F x) (gradFun g F x)) *
        Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have heq : MetricUniformEquivalentOn {x} g h 2 :=
    metricUniformEquivalentOn_of_metricDerivNorm_le_half {x} g h (by
      simpa using (hsmall 0 (by norm_num)).trans hε)
  have hjet : MetricCovDerivOrderBoundOn {x} 1 h g ε := by
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    have hb := covNorm_le_add 1 h g g x
    have hzero : metricCovDerivNorm 1 g g x = 0 := covNorm_self_succ g 0 x
    rw [hzero, zero_add] at hb
    exact hb.trans (hsmall 1 le_rfl)
  apply abs_hessFun_sub_le_of_connectionDifference_bound g h F hF x v w (12 * ε)
  have hb := connectionDifference_gJet_le heq hjet (Set.mem_singleton x) v w
  norm_num only at hb
  exact hb

end DifferentialGeometry.Geometry.Operator
