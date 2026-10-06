/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Metric.JoinJets
import DifferentialGeometry.Geometry.Operator.JetComparison

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

/-- Smooth metrics that agree on an open set give the same Hessian at each
point of its closure. -/
theorem hessFun_eq_of_metric_eqOn_open_closure
    (g h : SmoothRiemannianMetric I M) (O : TopologicalSpace.Opens M)
    (heq : ∀ y ∈ O, ∀ v w : TangentSpace I y, h.inner y v w = g.inner y v w)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (x : M) (hx : x ∈ closure (O : Set M)) (v w : TangentSpace I x) :
    hessFun h f x v w = hessFun g f x v w := by
  have hj (k : ℕ) :=
    DifferentialGeometry.Geometry.Metric.metricCovDeriv_eq_of_eqOn_open_closure
      h g g O heq x hx k
  have hn (k : ℕ) : metricDerivNorm k h g g x = 0 := by
    unfold metricDerivNorm metricDiffCovDerivAt
    rw [hj k, sub_self, (Tensor0SBundle.normSq0S_eq_zero_iff g x (k + 2) 0).mpr rfl,
      Real.sqrt_zero]
  have hh := abs_hessFun_sub_le_of_small_metric_derivatives g h f hf x 0
    (by norm_num) (fun k _ => (hn k).le) v w
  simpa only [mul_zero, zero_mul, abs_nonpos_iff, sub_eq_zero] using hh

end DifferentialGeometry.Geometry.Operator
