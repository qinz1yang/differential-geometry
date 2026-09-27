import DifferentialGeometry.Analysis.Calculus.Derivative.SuperlevelMonotonicity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

theorem metricScalarAt_le_max_terminal_of_deriv_nonneg_above
    {D : ℕ → RealTimeInterval} (S : ∀ n, SolutionOn (I := I) (M := M) (D n))
    (g r gRef rRef : SmoothRiemannianMetric I M) (x : M) {a b t q0 : ℝ}
    (ht : t ∈ Icc a b) (q : ℕ → ℝ)
    (hS : ∀ᶠ n in atTop, IsSolutionOn (S n))
    (hslab : ∀ᶠ n in atTop, Icc a b ⊆ (D n).carrier)
    (hq : ∀ᶠ n in atTop, q n ≤ q0)
    (hderiv : ∀ᶠ n in atTop, ∀ s ∈ Ioo a b, q n < (S n).scalar s x →
      0 ≤ deriv (fun u => (S n).scalar u x) s)
    (hconv : MetricCPConvergenceOn {x} 2 (fun n => (S n).base.metric t) g gRef)
    (hterminal : MetricCPConvergenceOn {x} 2 (fun n => (S n).base.metric b) r rRef) :
    metricScalarAt g x ≤ max q0 (metricScalarAt r x) := by
  have hleft :=
    (hconv.tendstoUniformlyOn_metricScalarAt isCompact_singleton).tendsto_at (mem_singleton x)
  have hright :=
    (hterminal.tendstoUniformlyOn_metricScalarAt isCompact_singleton).tendsto_at
      (mem_singleton x)
  apply le_of_tendsto_of_tendsto hleft (tendsto_const_nhds.max hright)
  filter_upwards [hS, hslab, hq, hderiv] with n hn hslabn hqn hderivn
  have hbound : (S n).scalar t x ≤ max (q n) ((S n).scalar b x) := by
    apply DifferentialGeometry.Analysis.le_max_endpoint_of_deriv_nonneg_above
      (fun s hs => (hn.scalarTime hs hslabn x).continuousWithinAt) ?_ ht
    intro s hs hhigh
    exact ⟨(hn.scalarTime hs (Ioo_subset_Icc_self.trans hslabn) x).differentiableAt
      (Ioo_mem_nhds hs.1 hs.2), hderivn s hs hhigh⟩
  exact hbound.trans (max_le_max hqn le_rfl)

end DifferentialGeometry.PDE.RicciFlow
