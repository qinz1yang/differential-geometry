import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteMetricFlow
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteOrder

/-!
# Consumer of G5-M: continuity of a fixed finite-order geodesic flow in the initial data

`finite_geodesicFlow_tendsto_of_tendsto`: for one `C^{r+1}` metric (`1 ≤ r`), the constant
sequence of metrics converges in every chart, so G5-M gives continuity of CM-P's geodesic flow in
the initial vector along sequences, on any time interval `[0, T]` inside the flow domains.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Consumer of G5-M.** The geodesic flow of a fixed `C^{r+1}` metric, `1 ≤ r`, is sequentially
continuous in the initial vector, at every time of `[0, T]` inside the flow domains. -/
theorem finite_geodesicFlow_tendsto_of_tendsto {r : ℕ∞} (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : ℕ → TangentBundle I M} {pInf : TangentBundle I M} (hp : Tendsto p atTop (𝓝 pInf))
    {T : ℝ} (hT : 0 ≤ T) (hdom : ∀ t ∈ Icc 0 T, (pInf, t) ∈ g.geodesicFlowDomain)
    (hdomi : ∀ i, ∀ t ∈ Icc 0 T, (p i, t) ∈ g.geodesicFlowDomain) :
    ∀ t ∈ Icc 0 T, Tendsto (fun i => g.geodesicFlow (p i) t) atTop
      (𝓝 (g.geodesicFlow pInf t)) :=
  tendsto_geodesicFlow_of_chart_C1_tendsto hr (fun _ => g) g
    (fun _ _ _ _ => MapCPConvergenceOn.const_seq _) hp hT hdom hdomi

end DifferentialGeometry.Geometry.Riemannian.Geodesic
