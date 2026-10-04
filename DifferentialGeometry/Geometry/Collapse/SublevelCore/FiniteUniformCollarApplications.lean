import DifferentialGeometry.Geometry.Collapse.SublevelCore.FiniteUniformCollar
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothDirectionsSingleton

/-!
# Consumers of LC49′ and of the singleton direction bridge (B5)

* `exists_uniform_margin_on_frontier_finite`: for a model core `D` of LC51's shape, strict
  negativity on `∂D` against every limit minimizing direction to `n` upgrades to a uniform margin
  `-2α` and a uniform bound on the closure of an open collar of `∂D`.
* `inner_le_of_mem_inwardMinimizingDirections_of_finite`: a margin stated with the finite-metric
  direction set holds for every `v ∈ 𝒰_n(q)` of a complete smooth metric (the form LC48 consumes).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Limit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [ProperSpace N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]

/-- **Uniform margin on a collar of `∂D`** (consumer of LC49′). -/
theorem exists_uniform_margin_on_frontier_finite {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (n : N) {D : Set N} (hDc : IsCompact D) (hin : closedBall n (1 / 2) ⊆ interior D)
    (hout : D ⊆ ball n 2) {O : Set N} (hO : IsOpen O) (hDO : frontier D ⊆ O)
    (V : (x : N) → TangentSpace I x)
    (hV : ContinuousOn (fun x => (⟨x, V x⟩ : TangentBundle I N)) O)
    (hneg : ∀ x ∈ frontier D, ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (V x) v < 0) :
    ∃ α : ℝ, 0 < α ∧ ∀ x ∈ frontier D, ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (V x) v ≤ -(2 * α) := by
  obtain ⟨α, B, hα, hB, U, hUo, hDU, hcpt, hsub, hU⟩ :=
    exists_uniform_collar_of_frontier_finite hr G hGnorm n hDc hin hout hO hDO V hV hneg
  exact ⟨α, hα, fun x hx v hv => (hU x (subset_closure (hDU hx))).2 v hv⟩

end Limit

section Smooth

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Finite-set margins hold on `𝒰_n(q)`** (consumer of B5). -/
theorem inner_le_of_mem_inwardMinimizingDirections_of_finite
    (g : SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) {n q : M}
    {Z : TangentSpace I q} {c : ℝ}
    (hZ : ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g {n} q, g.inner q Z w ≤ c)
    {w : TangentSpace I q} (hw : w ∈ inwardMinimizingDirections g hEnorm n q) :
    g.inner q Z w ≤ c := by
  rw [Bundle.ContMDiffRiemannianMetric.inwardMinimizingDirections_eq_finiteMinimizingDirectionsTo]
    at hw
  exact hZ w hw

end Smooth

end DifferentialGeometry.Geometry.Collapse
