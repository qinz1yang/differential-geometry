import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointLevelCircle

/-!
# Consumer of LFR23's level lemmas

`endpoint_sphere_jordan`: under LFR23's endpoint hypotheses (`δ ≤ 1/24000000`), for every
`a ∈ [1, 9]` the sphere `{r = a}` is the frontier of the closed ball `B̄(z₀, a)`, is path connected,
and is a Jordan circle — exactly the input of the Jordan-domain recognition used for LFR23's disk
clause.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Function
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  {r : ℕ∞}

/-- **Consumer.** The spheres `{r = a}`, `a ∈ [1, 9]`, are frontiers of the balls, path connected,
and Jordan circles. -/
theorem endpoint_sphere_jordan
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2)
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 24000000) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) {a : ℝ}
    (ha : a ∈ Icc (1 : ℝ) 9) :
    frontier (closedBall z₀ a) = sphere z₀ a ∧ IsPathConnected (sphere z₀ a) ∧
      ∃ c : Circle → M, Continuous c ∧ Injective c ∧ range c = sphere z₀ a := by
  have hδ1 : δ ≤ 1 / 9600 := hδ'.trans (by norm_num)
  exact ⟨frontier_closedBall_eq_sphere_of_endpoint g hr hnorm hsec hδ hδ1 hq0 hqnn hdist hdense
      ⟨by linarith [ha.1], by linarith [ha.2]⟩,
    isPathConnected_sphere_of_endpoint g hr hnorm hsec hδ hδ1 hq0 hqnn hdist hdense ha,
    exists_circle_sphere_of_endpoint g hr hnorm hsec hdim hδ hδ' hq0 hqnn hdist hdense ha⟩

end DifferentialGeometry.Geometry.Collapse
