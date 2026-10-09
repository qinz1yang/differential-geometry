import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveOpenCore
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.DerivativeAtZero

/-!
# Normal charts of a finite-order metric as partial diffeomorphisms (lane CMS3-SLICE, group G2)

`exists_uniform_normal_partialDiffeomorph`: on a compact set `K` there is a uniform radius `ρ > 0` such
that for every `x ∈ K` the normal chart of CM1.d (`exists_uniform_normal_charts`) is a `C^r` partial
diffeomorphism `e : E → M` with source the `g_x`-ball of radius `ρ`, target `ball x ρ`, `e = exp_x` on
its source, `d(x, e v) = |v|_{g_x}`, source balanced (`t • v` for `|t| ≤ 1`), `e 0 = x` and
`d e (0) = id` (`hasMFDerivAt_expMap_zero`). This is the finite-order replacement of the smooth suite's
diagonal inverse branches in the S3-SLICE route.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

section Packaging

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- An open partial homeomorphism `E → M` that is `C^n` both ways, as a partial diffeomorphism. -/
def partialDiffeomorphOfContMDiffOn {n : WithTop ℕ∞} (e : OpenPartialHomeomorph E M)
    (h₁ : ContMDiffOn 𝓘(ℝ, E) I n e e.source) (h₂ : ContMDiffOn I 𝓘(ℝ, E) n e.symm e.target) :
    PartialDiffeomorph 𝓘(ℝ, E) I E M n where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := h₁
  contMDiffOn_invFun := h₂

end Packaging

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **Uniform normal charts as `C^r` partial diffeomorphisms** (`2 ≤ r`). -/
theorem exists_uniform_normal_partialDiffeomorph
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ > 0, ∀ x ∈ K, ∃ e : PartialDiffeomorph 𝓘(ℝ, E) I E M (r : ℕ∞ω),
      e.source = {v : E | g.inner x v v < ρ ^ 2} ∧ e.target = ball x ρ ∧
      (∀ v ∈ e.source, e v = g.expMap (⟨x, v⟩ : TangentBundle I M)) ∧
      (∀ v ∈ e.source, dist x (e v) = Real.sqrt (g.inner x v v)) ∧
      (∀ v ∈ e.source, ∀ t ∈ Icc (-1 : ℝ) 1, t • v ∈ e.source) ∧
      (0 : E) ∈ e.source ∧ e 0 = x ∧
      HasMFDerivAt 𝓘(ℝ, E) I e 0 (ContinuousLinearMap.id ℝ E) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨ρ, hρ, hch⟩ := g.exists_uniform_normal_charts hr hnorm hK
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨e₀, hsrc, htgt, hexp, hsm, hsymm, hdist⟩ := hch x hx
  set e := partialDiffeomorphOfContMDiffOn e₀ hsm hsymm with he
  have hsrc' : e.source = {v : E | g.inner x v v < ρ ^ 2} := hsrc
  have hexp' : ∀ v ∈ e.source, e v = g.expMap (⟨x, v⟩ : TangentBundle I M) :=
    fun v hv => (hexp v hv).2
  have h0 : (0 : E) ∈ e.source := by
    rw [hsrc']
    change g.inner x 0 0 < ρ ^ 2
    simp only [map_zero]
    positivity
  have he0 : e 0 = x := by
    rw [hexp' 0 h0]
    exact g.expMap_zero hr1 x
  have hball : ∀ v ∈ e.source, ∀ t ∈ Icc (-1 : ℝ) 1, t • v ∈ e.source := by
    intro v hv t ht
    rw [hsrc'] at hv ⊢
    change g.inner x (t • v) (t • v) < ρ ^ 2
    have hsm' : g.inner x (t • v) (t • v) = t ^ 2 * g.inner x v v :=
      DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self g x t v
    rw [hsm']
    have hnn := DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g x v
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hv' : g.inner x v v < ρ ^ 2 := hv
    nlinarith
  have hderiv : HasMFDerivAt 𝓘(ℝ, E) I e 0 (ContinuousLinearMap.id ℝ E) := by
    have h := g.hasMFDerivAt_expMap_zero hr1 x
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [e.open_source.mem_nhds h0] with v hv
    exact hexp' v hv
  exact ⟨e, hsrc', htgt, hexp', hdist, hball, h0, he0, hderiv⟩

end DifferentialGeometry.Geometry.FiniteSoul
