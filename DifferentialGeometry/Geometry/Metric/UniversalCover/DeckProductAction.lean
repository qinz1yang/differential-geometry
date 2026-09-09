import DifferentialGeometry.Geometry.Metric.UniversalCover.DeckProductConjugation

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N] [ConnectedSpace N]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] {K : Type*} [TopologicalSpace K]
  {J : ModelWithCorners ℝ E' K}
  {M : Type*} [TopologicalSpace M] [ChartedSpace K M]
  [IsManifold J ∞ M] [T2Space M] [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

theorem exists_affine_product_deck_action_of_scalar_ne_zero
    (g : SmoothRiemannianMetric I N) (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x, DifferentialGeometry.Geometry.Curvature.metricScalarAt g x ≠ 0)
    (G : SmoothRiemannianMetric J M)
    (F : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) J (N × ℝ) (UniversalCover M) ∞)
    (hF : Diffeomorph.pullbackMetricCross (liftedMetric G) F =
      g.prod (euclideanMetric (E := ℝ)))
    (a : FundamentalGroup M (default : M)) :
    ∃ (φ : N ≃ₘ⟮I, I⟯ N) (ε c : ℝ),
      (ε = 1 ∨ ε = -1) ∧ Diffeomorph.pullbackMetric g φ = g ∧
        ∀ y r, a • F (y, r) = F (φ y, ε * r + c) := by
  have hdeck : Diffeomorph.pullbackMetricCross (liftedMetric G) (deckDiffeo a) =
      liftedMetric G := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact deck_inner G a x v w
  obtain ⟨φ, ε, c, hε, hφ, hconj⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_affine_product_conjugate_of_isometry
      g hdim hscalar (liftedMetric G) F hF (deckDiffeo a) hdeck
  refine ⟨φ, ε, c, hε, hφ, ?_⟩
  intro y r
  have h := congrArg F (hconj y r)
  change F (F.symm (a • F (y, r))) = F (φ y, ε * r + c) at h
  rw [F.apply_symm_apply] at h
  exact h

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
