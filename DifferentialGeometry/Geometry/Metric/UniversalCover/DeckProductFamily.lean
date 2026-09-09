import DifferentialGeometry.Geometry.Metric.UniversalCover.DeckProductAction

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

theorem exists_affine_product_deck_action_for_metric_family
    {τ : Type*} (g : τ → SmoothRiemannianMetric I N)
    (hdim : Module.finrank ℝ E = 2) (t₀ : τ)
    (hscalar : ∀ x, DifferentialGeometry.Geometry.Curvature.metricScalarAt (g t₀) x ≠ 0)
    (G : τ → SmoothRiemannianMetric J M)
    (F : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) J (N × ℝ) (UniversalCover M) ∞)
    (hF : ∀ t, Diffeomorph.pullbackMetricCross (liftedMetric (G t)) F =
      (g t).prod (euclideanMetric (E := ℝ)))
    (a : FundamentalGroup M (default : M)) :
    ∃ (φ : N ≃ₘ⟮I, I⟯ N) (ε c : ℝ),
      (ε = 1 ∨ ε = -1) ∧
        (∀ t, Diffeomorph.pullbackMetric (g t) φ = g t) ∧
        ∀ y r, a • F (y, r) = F (φ y, ε * r + c) := by
  let Φ := F.trans ((deckDiffeo (I := J) a).trans F.symm)
  have hconj (t : τ) : Diffeomorph.pullbackMetricCross
      ((g t).prod (euclideanMetric (E := ℝ))) Φ =
        (g t).prod (euclideanMetric (E := ℝ)) := by
    have hdeck : Diffeomorph.pullbackMetricCross (liftedMetric (G t)) (deckDiffeo a) =
        liftedMetric (G t) := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rw [Diffeomorph.pullbackMetricCross_inner]
      exact deck_inner (G t) a x v w
    have hFsym := Diffeomorph.pullbackMetricCross_symm_eq_iff.mp (hF t)
    dsimp [Φ]
    rw [← Diffeomorph.pullbackMetricCross_trans,
      ← Diffeomorph.pullbackMetricCross_trans, hFsym, hdeck, hF]
  obtain ⟨φ, ψ, hΦ, _, hψ⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_prod_isometries_of_scalar_ne_zero
      (g t₀) hdim hscalar Φ (hconj t₀)
  obtain ⟨ε, hε, haff⟩ := Diffeomorph.real_affine_of_pullbackMetric_eq_euclidean ψ hψ
  refine ⟨φ, ε, ψ 0, hε, ?_, ?_⟩
  · intro t
    have hmetric := hconj t
    rw [hΦ, Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
      Diffeomorph.pullbackMetric_prodCongr] at hmetric
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    have h := congrArg (fun q : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (N × ℝ) =>
      q.inner (y, 0)
        (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, 0) from (v, 0))
        (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, 0) from (w, 0))) hmetric
    rw [SmoothRiemannianMetric.prod_inner, SmoothRiemannianMetric.prod_inner,
      mfderiv_fst, mfderiv_snd] at h
    change (Diffeomorph.pullbackMetric (g t) φ).inner y v w +
      (Diffeomorph.pullbackMetric (euclideanMetric (E := ℝ)) ψ).inner 0 0 0 =
        (g t).inner y v w + (euclideanMetric (E := ℝ)).inner 0 0 0 at h
    simpa only [map_zero, zero_apply, add_zero] using h
  · intro y r
    have h := congrArg (fun e : Diffeomorph (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, ℝ)) (N × ℝ) (N × ℝ) ∞ => F (e (y, r))) hΦ
    change F (F.symm (a • F (y, r))) = F (φ y, ψ r) at h
    rw [F.apply_symm_apply, haff] at h
    exact h

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
