import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture

set_option autoImplicit false
noncomputable section
open Set Manifold Function
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem isCompact_riemannianClosedBallOf_of_metric_lower_on_opens
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (U : TopologicalSpace.Opens N) (f : U → M)
    (hf : IsLocalDiffeomorph J I ∞ f) (hinj : Injective f)
    (p : U) {r R L : ℝ} (hR : 0 < R) (hL : 0 < L) (hr : r < R / L)
    (hcompact : IsCompact (riemannianClosedBallOf h p.val R))
    (hsource : riemannianClosedBallOf h p.val R ⊆ U)
    (hlower : ∀ x : U, x.val ∈ riemannianClosedBallOf h p.val R →
      ∀ v : TangentSpace J x, h.inner x.val v v ≤ L ^ 2 *
        g.inner (f x) (mfderiv J I f x v) (mfderiv J I f x v)) :
    IsCompact (riemannianClosedBallOf g (f p) r) := by
  let : FiniteDimensional ℝ E :=
    Module.Finite.of_surjective ((hf p).mfderivToContinuousLinearEquiv (by decide)).toLinearMap
      ((hf p).mfderivToContinuousLinearEquiv (by decide)).surjective
  have hpre : IsCompact {x : U | x.val ∈ riemannianClosedBallOf h p.val R} :=
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hcompact
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hsource)
  have himage := hpre.image hf.contMDiff.continuous
  have hclosed : IsClosed (riemannianClosedBallOf g (f p) r) :=
    isClosed_le (Riemannian.continuous_riemannianEDist g (f p)) continuous_const
  apply himage.of_isClosed_subset hclosed
  intro y hy
  apply ball_subset_image_of_metric_lower_on_opens g h U f hf hinj p
    hR hL hcompact hsource hlower
  exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (div_pos hR hL)).mpr hr)

end DifferentialGeometry.Geometry.Metric
