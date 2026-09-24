import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

noncomputable section

open Set Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem isCompact_riemannianClosedBallOf_localPullMetric
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (p : M) (r : ℝ)
    (hcompact : IsCompact (riemannianClosedBallOf g (f p) r))
    (hball : riemannianClosedBallOf g (f p) r ⊆ range f) :
    IsCompact (riemannianClosedBallOf (localPullMetric g f hf) p r) := by
  have hemb : _root_.Topology.IsOpenEmbedding f :=
    .of_continuous_injective_isOpenMap hf.contMDiff.continuous hinj hf.isOpenMap
  have hK : IsCompact (f ⁻¹' riemannianClosedBallOf g (f p) r) :=
    hemb.isEmbedding.isInducing.isCompact_preimage' hcompact hball
  have hclosed : IsClosed (riemannianClosedBallOf (localPullMetric g f hf) p r) :=
    isClosed_le (by
      unfold riemannianEDistOf
      exact Riemannian.continuous_riemannianEDist _ p) continuous_const
  apply hK.of_isClosed_subset hclosed
  intro x hx
  have hambient := edistOf_le_of_quad_of_localDiffeomorph
    (localPullMetric g f hf) g f hf (c := 1) zero_lt_one
    (fun z v => by rw [localPullMetric_inner, one_mul]) p x
  simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hambient
  exact hambient.trans hx

variable [FiniteDimensional ℝ F] [T2Space N]

theorem exists_lift_isCompact_riemannianClosedBallOf_localPullMetric
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (x : N) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (riemannianClosedBallOf g x R))
    (hball : riemannianBallOf g x R ⊆ range f) :
    ∃ p : M, f p = x ∧ ∀ r : ℝ, r < R →
      IsCompact (riemannianClosedBallOf (localPullMetric g f hf) p r) := by
  have hx : x ∈ riemannianBallOf g x R := by
    change riemannianEDistOf g x x < ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hR
  obtain ⟨p, hp⟩ := hball hx
  refine ⟨p, hp, ?_⟩
  intro r hr
  have hinner : riemannianClosedBallOf g x r ⊆ riemannianBallOf g x R := by
    intro y hy
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hr)
  have hclosed : IsClosed (riemannianClosedBallOf g x r) :=
    isClosed_le (by
      unfold riemannianEDistOf
      exact Riemannian.continuous_riemannianEDist g x) continuous_const
  apply isCompact_riemannianClosedBallOf_localPullMetric g f hf hinj p r
  · rw [hp]
    exact hcompact.of_isClosed_subset hclosed (riemannianClosedBallOf_mono g x hr.le)
  · rw [hp]
    exact hinner.trans hball

end DifferentialGeometry.Geometry.Metric
