import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.Comparison.IsometricBalls
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
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

end

noncomputable section

open Set Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Metric

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem image_riemannianBallOf_localPullMetric
    (g : SmoothRiemannianMetric I N) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Function.Injective f)
    (p : M) {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf (localPullMetric g f hf) p R)) :
    f '' riemannianBallOf (localPullMetric g f hf) p r = riemannianBallOf g (f p) r := by
  let V := hf.image
  let e : M ≃ₘ⟮I, I⟯ V := DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage f hf hinj
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I V ⟨e p⟩
  let Φ : PartialDiffeomorph I I M N ∞ := e.toPartialDiffeomorph.trans iV
  have hsource : Φ.source = univ := by
    ext x
    change (x ∈ (univ : Set M) ∧ e x ∈ (univ : Set V)) ↔ x ∈ (univ : Set M)
    simp only [mem_univ, and_self]
  exact DifferentialGeometry.PartialDiffeomorph.image_riemannianBall_eq_of_isometric_on_compact_ball
    (localPullMetric g f hf) g Φ p hr hrR hcpt
    (by rw [hsource]; exact subset_univ _)
    (fun x _ v => (localPullMetric_inner g f hf x v v).symm)

theorem image_riemannianClosedBallOf_localPullMetric
    (g : SmoothRiemannianMetric I N) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Function.Injective f)
    (p : M) {R r : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf (localPullMetric g f hf) p R)) :
    f '' riemannianClosedBallOf (localPullMetric g f hf) p r = riemannianClosedBallOf g (f p) r := by
  let V := hf.image
  let e : M ≃ₘ⟮I, I⟯ V := DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage f hf hinj
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I V ⟨e p⟩
  let Φ : PartialDiffeomorph I I M N ∞ := e.toPartialDiffeomorph.trans iV
  have hsource : Φ.source = univ := by
    ext x
    change (x ∈ (univ : Set M) ∧ e x ∈ (univ : Set V)) ↔ x ∈ (univ : Set M)
    simp only [mem_univ, and_self]
  exact DifferentialGeometry.PartialDiffeomorph.image_riemannianClosedBall_eq_of_isometric_on_compact_ball
    (localPullMetric g f hf) g Φ p hr hrR hcpt
    (by rw [hsource]; exact subset_univ _)
    (fun x _ v => (localPullMetric_inner g f hf x v v).symm)

end DifferentialGeometry.Geometry.Metric
