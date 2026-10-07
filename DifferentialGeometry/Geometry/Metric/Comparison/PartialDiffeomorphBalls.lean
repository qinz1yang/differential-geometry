import DifferentialGeometry.Geometry.Comparison.BallCapture
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance

open Manifold Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem image_riemannianBall_subset_of_metric_upper
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) (p : M)
    {R r a : ℝ} (ha : 0 < a) (hbuffer : r < R)
    (hsource : riemannianClosedBallOf g p R ⊆ Φ.source)
    (hupper : ∀ x ∈ riemannianClosedBallOf g p R, ∀ v : TangentSpace I x,
      h.inner (Φ x) (mfderiv I J (Φ : M → N) x v)
        (mfderiv I J (Φ : M → N) x v) ≤ a ^ 2 * g.inner x v v) :
    (Φ : M → N) '' riemannianBallOf g p r ⊆ riemannianBallOf h (Φ p) (a * r) := by
  rintro y ⟨x, hx, rfl⟩
  have hr : 0 < r := ENNReal.ofReal_pos.mp (bot_le.trans_lt hx)
  have hR : 0 < R := hr.trans hbuffer
  have hxR := hx.trans ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hbuffer)
  have hdist :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      g h Φ p x hR ha hsource hupper hxR
  change riemannianEDistOf h (Φ p) (Φ x) < ENNReal.ofReal (a * r)
  calc
    _ ≤ ENNReal.ofReal a * riemannianEDistOf g p x := hdist
    _ < ENNReal.ofReal a * ENNReal.ofReal r :=
      ENNReal.mul_lt_mul_right (ENNReal.ofReal_ne_zero_iff.mpr ha)
        ENNReal.ofReal_ne_top hx
    _ = ENNReal.ofReal (a * r) := (ENNReal.ofReal_mul ha.le).symm

theorem riemannianBall_subset_image_of_metric_lower
    [FiniteDimensional ℝ E] [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) (p : M)
    {R r b : ℝ} (hb : 0 < b) (hbuffer : b * r < R)
    (hcpt : IsCompact (riemannianClosedBallOf g p R))
    (hsource : riemannianClosedBallOf g p R ⊆ Φ.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf g p R, ∀ v : TangentSpace I x,
      g.inner x v v ≤ b ^ 2 * h.inner (Φ x)
        (mfderiv I J (Φ : M → N) x v) (mfderiv I J (Φ : M → N) x v)) :
    riemannianBallOf h (Φ p) r ⊆ (Φ : M → N) '' riemannianBallOf g p (b * r) := by
  intro y hy
  have hr : 0 < r := ENNReal.ofReal_pos.mp (bot_le.trans_lt hy)
  have hfin : riemannianEDistOf h (Φ p) y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy.le
  let d := (riemannianEDistOf h (Φ p) y).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hdr : d < r := ENNReal.toReal_lt_of_lt_ofReal hy
  have hdeq : ENNReal.ofReal d = riemannianEDistOf h (Φ p) y :=
    ENNReal.ofReal_toReal hfin
  have hyclosed : y ∈ riemannianClosedBallOf h (Φ p) d := by
    change riemannianEDistOf h (Φ p) y ≤ ENNReal.ofReal d
    rw [hdeq]
  have hbdbr : b * d < b * r := mul_lt_mul_of_pos_left hdr hb
  obtain ⟨hyt, hx⟩ := symm_mem_riemannianClosedBall_of_metric_lower g h Φ p
    hd hb (hbdbr.trans hbuffer) hcpt hsource hlower y hyclosed
  refine ⟨Φ.symm y, ?_, Φ.right_inv' hyt⟩
  exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hb hr)).mpr hbdbr)

end DifferentialGeometry.PartialDiffeomorph
