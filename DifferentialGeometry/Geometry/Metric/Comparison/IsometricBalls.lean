import DifferentialGeometry.Geometry.Comparison.BallCapture
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PartialDiffeomorph

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem image_riemannianClosedBall_eq_of_isometric_on_compact_ball
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M ∞) (p : N)
    {R r : ℝ} (hr : 0 ≤ r) (hbuffer : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hmetric : ∀ x ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace I x,
      g.inner (F x) (mfderiv I I (F : N → M) x v)
        (mfderiv I I (F : N → M) x v) = h.inner x v v) :
    (F : N → M) '' riemannianClosedBallOf h p r = riemannianClosedBallOf g (F p) r := by
  have hR : 0 < R := hr.trans_lt hbuffer
  have hlower : ∀ x ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace I x,
      h.inner x v v ≤ (1 : ℝ) ^ 2 *
        g.inner (F x) (mfderiv I I (F : N → M) x v)
          (mfderiv I I (F : N → M) x v) := by
    intro x hx v
    rw [one_pow, one_mul, hmetric x hx v]
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hxR : riemannianEDistOf h p x < ENNReal.ofReal R :=
      lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hbuffer)
    have hle :=
      DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
        h g F p x hR (show (0 : ℝ) < 1 by norm_num) hsource
        (fun z hz v => by rw [one_pow, one_mul, hmetric z hz v]) hxR
    change riemannianEDistOf g (F p) (F x) ≤ ENNReal.ofReal r
    have hle' : riemannianEDistOf g (F p) (F x) ≤ riemannianEDistOf h p x := by
      simpa only [ENNReal.ofReal_one, one_mul] using hle
    exact hle'.trans hx
  · intro y hy
    obtain ⟨hyt, hx⟩ := symm_mem_riemannianClosedBall_of_metric_lower h g F p hr
      (show (0 : ℝ) < 1 by norm_num) (by simpa using hbuffer) hcpt hsource hlower y hy
    exact ⟨F.symm y, by simpa only [one_mul] using hx, F.right_inv' hyt⟩

theorem image_riemannianBall_eq_of_isometric_on_compact_ball
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M ∞) (p : N)
    {R r : ℝ} (hr : 0 < r) (hbuffer : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hmetric : ∀ x ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace I x,
      g.inner (F x) (mfderiv I I (F : N → M) x v)
        (mfderiv I I (F : N → M) x v) = h.inner x v v) :
    (F : N → M) '' riemannianBallOf h p r = riemannianBallOf g (F p) r := by
  have hR : 0 < R := hr.trans hbuffer
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hxR := hx.trans ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hbuffer)
    have hle :=
      DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
        h g F p x hR (show (0 : ℝ) < 1 by norm_num) hsource
        (fun z hz v => by rw [one_pow, one_mul, hmetric z hz v]) hxR
    exact lt_of_le_of_lt (by simpa only [ENNReal.ofReal_one, one_mul] using hle) hx
  · intro y hy
    have hfin : riemannianEDistOf g (F p) y ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy.le
    let d := (riemannianEDistOf g (F p) y).toReal
    have hd : 0 ≤ d := ENNReal.toReal_nonneg
    have hdr : d < r := (ENNReal.toReal_lt_of_lt_ofReal hy)
    have hdeq : ENNReal.ofReal d = riemannianEDistOf g (F p) y := ENNReal.ofReal_toReal hfin
    have hmem : y ∈ riemannianClosedBallOf g (F p) d := by
      change riemannianEDistOf g (F p) y ≤ ENNReal.ofReal d
      rw [hdeq]
    rw [← image_riemannianClosedBall_eq_of_isometric_on_compact_ball h g F p
      hd (hdr.trans hbuffer) hcpt hsource hmetric] at hmem
    obtain ⟨x, hx, hxy⟩ := hmem
    refine ⟨x, ?_, hxy⟩
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hdr)

end DifferentialGeometry.PartialDiffeomorph

end
