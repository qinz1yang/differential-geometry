import DifferentialGeometry.Geometry.Metric.Approximation.QuadraticBounds
import DifferentialGeometry.Geometry.Metric.Comparison.InverseHGI

noncomputable section
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PartialDiffeomorph

universe u v
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem inverse_mem_closedBall_of_metric_approximation
    (g : SmoothRiemannianMetric I M) (gTarget : SmoothRiemannianMetric I N)
    (Φ : PartialDiffeomorph I I M N ∞) (o : M) {R A ε : ℝ} {p : ℕ}
    (hA : 0 ≤ A) (hmargin : 2 * A < R) (hε : ε ≤ 3 / 4)
    (hcpt : IsCompact (riemannianClosedBallOf g o R))
    (hΦ : PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g o R) p ε g gTarget)
    (y : N) (hy : y ∈ riemannianClosedBallOf gTarget (Φ o) A) :
    y ∈ Φ.target ∧ Φ.symm y ∈ riemannianClosedBallOf g o R ∧
      Φ.symm y ∈ riemannianClosedBallOf g o (2 * A) := by
  have hR : 0 < R := (mul_nonneg (by norm_num) hA).trans_lt hmargin
  have hlower (x : M) (hx : x ∈ riemannianClosedBallOf g o R) (v : TangentSpace I x) :
      g.inner x v v ≤ (2 : ℝ) ^ 2 * gTarget.inner (Φ x)
        (mfderiv I I Φ x v) (mfderiv I I Φ x v) := by
    have h := (hΦ.quadratic_bounds hx v).1
    have hnn : 0 ≤ g.inner x v v := metric_inner_self_nonneg g x v
    have he := mul_le_mul_of_nonneg_right hε hnn
    nlinarith
  obtain ⟨s, hsA, hsR⟩ := exists_between (show A < R / 2 by linarith)
  have hs : 0 < s := hA.trans_lt hsA
  have hy' : riemannianEDistOf gTarget (Φ o) y < ENNReal.ofReal s :=
    (show riemannianEDistOf gTarget (Φ o) y ≤ ENNReal.ofReal A from hy).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hs).mpr hsA)
  have hc := PDE.RicciFlow.Perelman.KappaSolutions.inverse_mem_closedBall_of_metric_lower_HGI
    g gTarget Φ o hR (by norm_num : (0 : ℝ) < 2) (show A < R / 2 by linarith)
      hcpt hΦ.1 hlower y hy
  have hd := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_symm_le_of_metric_lower_on_compact_ball_HGI
    g gTarget Φ o hR (by norm_num : (0 : ℝ) < 2) hs hsR hcpt hΦ.1 hlower y hy'
  refine ⟨hc.1, hc.2, ?_⟩
  change riemannianEDistOf g o (Φ.symm y) ≤ ENNReal.ofReal (2 * A)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact hd.trans (mul_le_mul' le_rfl hy)


end DifferentialGeometry.PartialDiffeomorph
