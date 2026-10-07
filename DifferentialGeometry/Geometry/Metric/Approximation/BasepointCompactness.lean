import DifferentialGeometry.Geometry.Metric.Approximation.QuadraticBounds
import DifferentialGeometry.Geometry.Measure.PartialDiffeomorphComparison
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Analysis.Integration.Measure.BallPacking
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PartialDiffeomorph

open Integral.Measure (riemannianVolumeMeasure)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_isCompact_basepoint_images_of_metric_bounds
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (hvol : riemannianVolumeMeasure I M g Set.univ < ⊤)
    (x : M) {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    ∃ K : Set M, IsCompact K ∧
      ∀ (Φ : PartialDiffeomorph I I M M ∞),
        riemannianClosedBallOf g x r ⊆ Φ.source →
        (∀ y ∈ riemannianClosedBallOf g x r, ∀ v : TangentSpace I y,
          g.inner y v v ≤ C * g.inner (Φ y) (mfderiv I I Φ y v) (mfderiv I I Φ y v) ∧
          g.inner (Φ y) (mfderiv I I Φ y v) (mfderiv I I Φ y v) ≤ C * g.inner y v v) →
        Φ x ∈ K := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  have hball (y : M) {s : ℝ} (hs : 0 < s) :
      riemannianBallOf g y s = Metric.ball y s := by
    ext z
    change edist y z < ENNReal.ofReal s ↔ dist z y < s
    rw [edist_dist, dist_comm, ENNReal.ofReal_lt_ofReal_iff hs]
  have hclosed (y : M) {s : ℝ} (hs : 0 ≤ s) :
      riemannianClosedBallOf g y s = Metric.closedBall y s := by
    ext z
    change edist y z ≤ ENNReal.ofReal s ↔ dist z y ≤ s
    rw [edist_dist, dist_comm, ENNReal.ofReal_le_ofReal_iff hs]
  let _ : ProperSpace M := ⟨fun y s => by
    by_cases hs : 0 ≤ s
    · rw [← hclosed y hs]
      exact hg.closedEBall_isCompact y s
    · rw [Metric.closedBall_eq_empty.mpr (lt_of_not_ge hs)]
      exact isCompact_empty⟩
  let μ := riemannianVolumeMeasure I M g
  let _ : MeasureTheory.IsFiniteMeasure μ := ⟨hvol⟩
  let _ : μ.IsOpenPosMeasure := Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure g
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (C ^ Module.finrank ℝ E))
  have hc : 0 < c := ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos hC _))
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  let m := μ (Metric.ball x r)
  have hm : 0 < m := Metric.measure_ball_pos μ x hr
  let v := c⁻¹ * m
  have hv : 0 < v := ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hctop) hm.ne'
  let S : Set M := {y | ∃ Φ : PartialDiffeomorph I I M M ∞,
    riemannianClosedBallOf g x r ⊆ Φ.source ∧
    (∀ z ∈ riemannianClosedBallOf g x r, ∀ w : TangentSpace I z,
      g.inner z w w ≤ C * g.inner (Φ z) (mfderiv I I Φ z w) (mfderiv I I Φ z w) ∧
      g.inner (Φ z) (mfderiv I I Φ z w) (mfderiv I I Φ z w) ≤ C * g.inner z w w) ∧
    Φ x = y}
  have hL : 0 < C + 1 := by linarith
  have hmass : ∀ y ∈ S, v ≤ μ (Metric.ball y ((C + 1) * r)) := by
    rintro y ⟨Φ, hsource, hquad, rfl⟩
    have hAS : Metric.ball x r ⊆ Φ.source := by
      intro z hz
      apply hsource
      have hz' : z ∈ riemannianBallOf g x r := by rwa [hball x hr]
      exact (show riemannianEDistOf g x z < ENNReal.ofReal r from hz').le
    have himage : Φ '' Metric.ball x r ⊆ Metric.ball (Φ x) ((C + 1) * r) := by
      rintro _ ⟨z, hz, rfl⟩
      rw [← hball (Φ x) (mul_pos hL hr)]
      have hz' : z ∈ riemannianBallOf g x r := by rwa [hball x hr]
      have hupper : ∀ y ∈ riemannianClosedBallOf g x r, ∀ w : TangentSpace I y,
          g.inner (Φ y) (mfderiv I I Φ y w) (mfderiv I I Φ y w) ≤
            (C + 1) ^ 2 * g.inner y w w := by
        intro y hy w
        have hnn : 0 ≤ g.inner y w w := by
          by_cases hw : w = 0
          · simp [hw]
          · exact (g.pos y w hw).le
        have hcoef : C ≤ (C + 1) ^ 2 := by nlinarith
        exact (hquad y hy w).2.trans (mul_le_mul_of_nonneg_right hcoef hnn)
      have hd := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
        g g Φ x z hr hL hsource hupper hz'
      change riemannianEDistOf g (Φ x) (Φ z) < ENNReal.ofReal ((C + 1) * r)
      rw [ENNReal.ofReal_mul hL.le]
      exact hd.trans_lt ((ENNReal.mul_lt_mul_iff_right
        (ENNReal.ofReal_pos.mpr hL).ne' ENNReal.ofReal_ne_top).mpr hz')
    have hlower := Geometry.Measure.riemannianVolumeMeasure_le_image_of_partialDiffeomorph_metric_le
      g g Φ measurableSet_ball hAS hC (fun z hz w => by
        have hz' : z ∈ riemannianBallOf g x r := by rwa [hball x hr]
        have hzclosed : z ∈ riemannianClosedBallOf g x r :=
          (show riemannianEDistOf g x z < ENNReal.ofReal r from hz').le
        exact (hquad z hzclosed w).1)
    apply (ENNReal.inv_mul_le_iff hc.ne' hctop).mpr
    exact hlower.trans (mul_le_mul' le_rfl (MeasureTheory.measure_mono himage))
  have hbounded := MeasureTheory.isBounded_of_uniform_ball_measure_lower_bound μ
    (mul_pos hL hr) hv hmass
  refine ⟨closure S, hbounded.isCompact_closure, ?_⟩
  intro Φ hsource hquad
  exact subset_closure ⟨Φ, hsource, hquad, rfl⟩

theorem exists_isCompact_basepoint_images_of_metric_approximation
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (hvol : riemannianVolumeMeasure I M g Set.univ < ⊤)
    (x : M) {r : ℝ} (hr : 0 < r) :
    ∃ K : Set M, IsCompact K ∧
      ∀ (Φ : PartialDiffeomorph I I M M ∞) {p : ℕ} {ε : ℝ},
        isMetricApproximationOn Φ (riemannianClosedBallOf g x r) p ε g g →
        ε ≤ 1 / 2 → Φ x ∈ K := by
  obtain ⟨K, hK, hmaps⟩ := exists_isCompact_basepoint_images_of_metric_bounds
    g hg hvol x hr (C := 2) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro Φ p ε hΦ hε
  apply hmaps Φ hΦ.1
  intro y hy v
  obtain ⟨hl, hu⟩ := hΦ.quadratic_bounds hy v
  have hnn : 0 ≤ g.inner y v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos y v hv).le
  have hb := mul_le_mul_of_nonneg_right hε hnn
  constructor <;> nlinarith only [hl, hu, hb, hnn]

end DifferentialGeometry.PartialDiffeomorph
