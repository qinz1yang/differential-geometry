import DifferentialGeometry.Geometry.Measure.HyperbolicUniversalCover
import DifferentialGeometry.Geometry.Measure.PartialDiffeomorphComparison
import DifferentialGeometry.Geometry.Metric.Comparison.IntrinsicBallImage
import DifferentialGeometry.Geometry.Metric.Approximation.QuadraticBounds
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

noncomputable section

open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {H H' M N : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {J : ModelWithCorners ℝ E₃ H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

private theorem normalized_ball_volume_le_source_closed_ball
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (p : M) {δ : ℝ} (hδ : 0 < δ) (Φ : PartialDiffeomorph I J M N ∞)
    (hcompact : IsCompact (riemannianClosedBallOf g p (4 * δ)))
    (hsub : riemannianClosedBallOf g p (4 * δ) ⊆ Φ.source)
    (hlower : ∀ y ∈ riemannianClosedBallOf g p (4 * δ), ∀ v : TangentSpace I y,
      (1 / 4 : ℝ) * g.inner y v v ≤ h.inner (Φ y) (mfderiv I J Φ y v) (mfderiv I J Φ y v))
    (hupper : ∀ y ∈ riemannianClosedBallOf g p (4 * δ), ∀ v : TangentSpace I y,
      h.inner (Φ y) (mfderiv I J Φ y v) (mfderiv I J Φ y v) ≤ 4 * g.inner y v v) :
    riemannianVolumeMeasure J N (scaleMetric (1 / 4) (by norm_num) h)
      (riemannianBallOf (scaleMetric (1 / 4) (by norm_num) h) (Φ p) (δ / 2)) ≤
      riemannianVolumeMeasure I M g (riemannianClosedBallOf g p (4 * δ)) := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
  let _ : T3Space N := inferInstance
  have hcapture : riemannianBallOf h (Φ p) δ ⊆ Φ '' riemannianClosedBallOf g p (4 * δ) := by
    apply DifferentialGeometry.PartialDiffeomorph.riemannianBallOf_subset_image_of_metric_lower
      g h Φ (C := 2) (r := δ) (by norm_num) hcompact hsub
    · intro y hy v
      have hb := hlower y hy v
      norm_num
      linarith
    · change riemannianEDistOf g p p < ENNReal.ofReal δ
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hδ
    · linarith
  have himage := Geometry.Measure.riemannianVolumeMeasure_image_le_of_partialDiffeomorph_metric_le
    g h Φ hcompact.isClosed.measurableSet hsub (by norm_num : (0 : ℝ) < 4) hupper
  have hfactor : ENNReal.ofReal (Real.sqrt ((4 : ℝ) ^ Module.finrank ℝ E₃)) = 8 := by norm_num
  rw [hfactor] at himage
  have hmass := (MeasureTheory.measure_mono hcapture).trans himage
  have hscale := riemannianBallOf_scaleMetric (1 / 4 : ℝ) (by norm_num) h (Φ p) δ
  have hradius : Real.sqrt (1 / 4 : ℝ) * δ = δ / 2 := by norm_num; ring
  rw [hradius] at hscale
  rw [hscale, Integral.Measure.volume_scale_apply]
  have hmult := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ ENNReal.ofReal (Real.sqrt (1 / 4 : ℝ)) ^ Module.finrank ℝ E₃ from zero_le)
  have hcancel : ENNReal.ofReal (Real.sqrt (1 / 4 : ℝ)) ^ Module.finrank ℝ E₃ * (8 : ℝ≥0∞) = 1 := by
    calc
      _ = ENNReal.ofReal (Real.sqrt (1 / 4 : ℝ) ^ Module.finrank ℝ E₃ * 8) := by
        rw [ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg _) _),
          ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
        norm_num only [ENNReal.ofReal_ofNat]
      _ = 1 := by norm_num
  simpa only [← mul_assoc, hcancel, one_mul] using hmult

theorem exists_deck_displacement_lt_of_small_volume_metric_bounds
    [ConnectedSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (hh : RiemannianMetricComplete h) (x₀ : N)
    (hcurv : ∀ (q : N) (v w : TangentSpace J q),
      Curvature.metricRm04StandardAt h q v w w v =
        (-1 / 4 : ℝ) * (h.inner q v v * h.inner q w w - h.inner q v w * h.inner q v w))
    (p : M) {δ : ℝ} (hδ : 0 < δ) (Φ : PartialDiffeomorph I J M N ∞)
    (hcompact : IsCompact (riemannianClosedBallOf g p (4 * δ)))
    (hsub : riemannianClosedBallOf g p (4 * δ) ⊆ Φ.source)
    (hlower : ∀ y ∈ riemannianClosedBallOf g p (4 * δ), ∀ v : TangentSpace I y,
      (1 / 4 : ℝ) * g.inner y v v ≤ h.inner (Φ y) (mfderiv I J Φ y v) (mfderiv I J Φ y v))
    (hupper : ∀ y ∈ riemannianClosedBallOf g p (4 * δ), ∀ v : TangentSpace I y,
      h.inner (Φ y) (mfderiv I J Φ y v) (mfderiv I J Φ y v) ≤ 4 * g.inner y v v)
    (hsmall : riemannianVolumeMeasure I M g (riemannianClosedBallOf g p (4 * δ)) <
      riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃) Hyperboloid.riemannianMetric
        (Metric.ball Hyperboloid.origin (δ / 2))) :
    letI : Inhabited N := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H' := J.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H' N
    letI : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := J)
    ∀ x : UniversalCover N, UniversalCover.proj x = Φ p →
      ∃ γ : FundamentalGroup N (default : N), γ ≠ 1 ∧
        riemannianEDistOf (UniversalCover.liftedMetric (I := J)
          (scaleMetric (1 / 4) (by norm_num) h)) x (γ • x) < ENNReal.ofReal δ := by
  let _ : Inhabited N := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H' := J.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H' N
  let _ : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := J)
  dsimp only
  intro x hx
  by_contra hnot
  have hlong : ∀ γ : FundamentalGroup N (default : N), γ ≠ 1 →
      ENNReal.ofReal δ ≤ riemannianEDistOf (UniversalCover.liftedMetric (I := J)
        (scaleMetric (1 / 4) (by norm_num) h)) x (γ • x) := by
    intro γ hγ
    exact le_of_not_gt (fun hd => hnot ⟨γ, hγ, hd⟩)
  have hthick := riemannianVolumeMeasure_normalized_ball_eq_of_le_deck_displacement
    h hh (-1 / 4) (by norm_num) x₀ hcurv x (δ / 2)
  dsimp only at hthick
  simp only [neg_div, neg_neg] at hthick
  have htwice : 2 * (δ / 2) = δ := by ring
  rw [htwice] at hthick
  have hmodel := hthick hlong
  have hmass := normalized_ball_volume_le_source_closed_ball g h p hδ Φ hcompact hsub hlower hupper
  rw [hx] at hmodel
  exact (not_lt_of_ge (hmodel.symm.trans_le hmass)) hsmall

theorem exists_deck_displacement_lt_of_small_volume_metric_approximation
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (hh : RiemannianMetricComplete h) (x₀ : N)
    (hcurv : ∀ (q : N) (v w : TangentSpace I q),
      Curvature.metricRm04StandardAt h q v w w v =
        (-1 / 4 : ℝ) * (h.inner q v v * h.inner q w w - h.inner q v w * h.inner q v w))
    (p : M) {δ : ℝ} (hδ : 0 < δ) (Φ : PartialDiffeomorph I I M N ∞)
    (hcompact : IsCompact (riemannianClosedBallOf g p (4 * δ)))
    (k : ℕ) {ε : ℝ} (hε : ε ≤ 1 / 2)
    (happrox : DifferentialGeometry.PartialDiffeomorph.isMetricApproximationOn Φ
      (riemannianClosedBallOf g p (4 * δ)) k ε g h)
    (hsmall : riemannianVolumeMeasure I M g (riemannianClosedBallOf g p (4 * δ)) <
      riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃) Hyperboloid.riemannianMetric
        (Metric.ball Hyperboloid.origin (δ / 2))) :
    letI : Inhabited N := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
    letI : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
    ∀ x : UniversalCover N, UniversalCover.proj x = Φ p →
      ∃ γ : FundamentalGroup N (default : N), γ ≠ 1 ∧
        riemannianEDistOf (UniversalCover.liftedMetric (I := I)
          (scaleMetric (1 / 4) (by norm_num) h)) x (γ • x) < ENNReal.ofReal δ := by
  apply exists_deck_displacement_lt_of_small_volume_metric_bounds
    g h hh x₀ hcurv p hδ Φ hcompact happrox.1 ?_ ?_ hsmall
  · intro y hy v
    have hb := happrox.quadratic_bounds hy v
    have hcoef : (1 / 4 : ℝ) ≤ 1 - ε := by linarith
    exact (mul_le_mul_of_nonneg_right hcoef (metric_inner_self_nonneg g y v)).trans hb.1
  · intro y hy v
    have hb := happrox.quadratic_bounds hy v
    have hcoef : 1 + ε ≤ (4 : ℝ) := by linarith
    exact hb.2.trans (mul_le_mul_of_nonneg_right hcoef (metric_inner_self_nonneg g y v))

end DifferentialGeometry.Geometry.Hyperbolic
