import DifferentialGeometry.Geometry.Measure.HyperbolicCoveringCollapse
import DifferentialGeometry.Geometry.Measure.PartialDiffeomorphComparison
import DifferentialGeometry.Geometry.Metric.Comparison.BallImage
import DifferentialGeometry.Geometry.Metric.Approximation.QuadraticBounds
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

noncomputable section

open scoped Manifold ContDiff ENNReal Bundle
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] in
private theorem image_unit_ball_subset
    {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E₃ H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (o : M) (Φ : PartialDiffeomorph I J M N ∞)
    (hsub : riemannianClosedBallOf g o 1 ⊆ Φ.source)
    (hquad : ∀ x ∈ riemannianClosedBallOf g o 1, ∀ v : TangentSpace I x,
      h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v) ≤ 4 * g.inner x v v) :
    Φ '' riemannianBallOf g o 1 ⊆ riemannianBallOf h (Φ o) 2 := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : IsManifold J 1 N := IsManifold.of_le (I := J) (M := N) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
  let _ : T3Space N := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : PseudoEMetricSpace M := .ofRiemannianMetric I M
  let _ : Bundle.RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : PseudoEMetricSpace N := .ofRiemannianMetric J N
  have hgnorm (x : M) (v : TangentSpace I x) :
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hhnorm (y : N) (v : TangentSpace J y) :
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner y v v)) := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hclosed : Metric.closedEBall o (ENNReal.ofReal 1) = riemannianClosedBallOf g o 1 := by
    ext x
    change edist x o ≤ ENNReal.ofReal 1 ↔ edist o x ≤ ENNReal.ofReal 1
    rw [edist_comm]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨r, hr0, hxr, hr1⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx
  have hr : r < 1 := (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mp hr1
  have hxr' : x ∈ Metric.eball o (ENNReal.ofReal r) := by
    change edist x o < ENNReal.ofReal r
    rw [edist_comm]
    exact hxr
  have himage := DifferentialGeometry.PartialDiffeomorph.image_eball_subset_closedEBall_of_quad_le
    Φ (by simp) hgnorm hhnorm hr.le (by norm_num : (0 : ℝ) ≤ 4)
    (by rwa [hclosed]) (by simpa only [hclosed] using hquad) ⟨x, hxr', rfl⟩
  rw [Metric.mem_closedEBall, edist_comm] at himage
  change edist (Φ o) (Φ x) < ENNReal.ofReal 2
  apply himage.trans_lt
  apply ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr
  norm_num
  linarith

private theorem source_volume_le_normalized_target_ball
    {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E₃ H'} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (o : M) (Φ : PartialDiffeomorph I J M N ∞)
    (hsub : riemannianClosedBallOf g o 1 ⊆ Φ.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf g o 1, ∀ v : TangentSpace I x,
      (1 / 4 : ℝ) * g.inner x v v ≤ h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v))
    (hupper : ∀ x ∈ riemannianClosedBallOf g o 1, ∀ v : TangentSpace I x,
      h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v) ≤ 4 * g.inner x v v) :
    riemannianVolumeMeasure I M g (riemannianBallOf g o 1) ≤
      64 * riemannianVolumeMeasure J N (scaleMetric (1 / 4) (by norm_num) h)
        (riemannianBallOf (scaleMetric (1 / 4) (by norm_num) h) (Φ o) 1) := by
  let _ : MeasurableSpace N := borel N
  let _ : BorelSpace N := ⟨rfl⟩
  have hball : riemannianBallOf g o 1 ⊆ riemannianClosedBallOf g o 1 := fun x hx => (show riemannianEDistOf g o x < ENNReal.ofReal 1 from hx).le
  have hm := Geometry.Measure.riemannianVolumeMeasure_le_image_of_partialDiffeomorph_metric_le
    g h Φ (isOpen_lt (Riemannian.continuous_riemannianEDist g o) continuous_const).measurableSet
    (hball.trans hsub) (by norm_num : (0 : ℝ) < 4)
    (fun x hx v => by have hh := hlower x (hball hx) v; linarith)
  have hmass := hm.trans (mul_le_mul_of_nonneg_left
    (MeasureTheory.measure_mono (image_unit_ball_subset g h o Φ hsub hupper)) (show 0 ≤ _ from zero_le))
  have he := riemannianBallOf_scaleMetric (1 / 4 : ℝ) (by norm_num) h (Φ o) 2
  norm_num at he
  have hf : ENNReal.ofReal (Real.sqrt ((4 : ℝ) ^ Module.finrank ℝ E₃)) = 8 := by norm_num
  rw [hf] at hmass
  rw [he, Integral.Measure.volume_scale_apply, ← mul_assoc]
  have hf' : (64 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (1 / 4 : ℝ)) ^ Module.finrank ℝ E₃ = 8 := by
    calc
      _ = ENNReal.ofReal (64 * Real.sqrt (1 / 4 : ℝ) ^ Module.finrank ℝ E₃) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64), ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
        norm_num only [ENNReal.ofReal_ofNat]
      _ = 8 := by norm_num
  rw [hf']
  exact hmass

universe v w

theorem exists_pos_deck_displacement_of_partialDiffeomorph_metric_bounds
    (g : SmoothRiemannianMetric I M) (o : M) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : Type v) (H' : Type w) [TopologicalSpace H']
        (J : ModelWithCorners ℝ E₃ H') [J.Boundaryless]
        [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
        [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
        (h : SmoothRiemannianMetric J N) (_ : RiemannianMetricComplete h)
        (Φ : PartialDiffeomorph I J M N ∞),
        (∀ (q : N) (v w : TangentSpace J q),
          Curvature.metricRm04StandardAt h q v w w v =
            (-1 / 4 : ℝ) * (h.inner q v v * h.inner q w w - h.inner q v w * h.inner q v w)) →
        riemannianClosedBallOf g o 1 ⊆ Φ.source →
        (∀ x ∈ riemannianClosedBallOf g o 1, ∀ v : TangentSpace I x,
          (1 / 4 : ℝ) * g.inner x v v ≤ h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v)) →
        (∀ x ∈ riemannianClosedBallOf g o 1, ∀ v : TangentSpace I x,
          h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v) ≤ 4 * g.inner x v v) →
        letI : Inhabited N := ⟨Φ o⟩
        letI : LocallyPathConnectedSpace H' := J.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
        letI : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H' N
        letI : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := J)
        ∀ x : UniversalCover N, UniversalCover.proj x = Φ o →
        ∀ γ : FundamentalGroup N (default : N), γ ≠ 1 →
          ENNReal.ofReal δ < riemannianEDistOf
            (UniversalCover.liftedMetric (I := J) (scaleMetric (1 / 4) (by norm_num) h)) x (γ • x) := by
  let _ := Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure g
  have hpos : 0 < riemannianVolumeMeasure I M g (riemannianBallOf g o 1) := by
    apply (isOpen_lt (Riemannian.continuous_riemannianEDist g o) continuous_const).measure_pos (μ := riemannianVolumeMeasure I M g)
    refine ⟨o, ?_⟩
    change riemannianEDistOf g o o < ENNReal.ofReal 1
    simp [riemannianEDistOf_self]
  obtain ⟨a, ha0, ha, hamass⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  have hapos : 0 < a := ENNReal.ofReal_pos.mp ha
  let μH := riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃) Hyperboloid.riemannianMetric
  let V := μH (Metric.ball Hyperboloid.origin 2)
  let _ : MeasurableSpace (Hyperboloid E₃) := borel (Hyperboloid E₃)
  let _ : BorelSpace (Hyperboloid E₃) := ⟨rfl⟩
  let _ := Integral.Measure.riemannianVolumeMeasure_isFiniteMeasureOnCompacts
    (Hyperboloid.riemannianMetric (E := E₃))
  have hV : V ≠ ⊤ := MeasureTheory.measure_ball_ne_top
  obtain ⟨k, hk, hklarge⟩ := ENNReal.exists_nat_pos_mul_gt
    (a := ENNReal.ofReal (a / 64)) (b := V) (by positivity) hV
  refine ⟨1 / k, by positivity, ?_⟩
  intro N H' topH' J bJ topN chartN smoothN t2N sigmaN connN h hh Φ hcurv hsub hlower hupper
  let _ : Inhabited N := ⟨Φ o⟩
  let _ : LocallyPathConnectedSpace H' := J.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H' N
  let _ : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := J)
  dsimp only
  intro x hx γ hγ
  let hN := scaleMetric (1 / 4 : ℝ) (by norm_num) h
  have hmass := source_volume_le_normalized_target_ball g h o Φ hsub hlower hupper
  have hlow : ENNReal.ofReal (a / 64) ≤
      riemannianVolumeMeasure J N hN (riemannianBallOf hN (Φ o) 1) := by
    have hle := hamass.le.trans hmass
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 64)]
    exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by simpa only [hN, ENNReal.ofReal_ofNat, mul_comm] using hle)
  by_contra hnot
  have hshort := le_of_not_gt hnot
  have hbound := nat_mul_volume_normalized_ball_le_of_short_deck_displacement
    h hh (-1 / 4) (by norm_num) (Φ o) hcurv γ hγ x 1 (1 / k)
      zero_lt_one (by positivity)
  dsimp only at hbound
  simp only [neg_div, neg_neg] at hbound
  have hbound' := hbound hshort k
  have hradius : (1 : ℝ) + ((k - 1 : ℕ) : ℝ) * (1 / k) ≤ 2 := by
    have hle : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have hmul := mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ 1 / k)
    have hkeq : (k : ℝ) * (1 / k) = 1 := by field_simp
    rw [hkeq] at hmul
    linarith
  have hfinal : (k : ℝ≥0∞) * riemannianVolumeMeasure J N hN
      (riemannianBallOf hN (Φ o) 1) ≤ V := by
    have hb := hbound'.trans (MeasureTheory.measure_mono (Metric.ball_subset_ball hradius))
    simpa only [neg_div, neg_neg, hx] using hb
  exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left hlow (show 0 ≤ (k : ℝ≥0∞) from zero_le)).trans hfinal)) hklarge

theorem exists_pos_deck_displacement_of_metric_approximation
    (g : SmoothRiemannianMetric I M) (o : M) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : Type v) [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
        [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
        (h : SmoothRiemannianMetric I N) (_ : RiemannianMetricComplete h)
        (Φ : PartialDiffeomorph I I M N ∞),
        (∀ (q : N) (v w : TangentSpace I q),
          Curvature.metricRm04StandardAt h q v w w v =
            (-1 / 4 : ℝ) * (h.inner q v v * h.inner q w w - h.inner q v w * h.inner q v w)) →
        ∀ (p : ℕ) (ε : ℝ), ε ≤ 3 / 4 →
        DifferentialGeometry.PartialDiffeomorph.isMetricApproximationOn Φ
          (riemannianClosedBallOf g o 1) p ε g h →
        letI : Inhabited N := ⟨Φ o⟩
        letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
        letI : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
        letI : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
        ∀ x : UniversalCover N, UniversalCover.proj x = Φ o →
        ∀ γ : FundamentalGroup N (default : N), γ ≠ 1 →
          ENNReal.ofReal δ < riemannianEDistOf
            (UniversalCover.liftedMetric (I := I) (scaleMetric (1 / 4) (by norm_num) h)) x (γ • x) := by
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_deck_displacement_of_partialDiffeomorph_metric_bounds
    g o
  refine ⟨δ, hδ, ?_⟩
  intro N topN chartN smoothN t2N sigmaN connN h hh Φ hcurv p ε hε happrox
  apply hbound N H I h hh Φ hcurv happrox.1
  · intro x hx v
    have hbounds := happrox.quadratic_bounds hx v
    have hnn := metric_inner_self_nonneg g x v
    have hcoef : (1 / 4 : ℝ) ≤ 1 - ε := by linarith
    exact (mul_le_mul_of_nonneg_right hcoef hnn).trans hbounds.1
  · intro x hx v
    have hbounds := happrox.quadratic_bounds hx v
    have hnn := metric_inner_self_nonneg g x v
    have hcoef : 1 + ε ≤ (4 : ℝ) := by linarith
    exact hbounds.2.trans (mul_le_mul_of_nonneg_right hcoef hnn)

end DifferentialGeometry.Geometry.Hyperbolic
