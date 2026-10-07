import DifferentialGeometry.Geometry.Curvature.Bounds.PullbackSectionalPinching
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.RawRestriction
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphBalls
import DifferentialGeometry.Geometry.Metric.Pullback.MetricBounds

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open Curvature Riemannian DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection

universe uE uH uM uF uH' uN

theorem exists_pos_curvatureRadius_close_of_pullback_metricDerivNorm_le
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ δ > 0,
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] (H : Type uH) [TopologicalSpace H]
        (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M]
        (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F] (H' : Type uH') [TopologicalSpace H']
        (J : ModelWithCorners ℝ F H') [J.Boundaryless]
        (N : Type uN) [TopologicalSpace N] [ChartedSpace H' N]
        [IsManifold J ∞ N] [T2Space N]
        (Φ : PartialDiffeomorph I J M N ∞) (U : TopologicalSpace.Opens M)
        (hU : (U : Set M) ⊆ Φ.source)
        (G : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
        (K : Set U) (p : U),
        let hΦ := isLocalDiffeomorph_restrict_open (I := I) (J := J) U
          (fun y => Φ.isLocalDiffeomorphAt I J ∞ (hU y.property))
        2 ≤ Module.finrank ℝ E →
        riemannianBallOf h (Φ p) (1 / Real.sqrt κ) ⊆ (fun x : U => Φ x) '' K →
        (∀ x ∈ K, ∀ k : ℕ, k ≤ 2 →
          metricDerivNorm k (localPullMetric h (fun y : U => Φ y) hΦ)
            (G.restrictOpen U) (G.restrictOpen U) x ≤ δ) →
        (∀ x ∈ K, ∀ v w : TangentSpace I x, LinearIndependent ℝ ![v, w] →
          sectionalCurvature G (x : M) v w = -κ) →
        curvatureRadius h (Φ p) ≠ ⊤ ∧
          |(curvatureRadius h (Φ p)).toReal - 1 / Real.sqrt κ| < ε := by
  obtain ⟨η, hη, _, hρ⟩ := exists_sectional_tolerance_curvatureRadius_close hκ hε
  obtain ⟨δ, hδ, hpinch⟩ :=
    exists_pos_sectional_pinching_of_pullback_metricDerivNorm_le hκ hη
  refine ⟨δ, hδ, ?_⟩
  intro E _ _ _ H _ I _ M _ _ _ _ F _ _ _ H' _ J _ N _ _ _ _ Φ U hU G h K p
    hΦ hdim hcapture hsmall hsec
  have hall (y : N) (hy : y ∈ riemannianBallOf h (Φ p) (1 / Real.sqrt κ)) :
      SectionalBoundedBelowAt h y (-(κ + η)) ∧
        ∀ v w : TangentSpace J y, LinearIndependent ℝ ![v, w] →
          sectionalCurvature h y v w ≤ -(κ - η) := by
    obtain ⟨x, hx, rfl⟩ := hcapture hy
    exact hpinch E H I M F H' J N Φ U hU G h x (hsmall x hx) (hsec x hx)
  apply hρ F H' J N h (Φ p) (fun y hy => (hall y hy).1)
  have hp : Φ p ∈ riemannianBallOf h (Φ p) (1 / Real.sqrt κ) := by
    change riemannianEDistOf h (Φ p) (Φ p) < ENNReal.ofReal (1 / Real.sqrt κ)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (one_div_pos.mpr (Real.sqrt_pos.mpr hκ))
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank
    (show 2 ≤ Module.finrank ℝ (TangentSpace I p) from hdim)
  let D := hΦ.mfderivToContinuousLinearEquiv (by simp) p
  have hpair : LinearIndependent ℝ ![D (b 0), D (b 1)] := by
    have hm := hb.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr D.injective)
    convert hm using 1
    ext i
    fin_cases i <;> rfl
  exact ⟨D (b 0), D (b 1), hpair, (hall (Φ p) hp).2 _ _ hpair⟩

theorem exists_pos_curvatureRadius_close_of_raw_pullback_derivatives
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ δ > 0,
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] (H : Type uH) [TopologicalSpace H]
        (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M]
        (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F] (H' : Type uH') [TopologicalSpace H']
        (J : ModelWithCorners ℝ F H') [J.Boundaryless]
        (N : Type uN) [TopologicalSpace N] [ChartedSpace H' N]
        [IsManifold J ∞ N] [T2Space N]
        (Φ : PartialDiffeomorph I J M N ∞)
        (G : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
        (c : ℝ) (hc : 0 < c) (p : M),
        2 ≤ Module.finrank ℝ E →
        IsCompact (riemannianClosedBallOf G p (2 / Real.sqrt κ)) →
        riemannianClosedBallOf G p (2 / Real.sqrt κ) ⊆ Φ.source →
        (∀ x ∈ riemannianClosedBallOf G p (2 / Real.sqrt κ), ∀ k : ℕ, k ≤ 2 →
          tensor0SFiberNorm G x (2 + k)
            (iteratedMetricCovariantDerivative G 2
              (fun y : M =>
                ((continuousMultilinearCurryFin1 ℝ (TangentSpace I y) ℝ).symm.toContinuousLinearMap.comp
                  (c • localPullInner h (Φ : M → N) y - G.inner y)).uncurryLeft) k x) ≤ δ) →
        (∀ x ∈ riemannianClosedBallOf G p (2 / Real.sqrt κ),
          ∀ v w : TangentSpace I x, LinearIndependent ℝ ![v, w] →
            sectionalCurvature G x v w = -κ) →
        curvatureRadius (scaleMetric c hc h) (Φ p) ≠ ⊤ ∧
          |(curvatureRadius (scaleMetric c hc h) (Φ p)).toReal - 1 / Real.sqrt κ| < ε := by
  obtain ⟨δρ, hδρ, hρ⟩ := exists_pos_curvatureRadius_close_of_pullback_metricDerivNorm_le hκ hε
  refine ⟨min δρ (1 / 2), lt_min hδρ (by norm_num), ?_⟩
  intro E _ _ _ H _ I _ M _ _ _ _ F _ _ _ H' _ J _ N _ _ _ _ Φ G h c hc p
    hdim hcpt hsource hsmall hsec
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let U : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  have hU : (U : Set M) ⊆ Φ.source := fun _ hx => hx
  have hκroot : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hR : 0 < 1 / Real.sqrt κ := one_div_pos.mpr hκroot
  have hbuffer : (3 / 2 : ℝ) * (1 / Real.sqrt κ) < 2 / Real.sqrt κ := by
    have heq : 2 / Real.sqrt κ = 2 * (1 / Real.sqrt κ) := by ring
    rw [heq]
    nlinarith
  have hpball : p ∈ riemannianClosedBallOf G p (2 / Real.sqrt κ) := by
    change riemannianEDistOf G p p ≤ ENNReal.ofReal (2 / Real.sqrt κ)
    rw [riemannianEDistOf_self]
    exact bot_le
  let pU : U := ⟨p, hsource hpball⟩
  let K : Set U := {x | (x : M) ∈ riemannianClosedBallOf G p (2 / Real.sqrt κ)}
  let hΦ := isLocalDiffeomorph_restrict_open (I := I) (J := J) U
    (fun y => Φ.isLocalDiffeomorphAt I J ∞ (hU y.property))
  have hzero (x : M) (hx : x ∈ riemannianClosedBallOf G p (2 / Real.sqrt κ)) :
      tensor0SFiberNorm G x 2
        (((continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ).symm.toContinuousLinearMap.comp
          (c • localPullInner h (Φ : M → N) x - G.inner x)).uncurryLeft) ≤ 1 / 2 :=
    (hsmall x hx 0 (by omega)).trans (min_le_right _ _)
  have hcapture0 := PartialDiffeomorph.riemannianBall_subset_image_of_metric_lower G
    (scaleMetric c hc h) Φ p (by norm_num : (0 : ℝ) < 3 / 2) hbuffer hcpt hsource
    (fun x hx v => by
      have hb := (scaled_pullback_inner_bounds_of_tensor0SFiberNorm_le G h
        (Φ : M → N) c hc x (hzero x hx) v).1
      have hg := metric_inner_self_nonneg G x v
      have hh := metric_inner_self_nonneg (scaleMetric c hc h) (Φ x)
        (mfderiv I J (Φ : M → N) x v)
      nlinarith)
  have hcapture : riemannianBallOf (scaleMetric c hc h) (Φ pU) (1 / Real.sqrt κ) ⊆
      (fun x : U => Φ x) '' K := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hcapture0 hy
    have hxball : x ∈ riemannianClosedBallOf G p (2 / Real.sqrt κ) :=
      hx.le.trans (ENNReal.ofReal_le_ofReal hbuffer.le)
    exact ⟨⟨x, hsource hxball⟩, hxball, hxy⟩
  apply hρ E H I M F H' J N Φ U hU G (scaleMetric c hc h) K pU hdim hcapture
  · intro x hx k hk
    rw [metricDerivNorm_scaled_localPullMetric_eq_raw G h (Φ : M → N) U hΦ c hc k x]
    exact (hsmall x hx k hk).trans (min_le_left _ _)
  · intro x hx v w hvw
    exact hsec x hx v w hvw

end DifferentialGeometry.Geometry.Collapse
