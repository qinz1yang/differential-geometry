import DifferentialGeometry.Geometry.Hyperbolic.TruncationThinness
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusPullback

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

open Collapse Riemannian Connection DifferentialGeometry.Tensor0SBundle

private theorem quadratic_bounds_from_error {a b δ : ℝ} (hδ : 0 ≤ δ)
    (hδhalf : δ ≤ 1 / 2) (ha : 0 ≤ a)
    (hlo : (1 - δ) * a ≤ b) (hhi : b ≤ (1 + δ) * a) :
    a ≤ (1 + 2 * δ) ^ 2 * b ∧ b ≤ (1 + 2 * δ) ^ 2 * a := by
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hcoeff : 1 ≤ (1 + 2 * δ) ^ 2 * (1 - δ) := by
    nlinarith [mul_nonneg hδ (by linarith : (0 : ℝ) ≤ 3 - 4 * δ ^ 2)]
  have hstep := mul_le_mul_of_nonneg_left hlo (sq_nonneg (1 + 2 * δ))
  have hlow := mul_le_mul_of_nonneg_right hcoeff ha
  have hupp := mul_le_mul_of_nonneg_right
    (show 1 + δ ≤ (1 + 2 * δ) ^ 2 by nlinarith [sq_nonneg δ]) ha
  constructor <;> nlinarith

universe u v w z

theorem exists_volume_superlevel_preimage_subset_ball_of_raw_pullback_derivatives
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H) (o : H.Carrier) :
    ∃ η > 0, ∃ δ > 0, ∀ w : ℝ, 0 < w → w < η →
        ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
          [FiniteDimensional ℝ F] (H' : Type w) [TopologicalSpace H']
          (J : ModelWithCorners ℝ F H') [J.Boundaryless]
          (N : Type z) [TopologicalSpace N] [ChartedSpace H' N]
          [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
          (h : SmoothRiemannianMetric J N)
          (Φ : PartialDiffeomorph (𝓡 3) J H.Carrier N ∞)
          (p : H.Carrier), ∀ (c : ℝ) (hc : 0 < c),
          riemannianClosedBallOf H.metric p 4 ⊆ Φ.source →
          (∀ x ∈ riemannianClosedBallOf H.metric p 4, ∀ k : ℕ, k ≤ 2 →
            tensor0SFiberNorm H.metric x (2 + k)
              (iteratedMetricCovariantDerivative H.metric 2
                (fun y : H.Carrier =>
                  ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) y) ℝ).symm.toContinuousLinearMap.comp
                    (c • localPullInner h (Φ : H.Carrier → N) y - H.metric.inner y)).uncurryLeft)
                k x) ≤ δ) →
          ENNReal.ofReal (w * (curvatureRadius (scaleMetric c hc h) (Φ p)).toReal ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure J N (scaleMetric c hc h)
              (riemannianBallOf (scaleMetric c hc h) (Φ p)
                (curvatureRadius (scaleMetric c hc h) (Φ p)).toReal) →
          p ∈ riemannianBallOf H.metric o (1 / (2 * w)) := by
  obtain ⟨η, hη, δm, hδm, hvolume⟩ :=
    Tr.exists_metric_tolerance_volume_superlevel_preimage_subset_ball o
  let ε : ℝ := min δm (1 / 4)
  have hε : 0 < ε := lt_min hδm (by norm_num)
  have hεm : ε ≤ δm := min_le_left _ _
  have hεquarter : ε ≤ 1 / 4 := min_le_right _ _
  obtain ⟨δρ, hδρ, hradius⟩ :=
    exists_pos_curvatureRadius_close_of_raw_pullback_derivatives.{0, 0, u, v, w, z}
      (κ := (1 / 4 : ℝ)) (by norm_num) hε
  let δ : ℝ := min δρ (ε / 4)
  have hδ : 0 < δ := lt_min hδρ (by positivity)
  have hδρle : δ ≤ δρ := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  have hδhalf : δ ≤ 1 / 2 := by linarith
  refine ⟨η, hη, δ, hδ, ?_⟩
  intro w hw hwη F _ _ _ H' _ J _ N _ _ _ _ _ h Φ p c hc hsource hraw hmass
  let _ : IsManifold (𝓡 3) 1 H.Carrier :=
    IsManifold.of_le (I := 𝓡 3) (n := ∞) (by decide)
  have hcompact : IsCompact (riemannianClosedBallOf H.metric p 4) :=
    H.complete.closedEBall_isCompact p 4
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr
    norm_num
  have hfour : (2 : ℝ) / Real.sqrt (1 / 4 : ℝ) = 4 := by rw [hsqrt]; norm_num
  have htwo : (1 : ℝ) / Real.sqrt (1 / 4 : ℝ) = 2 := by rw [hsqrt]; norm_num
  have hclose := hradius (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))
    (𝓡 3) H.Carrier F H' J N Φ H.metric h c hc p (by simp)
    (by simpa only [hfour] using hcompact)
    (by simpa only [hfour] using hsource)
    (by
      intro x hx k hk
      have hx4 : x ∈ riemannianClosedBallOf H.metric p 4 := by
        simpa only [hfour] using hx
      exact (hraw x hx4 k hk).trans hδρle)
    (by
      intro x _ v w hvw
      exact H.curvature x v w hvw)
  let s : ℝ := (curvatureRadius (scaleMetric c hc h) (Φ p)).toReal
  have hs : |s - 2| < ε := by simpa only [htwo] using hclose.2
  have hsδm : |s - 2| < δm := hs.trans_le hεm
  have hspos : 0 < s := by
    have hh := (abs_lt.mp hs).1
    linarith
  have hsupper : s < 9 / 4 := by
    have hh := (abs_lt.mp hs).2
    linarith
  let a : ℝ := 1 + 2 * δ
  have haone : 1 ≤ a := by dsimp [a]; linarith
  have hapos : 0 < a := zero_lt_one.trans_le haone
  have haδm : |a - 1| < δm := by
    rw [abs_of_nonneg (sub_nonneg.mpr haone)]
    dsimp [a]
    linarith
  have haupper : a ≤ 3 / 2 := by dsimp [a]; linarith
  have hsmall : s / a < 4 := by
    apply (div_lt_iff₀ hapos).mpr
    nlinarith
  have hlarge : a * s < 4 := by
    have hb := mul_le_mul haupper hsupper.le hspos.le (by norm_num : (0 : ℝ) ≤ 3 / 2)
    nlinarith
  have hbounds (x : H.Carrier) (hx : x ∈ riemannianClosedBallOf H.metric p 4)
      (v : TangentSpace (𝓡 3) x) :
      H.metric.inner x v v ≤ a ^ 2 * (scaleMetric c hc h).inner (Φ x)
          (mfderiv (𝓡 3) J (Φ : H.Carrier → N) x v)
          (mfderiv (𝓡 3) J (Φ : H.Carrier → N) x v) ∧
        (scaleMetric c hc h).inner (Φ x)
          (mfderiv (𝓡 3) J (Φ : H.Carrier → N) x v)
          (mfderiv (𝓡 3) J (Φ : H.Carrier → N) x v) ≤ a ^ 2 * H.metric.inner x v v := by
    have hb := scaled_pullback_inner_bounds_of_tensor0SFiberNorm_le H.metric h
      (Φ : H.Carrier → N) c hc x (hraw x hx 0 (by omega)) v
    exact quadratic_bounds_from_error hδ.le hδhalf
      (metric_inner_self_nonneg H.metric x v) hb.1 hb.2
  exact hvolume w hw hwη F H' J N (scaleMetric c hc h) Φ p a a s 4 haδm haδm hsδm
    hsmall hlarge hsource (fun x hx v => (hbounds x hx v).1)
    (fun x hx v => (hbounds x hx v).2) hmass

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
