import DifferentialGeometry.Geometry.Metric.Convergence.Metric.QuadraticBounds
import DifferentialGeometry.Geometry.Comparison.MetricDistanceTransfer
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {E F H H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
  [∀ n, IsManifold I ∞ (M n)] [∀ n, T2Space (M n)]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem MetricCPConvergenceOn.eventually_closedBall_subset_image_of_pullback
    {gSeq : ℕ → SmoothRiemannianMetric J N} {gInf gRef : SmoothRiemannianMetric J N}
    (hSeq : ∀ n, SmoothRiemannianMetric I (M n))
    (Phi : ∀ n, PartialDiffeomorph J I N (M n) ∞) (p : N) {R r : ℝ}
    (hR : 0 < R) (hr : r < R)
    (hcompact : IsCompact (riemannianClosedBallOf gInf p R))
    (hconv : MetricCPConvergenceOn (riemannianClosedBallOf gInf p R) 0 gSeq gInf gRef)
    (hsource : ∀ᶠ n in atTop, riemannianClosedBallOf gInf p R ⊆ (Phi n).source)
    (hmetric : ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf gInf p R,
      ∀ v : TangentSpace J x, (gSeq n).inner x v v = (hSeq n).inner (Phi n x)
        (mfderiv J I (Phi n) x v) (mfderiv J I (Phi n) x v)) :
    ∀ᶠ n in atTop, riemannianClosedBallOf (hSeq n) (Phi n p) r ⊆
      (Phi n) '' riemannianClosedBallOf gInf p R := by
  let eta := min ((R - r) / (2 * R)) (1 / 4)
  have heta : 0 < eta := lt_min (div_pos (sub_pos.mpr hr) (by positivity)) (by norm_num)
  have heta4 : eta ≤ 1 / 4 := min_le_right _ _
  have hetaR : eta * (2 * R) ≤ R - r :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hminus : 1 - eta ≤ Real.sqrt (1 - eta) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [heta.le, heta4]
  have hpos : 0 < 1 - eta := by linarith
  have hsqrt : 0 < Real.sqrt (1 - eta) := Real.sqrt_pos.mpr hpos
  filter_upwards [hsource, hconv.eventually_quadratic_bounds hcompact heta, hmetric]
    with n hn hbound hm
  refine DifferentialGeometry.PartialDiffeomorph.closedBall_subset_image_closedBall_of_metric_lower
    gInf (hSeq n) (Phi n) p hR (inv_pos.mpr hsqrt) ?_ hcompact hn ?_
  · rw [div_inv_eq_mul]
    nlinarith only [hetaR, mul_le_mul_of_nonneg_right hminus hR.le, heta, hR]
  intro x hx v
  rw [inv_pow, Real.sq_sqrt hpos.le]
  have hb := (hbound x hx v).1
  rw [hm x hx v] at hb
  calc
    gInf.inner x v v = (1 - eta)⁻¹ * ((1 - eta) * gInf.inner x v v) := by
      rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hpos).le

theorem MetricCPConvergenceOn.eventually_uniform_edist_toReal_of_pullback
    {gSeq : ℕ → SmoothRiemannianMetric J N} {gInf gRef : SmoothRiemannianMetric J N}
    (hSeq : ∀ n, SmoothRiemannianMetric I (M n))
    (Phi : ∀ n, PartialDiffeomorph J I N (M n) ∞) (p : N) {R rho : ℝ}
    (hrho : 0 ≤ rho) (hroom : 3 * rho < R)
    (hcompact : IsCompact (riemannianClosedBallOf gInf p R))
    (hconv : MetricCPConvergenceOn (riemannianClosedBallOf gInf p R) 0 gSeq gInf gRef)
    (hsource : ∀ᶠ n in atTop, riemannianClosedBallOf gInf p R ⊆ (Phi n).source)
    (hmetric : ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf gInf p R,
      ∀ v : TangentSpace J x, (gSeq n).inner x v v = (hSeq n).inner (Phi n x)
        (mfderiv J I (Phi n) x v) (mfderiv J I (Phi n) x v))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf gInf p rho,
      ∀ y ∈ riemannianClosedBallOf gInf p rho,
        |(riemannianEDistOf (hSeq n) (Phi n x) (Phi n y)).toReal -
          (riemannianEDistOf gInf x y).toReal| < epsilon := by
  have hR : 0 < R := lt_of_le_of_lt (by positivity) hroom
  let eta := min (epsilon / (4 * rho + 1))
    (min ((R - 3 * rho) / (2 * (R + 3 * rho))) (1 / 4))
  have heta : 0 < eta := lt_min (div_pos hepsilon (by positivity))
    (lt_min (div_pos (sub_pos.mpr hroom) (by positivity)) (by norm_num))
  have heta4 : eta ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hetaE : eta * (4 * rho + 1) ≤ epsilon :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hetaR : eta * (2 * (R + 3 * rho)) ≤ R - 3 * rho :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hplus : Real.sqrt (1 + eta) ≤ 1 + eta :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hminus : 1 - eta ≤ Real.sqrt (1 - eta) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [heta.le, heta4]
  have hroom' : Real.sqrt (1 + eta) * (3 * rho) < Real.sqrt (1 - eta) * R := by
    have hu := mul_le_mul_of_nonneg_right hplus (show 0 ≤ 3 * rho by positivity)
    have hl := mul_le_mul_of_nonneg_right hminus hR.le
    nlinarith only [hu, hl, hetaR, hroom]
  filter_upwards [hsource, hconv.eventually_quadratic_bounds hcompact heta, hmetric]
    with n hn hbound hm
  have hb : ∀ x ∈ riemannianClosedBallOf gInf p R, ∀ v : TangentSpace J x,
      (1 - eta) * gInf.inner x v v ≤ (hSeq n).inner (Phi n x)
        (mfderiv J I (Phi n) x v) (mfderiv J I (Phi n) x v) ∧
      (hSeq n).inner (Phi n x) (mfderiv J I (Phi n) x v) (mfderiv J I (Phi n) x v) ≤
        (1 + eta) * gInf.inner x v v := by
    intro x hx v
    rw [← hm x hx v]
    exact hbound x hx v
  have hd := crossModel_toReal_transfer gInf (hSeq n) (Phi n) p hR heta.le
    (by linarith) hrho hcompact hn hb hroom'
  intro x hx y hy
  have hpairs := hd x hx y hy
  have hnonneg := ENNReal.toReal_nonneg (a := riemannianEDistOf gInf x y)
  have hdiam : (riemannianEDistOf gInf x y).toReal ≤ 2 * rho := by
    have hdist : riemannianEDistOf gInf x y ≤ ENNReal.ofReal (2 * rho) := by
      calc
        _ ≤ riemannianEDistOf gInf x p + riemannianEDistOf gInf p y :=
          riemannianEDistOf_triangle gInf x p y
        _ ≤ ENNReal.ofReal rho + ENNReal.ofReal rho := by
          rw [riemannianEDistOf_comm gInf x p]
          exact add_le_add hx hy
        _ = ENNReal.ofReal (2 * rho) := by rw [← ENNReal.ofReal_add hrho hrho]; congr 1; ring
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ 2 * rho by positivity)] using hh
  have hl := (mul_le_mul_of_nonneg_right hminus hnonneg).trans hpairs.1
  have hu := hpairs.2.trans (mul_le_mul_of_nonneg_right hplus hnonneg)
  have herr : eta * (riemannianEDistOf gInf x y).toReal < epsilon := by
    nlinarith only [mul_le_mul_of_nonneg_left hdiam heta.le, hetaE, heta, hrho]
  exact abs_lt.mpr ⟨by nlinarith only [hl, herr], by nlinarith only [hu, herr]⟩

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E E' H H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : ℕ → Type*} [∀ n, TopologicalSpace (N n)] [∀ n, ChartedSpace H' (N n)]
  [∀ n, IsManifold J ∞ (N n)]

theorem tendsto_riemannianEDistOf_map_zero_of_metricCPConvergenceOn
    (gInf gRef : SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (h : ∀ n, SmoothRiemannianMetric J (N n))
    (F : ∀ n, PartialDiffeomorph I J M (N n) ∞)
    (p : M) {R : ℝ} (hR : 0 < R)
    (hK : IsCompact (riemannianClosedBallOf gInf p R))
    (hconv : MetricCPConvergenceOn (riemannianClosedBallOf gInf p R) 0 gSeq gInf gRef)
    (hsource : ∀ᶠ n in atTop, riemannianClosedBallOf gInf p R ⊆ (F n).source)
    (hmetric : ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf gInf p R,
      ∀ v : TangentSpace I x,
        (gSeq n).inner x v v =
          (h n).inner (F n x) (mfderiv I J (F n) x v) (mfderiv I J (F n) x v))
    {z : ℕ → M} (hz : Tendsto z atTop (𝓝 p)) :
    Tendsto (fun n => riemannianEDistOf (h n) (F n p) (F n (z n))) atTop (𝓝 0) := by
  have hdist : Tendsto (fun n => riemannianEDistOf gInf p (z n)) atTop (𝓝 0) := by
    have hd := (Geometry.Riemannian.continuous_riemannianEDist gInf p).continuousAt.tendsto.comp hz
    change Tendsto (fun n => riemannianEDistOf gInf p (z n)) atTop
      (𝓝 (riemannianEDistOf gInf p p)) at hd
    simpa only [riemannianEDistOf_self] using hd
  have hsmall : ∀ᶠ n in atTop, riemannianEDistOf gInf p (z n) < ENNReal.ofReal R :=
    hdist.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hR))
  have hbound : ∀ᶠ n in atTop,
      riemannianEDistOf (h n) (F n p) (F n (z n)) ≤
        ENNReal.ofReal 2 * riemannianEDistOf gInf p (z n) := by
    filter_upwards [hconv.eventually_quadratic_bounds hK (by norm_num : (0 : ℝ) < 3),
      hsource, hmetric, hsmall] with n hn hs hm hz'
    apply PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      gInf (h n) (F n) p (z n) hR (by norm_num) hs _ hz'
    intro x hx v
    rw [← hm x hx v]
    convert (hn x hx v).2 using 1
    norm_num
  have hlim : Tendsto (fun n => ENNReal.ofReal 2 * riemannianEDistOf gInf p (z n))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hdist
      (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) hbound

end DifferentialGeometry.CheegerGromovCompactness
