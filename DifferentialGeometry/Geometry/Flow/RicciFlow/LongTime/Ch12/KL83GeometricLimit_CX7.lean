import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83Noncollapse_CX7
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83StrainerVolume_CX7
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.LowDimensionalLimit
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.ModifiedScale
import DifferentialGeometry.Geometry.Comparison.UniformLiftedPacket

/-! # CH12-CX7: geometric bindings of noncollapse and sharp strainer volume -/

set_option autoImplicit false

noncomputable section

open Set Metric Filter MeasureTheory Bundle
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
  (modelVolume euclideanUnitBallVolume euclideanUnitBallVolume_pos)
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace GC.LongTime.Ch12

universe u v

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [NeZero (Module.finrank ℝ E)] in
/-- The Riemannian version of the finite-cover noncollapse argument. -/
theorem dimH_gt_two_of_riemannian_noncollapse_CX7 (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {p : ∀ i, X i} {Y : Type v} [MetricSpace Y] [ProperSpace Y] {q : Y}
    (hconv : PointedGHConverges p q) {v : ℝ} (hv : 0 < v)
    (hlower : ∀ᶠ i in atTop, ENNReal.ofReal v ≤ ballVolume (g i) (p i) 2)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ ball (p i) 5, SectionalBoundedBelowAt (g i) y (-1)) :
    2 < dimH (univ : Set Y) := by
  let : ∀ i, MeasurableSpace (X i) := fun i => borel (X i)
  let μ := fun i => Integral.Measure.riemannianVolumeMeasure I (X i) (g i)
  have hball (i : ℕ) (x : X i) (r : ℝ) : riemannianBallOf (g i) x r = ball x r := by
    ext y
    change riemannianEDistOf (g i) x y < ENNReal.ofReal r ↔ dist y x < r
    rw [hmetric, dist_comm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg
  have hvol (i : ℕ) (x : X i) (r : ℝ) : μ i (ball x r) = ballVolume (g i) x r := by
    rw [ballVolume, hball]
  have hω := euclideanUnitBallVolume_pos 3
  apply dimH_gt_two_of_noncollapsed_CX7 hconv μ hv
    (show 0 < euclideanUnitBallVolume 3 * Real.exp 2 by positivity)
  · simpa only [hvol] using hlower
  · filter_upwards [hsec] with i hi
    intro x hx r hr hr1
    have : ConnectedSpace (X i) := connectedSpace_of_aligned_metric (g i) (hmetric i) (p i)
    have hg := (riemannianMetricComplete_iff_completeSpace (hmetric i)).mpr inferInstance
    have hb := ballVolume_le_modelVolume_of_sectional_three (g i) hg hdim x
      (κ := 1) zero_le_one hr (fun y hy => hi y (by
        rw [hball] at hy
        have := dist_triangle y x (p i)
        have hy' := mem_ball.mp hy
        have hx' := mem_ball.mp hx
        change dist y (p i) < 5
        linarith))
    rw [hvol]
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hm := modelVolume_neg_sq_three_le (q := 1) zero_le_one hr.le
    norm_num only [one_pow, one_mul] at hm
    calc modelVolume (-1) 3 r ≤ euclideanUnitBallVolume 3 * r ^ 3 * Real.exp (2 * r) := hm
      _ ≤ euclideanUnitBallVolume 3 * r ^ 3 * Real.exp 2 := by
        gcongr
        linarith
      _ = (euclideanUnitBallVolume 3 * Real.exp 2) * r ^ 3 := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)] in
/-- A growing curvature buffer supplies every fixed `sec ≥ -1` ball. -/
theorem eventually_sectional_neg_one_CX7
    (g : ∀ i, SmoothRiemannianMetric I (X i)) {p : ∀ i, X i} {L : ℕ → ℝ}
    (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ ball (p i) (L i), SectionalBoundedBelowAt (g i) y (-((L i)⁻¹ ^ 2)))
    (R : ℝ) : ∀ᶠ i in atTop, ∀ y ∈ ball (p i) R, SectionalBoundedBelowAt (g i) y (-1) := by
  filter_upwards [hL.eventually (eventually_ge_atTop R),
    hL.eventually (eventually_ge_atTop 1)] with i hi hi1
  intro y hy
  apply (hsec i y (ball_subset_ball hi hy)).mono
  have hinv : (L i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hi1
  have hinv0 : 0 ≤ (L i)⁻¹ := inv_nonneg.mpr (by linarith)
  have hp := pow_le_one₀ hinv0 hinv (n := 2)
  linarith

/-- A nonnegative three-dimensional limit produces uniformly sized almost-Euclidean
balls on the whole converging tail. No volume-convergence theorem is assumed. -/
theorem eventually_almost_euclidean_ball_CX7 [∀ i, ProperSpace (X i)]
    (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {p : ∀ i, X i} {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ ball (p i) (L i), SectionalBoundedBelowAt (g i) y (-((L i)⁻¹ ^ 2)))
    {Y : Type v} [MetricSpace Y] {q : Y} (hconv : PointedGHConverges p q)
    (hcomp : fourPointComparison 0 (univ : Set Y))
    (hdimlo : 2 < dimH (univ : Set Y)) (hdimhi : dimH (univ : Set Y) ≤ 3)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 10) :
    ∃ s : ℝ, 0 < s ∧ s < 1 / 4 ∧ ∀ᶠ i in atTop, ∃ y : X i,
      dist y (p i) < 1 / 2 ∧
      ENNReal.ofReal ((1 - 9 * θ) * euclideanUnitBallVolume 3 * s ^ 3) ≤ ballVolume (g i) y s := by
  have : CompleteSpace Y := hconv.complete_space
  have hcurves := hconv.arbitrarily_short_curves (fun i x y ε hε =>
    Geometry.Metric.exists_arbitrarily_short_riemannian_curve (g i) (hmetric i) x y hε)
  obtain ⟨z, hz, a, b, hp⟩ := exists_rank_three_packet_near_of_dimH_gt_two hcurves hcomp
    hdimlo hdimhi q (r := 1 / 4) (ε := θ / 20) (by norm_num) (by positivity)
  obtain ⟨a₀, A, ha₀, -, hb⟩ := hp.exists_positive_anchor_bounds (by positivity)
    (by linarith [Real.pi_gt_three])
  have hcompare (R : ℝ) (_hR : 0 < R) :
      ∀ᶠ i in atTop, fourPointComparison 1 (ball (p i) R) := by
    filter_upwards [eventually_sectional_neg_one_CX7 g hL hsec (8 * R)] with i hi
    apply fourPointComparison_of_sectional_lower_bound_on_eight_ball (g i) (hmetric i) (p i)
      (by norm_num)
    simpa only [one_pow] using hi
  obtain ⟨r, R, hr, hrsmall, hR, htail⟩ := hp.eventually_uniform_lift hconv hcompare
    (δ := θ / 10) (by linarith) ha₀ hb (mem_ball.mp hz)
  let K := 4 * Real.cosh ((A + 1) + 1) / Real.sinh (a₀ / 2)
  have hK : 0 < K := div_pos (by positivity) (Real.sinh_pos_iff.mpr (by positivity))
  let s := min r (min (1 / 2) (min (a₀ / 8) (θ / (42 * K))))
  have hs : 0 < s := by positivity
  have hsr : s ≤ r := min_le_left _ _
  have hs1 : s ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hsa : s ≤ a₀ / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsK : s ≤ θ / (42 * K) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨s, hs, hsr.trans_lt hrsmall, ?_⟩
  filter_upwards [htail, eventually_sectional_neg_one_CX7 g hL hsec (8 * R)] with i hi hisec
  obtain ⟨y, c, d, hy, -, hanc, hbuf, hpacket, -, hbounds⟩ := hi
  let : RiemannianBundle (fun x : X i => TangentSpace I x) := ⟨(g i).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun x : X i => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric (g i)
  have : IsRiemannianManifold I (X i) := by
    constructor
    intro x y
    change edist x y = riemannianEDistOf (g i) x y
    rw [edist_dist, hmetric]
  have hn := isMetricNorm_of_smoothRiemannianMetric (g i)
  refine ⟨y, hy, strainer_volume_CX7 (g i) hn (p i) hdim hpacket hbuf
    (fun j => hanc (Or.inl ⟨j, rfl⟩)) (fun j => hanc (Or.inr ⟨j, rfl⟩))
    (by simpa only [one_pow] using hisec)
    (fun z hz j => ⟨hbounds z hz _ (Or.inl ⟨j, rfl⟩), hbounds z hz _ (Or.inr ⟨j, rfl⟩)⟩)
    (by positivity) hs (ball_subset_ball (by linarith)) (isCompact_closedBall y s)
    hθ hθ1 (by positivity) le_rfl (by linarith) (by linarith) ?_⟩
  change K * s ≤ θ / 42
  have hh := (le_div_iff₀ (show 0 < 42 * K by positivity)).mp hsK
  linarith

end GC.LongTime.Ch12
