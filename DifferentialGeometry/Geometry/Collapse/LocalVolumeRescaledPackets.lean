import DifferentialGeometry.Geometry.Collapse.LocalVolumePackets
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.PointedLimit

set_option autoImplicit false
noncomputable section
open Set Metric Filter Real
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov GC.MetricGeometry
namespace DifferentialGeometry.Geometry.Collapse
universe u v
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Z : ℕ → Type u} [mZ : ∀ n, MetricSpace (Z n)]
  [∀ n, ChartedSpace H (Z n)] [∀ n, IsManifold I ∞ (Z n)]
  [∀ n, SigmaCompactSpace (Z n)] [∀ n, CompleteSpace (Z n)]

/-- LC12–13 on the actual rescaled metrics, retaining the chosen limiting packet. -/
theorem exists_uniform_rescaled_packet_cubes
    (g : ∀ n, SmoothRiemannianMetric I (Z n))
    (hmetric : ∀ n a b, riemannianEDistOf (g n) a b = ENNReal.ofReal (dist a b))
    (p : ∀ n, Z n) {ρ L : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n)
    (hL : Tendsto L atTop atTop)
    (hsec : ∀ n, ∀ y ∈ riemannianBallOf (g n) (p n) (L n * ρ n),
      SectionalBoundedBelowAt (g n) y (-((L n * ρ n) ^ 2)⁻¹))
    {Y : Type v} [MetricSpace Y] {x : Y}
    (hconv : @PointedGHConverges Z
      (fun n => (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))) Y _ p x)
    {q : Y} {a b : Fin 3 → Y}
    (hpacket : PairedComparisonPacket (1 / 320000) {q} a b)
    (hq : dist q x < 1 / 4) :
    letI : ∀ n, MetricSpace (Z n) := fun n =>
      (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))
    ∃ a₀ A r R : ℝ, 0 < a₀ ∧ a₀ ≤ A ∧ 0 < r ∧ r < 1 / 4 ∧ 0 < R ∧
      9 / 10 ≤ (1 - 3 * (1 / 600) ^ 2 - 12 * (1 / 600) : ℝ) ∧
      0 < localVolumeCubeRadius a₀ A r ∧ ∀ᶠ n in atTop,
      ∃ y : Z n, ∃ c d : Fin 3 → Z n,
        dist y (p n) < 1 / 2 ∧
        fourPointComparison 1
          (riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) (p n) R) ∧
        range c ∪ range d ⊆
          riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) (p n) R ∧
        riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) y (2 * r) ⊆
          riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) (p n) R ∧
        PairedComparisonPacket (1 / 600)
          (riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) y (2 * r)) c d ∧
        IsComplete (closedBall y r) ∧
        (∀ z ∈ riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) y (2 * r),
          ∀ w ∈ range c ∪ range d, dist z w ∈ Icc (a₀ / 2) (A + 1)) ∧
        Function.Injective (Sum.elim c d) ∧ y ∉ range c ∪ range d ∧
        {w : EuclideanSpace ℝ (Fin 3) |
          ∀ j, |w j - dist y (c j)| ≤ localVolumeCubeRadius a₀ A r / 4} ⊆
          distanceCoordinates 2 c ''
            riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) y (r / 2) ∧
        LipschitzWith (NNReal.sqrt 3) (distanceCoordinates 2 c)
 := by
  let m' : ∀ n, MetricSpace (Z n) := fun n =>
    (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))
  have : ∀ n, CompleteSpace (Z n) := fun n =>
    ((mZ n).rescale_completeSpace_iff (ρ n)⁻¹ (inv_pos.mpr (hρ n))).mpr inferInstance
  obtain ⟨a₀, A, r, R, ha₀, haA, hr, hrsmall, hR, he, htail⟩ :=
    exists_uniform_local_volume_cubes hconv
      (exists_arbitrarily_short_rescaled_curve (mX := mZ) g hmetric hρ)
      (fun R _ =>
        eventually_fourPointComparison_rescaled_ball (mX := mZ) g hmetric p hρ hL hsec R)
      hpacket hq
  refine ⟨a₀, A, r, R, ha₀, haA, hr, hrsmall, hR, by norm_num, he, ?_⟩
  filter_upwards [htail] with n hn
  obtain ⟨y, c, d, hy, hcn, hanc, hbuf, hp, hc, hb, hcube, hlip⟩ := hn
  have hpy : PairedComparisonPacket (1 / 600) {y} c d :=
    hp.mono (singleton_subset_iff.mpr (mem_ball_self (mul_pos (by norm_num) hr)))
  have hquality : (1 / 600 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hinj := hpy.injective_anchors hquality
  have hne : y ∉ range c ∪ range d := hpy.not_mem_anchors (by simp) hquality
  have hball (v : Z n) (s : ℝ) :
      riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
        (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) v s = ball v s := by
    ext w
    change riemannianEDistOf (scaleMetric ((ρ n)⁻¹ ^ 2)
      (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) v w < ENNReal.ofReal s ↔ dist w v < s
    rw [riemannianEDistOf_scaleMetric_inv_sq_eq_rescale
      (m := mZ n) (g n) (hmetric n) (hρ n), dist_comm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg
  simpa only [hball] using
    ⟨y, c, d, hy, hcn, hanc, hbuf, hp, hc, hb, hinj, hne, hcube, hlip⟩

/-- The original Riemannian data produce the limiting packet and the same uniform cubes. -/
theorem exists_uniform_rescaled_packet_cubes_of_dimH_gt_two
    (hdim : Module.finrank ℝ E = 3)
    (g : ∀ n, SmoothRiemannianMetric I (Z n))
    (hmetric : ∀ n a b, riemannianEDistOf (g n) a b = ENNReal.ofReal (dist a b))
    (p : ∀ n, Z n) {ρ L : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n)
    (hL : Tendsto L atTop atTop)
    (hsec : ∀ n, ∀ y ∈ riemannianBallOf (g n) (p n) (L n * ρ n),
      SectionalBoundedBelowAt (g n) y (-((L n * ρ n) ^ 2)⁻¹))
    {Y : Type v} [MetricSpace Y] {x : Y}
    (hconv : @PointedGHConverges Z
      (fun n => (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))) Y _ p x)
    (hdimY : 2 < dimH (univ : Set Y)) :
    letI : ∀ n, MetricSpace (Z n) := fun n =>
      (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))
    ∃ q ∈ ball x (1 / 4), ∃ a b : Fin 3 → Y,
      PairedComparisonPacket (1 / 320000) {q} a b ∧
      Function.Injective (Sum.elim a b) ∧ q ∉ range a ∪ range b ∧
    ∃ a₀ A r R : ℝ, 0 < a₀ ∧ a₀ ≤ A ∧ 0 < r ∧ r < 1 / 4 ∧ 0 < R ∧
      9 / 10 ≤ (1 - 3 * (1 / 600) ^ 2 - 12 * (1 / 600) : ℝ) ∧
      0 < localVolumeCubeRadius a₀ A r ∧ ∀ᶠ n in atTop,
      ∃ y : Z n, ∃ c d : Fin 3 → Z n,
        dist y (p n) < 1 / 2 ∧
        fourPointComparison 1
          (riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) (p n) R) ∧
        range c ∪ range d ⊆
          riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) (p n) R ∧
        riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) y (2 * r) ⊆
          riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) (p n) R ∧
        PairedComparisonPacket (1 / 600)
          (riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) y (2 * r)) c d ∧
        IsComplete (closedBall y r) ∧
        (∀ z ∈ riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) y (2 * r),
          ∀ w ∈ range c ∪ range d, dist z w ∈ Icc (a₀ / 2) (A + 1)) ∧
        Function.Injective (Sum.elim c d) ∧ y ∉ range c ∪ range d ∧
        {w : EuclideanSpace ℝ (Fin 3) |
          ∀ j, |w j - dist y (c j)| ≤ localVolumeCubeRadius a₀ A r / 4} ⊆
          distanceCoordinates 2 c ''
            riemannianBallOf (scaleMetric ((ρ n)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) y (r / 2) ∧
        LipschitzWith (NNReal.sqrt 3) (distanceCoordinates 2 c)
 := by
  let m' : ∀ n, MetricSpace (Z n) := fun n =>
    (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))
  have : ∀ n, CompleteSpace (Z n) := fun n =>
    ((mZ n).rescale_completeSpace_iff (ρ n)⁻¹ (inv_pos.mpr (hρ n))).mpr inferInstance
  have hκ : ∀ n, 0 ≤ (L n ^ 2)⁻¹ := fun n => inv_nonneg.mpr (sq_nonneg _)
  have hκzero : Tendsto (fun n => (L n ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp hL)
  have hcompY : fourPointComparison 0 (univ : Set Y) :=
    hconv.fourPointComparison_zero_of_eventual_comparison hκ hκzero fun R _ =>
      eventually_fourPointComparison_rescaled_ball_buffer (mX := mZ) g hmetric p hρ hL hsec R
  have hdimle : dimH (univ : Set Y) ≤ 3 := by
    have h := hconv.dimH_le_of_ceil_covering (Module.finrank ℝ E)
      (fun R => 4 * (2 : ℝ) ^ 2 * Real.sqrt (Module.finrank ℝ E) * Real.sinh (2 * R))
      (fun R hR => by positivity)
      (fun R hR η hη _ =>
        eventually_rescaled_ceil_nets (mX := mZ) g hmetric p hρ hL hsec R hR η hη)
    rwa [hdim, Nat.cast_ofNat] at h
  have : CompleteSpace Y := hconv.complete_space
  obtain ⟨q, hq, a, b, hp, hinj, hne⟩ := exists_local_volume_packet
    (hconv.arbitrarily_short_curves
      (exists_arbitrarily_short_rescaled_curve (mX := mZ) g hmetric hρ))
    hcompY hdimY hdimle x
  exact ⟨q, hq, a, b, hp, hinj, hne,
    exists_uniform_rescaled_packet_cubes (mZ := mZ) g hmetric p hρ hL hsec hconv hp
      (mem_ball.mp hq)⟩

end DifferentialGeometry.Geometry.Collapse
