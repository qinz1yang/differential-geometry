import Mathlib.Analysis.Real.Pi.Bounds
import DifferentialGeometry.Geometry.Metric.Approximation.MidpointTransfer
import DifferentialGeometry.Geometry.Comparison.FullRankPacket
import DifferentialGeometry.Geometry.Comparison.PairedPacketAnchors
import DifferentialGeometry.Geometry.Comparison.UniformLiftedPacket
import DifferentialGeometry.Geometry.Comparison.UniformImageCube
import DifferentialGeometry.Analysis.Integration.Measure.CubeMeasureBound

set_option autoImplicit false

open Set Metric Filter Real MeasureTheory
open scoped Topology ENNReal NNReal

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u v

theorem PointedGHConverges.eventually_normalizedHausdorffMeasure_ball_lower_bound
    {X : Type v} [MetricSpace X] {Z : ℕ → Type u}
    [∀ n, MetricSpace (Z n)] [∀ n, CompleteSpace (Z n)]
    [∀ n, MeasurableSpace (Z n)] [∀ n, BorelSpace (Z n)]
    {p : ∀ n, Z n} {x : X} (hconv : PointedGHConverges p x)
    (hcurves : ∀ n, ∀ q y : Z n, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → Z n, Continuous c ∧ c 0 = q ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist q y + η))
    (hcomp : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop, fourPointComparison 1 (ball (p n) R))
    (hcompX : fourPointComparison 0 (univ : Set X))
    (hdimlo : 2 < dimH (univ : Set X)) (hdimhi : dimH (univ : Set X) ≤ 3) :
    ∃ v : ℝ, 0 < v ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal v ≤ normalizedHausdorffMeasure 3 (ball (p n) 2) := by
  have : CompleteSpace X := hconv.complete_space
  obtain ⟨q, hq, a, b, hpacket⟩ := exists_rank_three_packet_near_of_dimH_gt_two
    (hconv.arbitrarily_short_curves hcurves) hcompX hdimlo hdimhi x (r := 1 / 4) (ε := 1 / 320000) (by norm_num) (by norm_num)
  obtain ⟨a₀, A, ha₀, _, habounds⟩ := hpacket.exists_positive_anchor_bounds (by norm_num)
    (by linarith [Real.pi_gt_three])
  obtain ⟨r, R, hr, hrsmall, _, htail⟩ := hpacket.eventually_uniform_lift hconv hcomp
    (δ := 1 / 600) (by norm_num) ha₀ habounds (mem_ball.mp hq)
  let δ : ℝ := 1 / 600
  let μ := 1 - 3 * δ ^ 2 - 12 * δ
  let K := 4 * cosh ((A + 1) + 1) / sinh (a₀ / 2)
  let e := min 1 (min ((a₀ / 2) / 2) (min (δ ^ 2 / K) (μ * r / 2)))
  have hδ : 0 < δ := by norm_num [δ]
  have hμ : 0 < μ := by norm_num [μ, δ]
  have hK : 0 < K := div_pos (mul_pos (by norm_num) (cosh_pos _)) (sinh_pos_iff.mpr (half_pos ha₀))
  have he : 0 < e := lt_min zero_lt_one
    (lt_min (half_pos (half_pos ha₀))
      (lt_min (div_pos (sq_pos_of_pos hδ) hK) (by positivity)))
  refine ⟨(e / 2) ^ 3 / (3 * sqrt 3), by positivity, ?_⟩
  filter_upwards [htail] with n hn
  obtain ⟨y, c, d, hy, hcn, hanc, hbuf, hp, hcomplete, hb⟩ := hn
  obtain ⟨_, _, hcube, hlip⟩ := hp.cube_subset_distanceCoordinates_image_three
    (hcurves n) hcn hbuf hanc (half_pos ha₀) hδ (by norm_num [δ]) hr hcomplete
    (Subset.refl _) hb
  change {w : EuclideanSpace ℝ (Fin 3) | ∀ j, |w j - dist y (c j)| ≤ e / 4} ⊆
    distanceCoordinates 2 c '' ball y (r / 2) at hcube
  have hvol := (cube_le_normalizedHausdorffMeasure_three hlip.lipschitzOnWith he
    (v := distanceCoordinates 2 c y) hcube).1
  apply hvol.trans
  apply measure_mono
  intro z hz
  have hz' := mem_ball.mp hz
  have ht := dist_triangle z y (p n)
  rw [mem_ball]
  linarith

end GC.MetricGeometry
