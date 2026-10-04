import DifferentialGeometry.Geometry.Metric.Approximation.LimitVolumeLowerBound

set_option autoImplicit false

noncomputable section

open Set Metric Filter Real
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

/-- LC11: the six actual anchors are distinct and avoid the packet centre. -/
theorem exists_local_volume_packet
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdimlo : 2 < dimH (univ : Set X)) (hdimhi : dimH (univ : Set X) ≤ 3) (x : X) :
    ∃ q ∈ ball x (1 / 4), ∃ a b : Fin 3 → X,
      PairedComparisonPacket (1 / 320000) {q} a b ∧
      Function.Injective (Sum.elim a b) ∧ q ∉ range a ∪ range b := by
  obtain ⟨q, hq, a, b, hp⟩ := exists_rank_three_packet_near_of_dimH_gt_two
    hcurves hcomp hdimlo hdimhi x (r := 1 / 4) (ε := 1 / 320000) (by norm_num) (by norm_num)
  have hquality : (1 / 320000 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  exact ⟨q, hq, a, b, hp, hp.injective_anchors hquality,
    hp.not_mem_anchors (by simp) hquality⟩

/-- The LC13 radius, with the LC12 bounds on the entire lifted packet neighbourhood. -/
def localVolumeCubeRadius (a₀ A r : ℝ) : ℝ :=
  min 1 (min ((a₀ / 2) / 2)
    (min ((1 / 600) ^ 2 / (4 * cosh ((A + 1) + 1) / sinh (a₀ / 2)))
      ((1 - 3 * (1 / 600) ^ 2 - 12 * (1 / 600)) * r / 2)))

/-- LC12–13 share the same constants, lifts and tail of the original convergent sequence. -/
theorem exists_uniform_local_volume_cubes
    {X : Type*} [MetricSpace X] {Z : ℕ → Type*}
    [∀ n, MetricSpace (Z n)] [∀ n, CompleteSpace (Z n)]
    {p : ∀ n, Z n} {x q : X} {a b : Fin 3 → X}
    (hconv : PointedGHConverges p x)
    (hcurves : ∀ n, ∀ v w : Z n, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → Z n, Continuous c ∧ c 0 = v ∧ c 1 = w ∧
        eVariationOn c univ < ENNReal.ofReal (dist v w + η))
    (hcomp : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop, fourPointComparison 1 (ball (p n) R))
    (hpacket : PairedComparisonPacket (1 / 320000) {q} a b)
    (hq : dist q x < 1 / 4) :
    ∃ a₀ A r R : ℝ, 0 < a₀ ∧ a₀ ≤ A ∧ 0 < r ∧ r < 1 / 4 ∧ 0 < R ∧
      0 < localVolumeCubeRadius a₀ A r ∧ ∀ᶠ n in atTop,
      ∃ y : Z n, ∃ c d : Fin 3 → Z n,
        dist y (p n) < 1 / 2 ∧ fourPointComparison 1 (ball (p n) R) ∧
        range c ∪ range d ⊆ ball (p n) R ∧ ball y (2 * r) ⊆ ball (p n) R ∧
        PairedComparisonPacket (1 / 600) (ball y (2 * r)) c d ∧
        IsComplete (closedBall y r) ∧
        (∀ z ∈ ball y (2 * r), ∀ v ∈ range c ∪ range d,
          dist z v ∈ Icc (a₀ / 2) (A + 1)) ∧
        {w : EuclideanSpace ℝ (Fin 3) |
          ∀ j, |w j - dist y (c j)| ≤ localVolumeCubeRadius a₀ A r / 4} ⊆
          distanceCoordinates 2 c '' ball y (r / 2) ∧
        LipschitzWith (NNReal.sqrt 3) (distanceCoordinates 2 c) := by
  obtain ⟨a₀, A, ha₀, haA, hab⟩ := hpacket.exists_positive_anchor_bounds
    (by norm_num) (by linarith [Real.pi_gt_three])
  obtain ⟨r, R, hr, hrsmall, hR, htail⟩ := hpacket.eventually_uniform_lift
    hconv hcomp (by norm_num : (1 / 320000 : ℝ) < 1 / 600) ha₀ hab hq
  have hK : 0 < 4 * cosh ((A + 1) + 1) / sinh (a₀ / 2) :=
    div_pos (mul_pos (by norm_num) (cosh_pos _)) (sinh_pos_iff.mpr (half_pos ha₀))
  have he : 0 < localVolumeCubeRadius a₀ A r := by
    unfold localVolumeCubeRadius
    have hμ : 0 < (1 - 3 * (1 / 600) ^ 2 - 12 * (1 / 600) : ℝ) := by norm_num
    exact lt_min zero_lt_one (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  refine ⟨a₀, A, r, R, ha₀, haA, hr, hrsmall, hR, he, ?_⟩
  filter_upwards [htail] with n hn
  obtain ⟨y, c, d, hy, hcn, hanc, hbuf, hp, hc, hb⟩ := hn
  obtain ⟨_, _, hcube, hlip⟩ := hp.cube_subset_distanceCoordinates_image_three
    (hcurves n) hcn hbuf hanc (half_pos ha₀) (by norm_num) (by norm_num)
    hr hc (Subset.refl _) hb
  exact ⟨y, c, d, hy, hcn, hanc, hbuf, hp, hc, hb, hcube, hlip⟩

end DifferentialGeometry.Geometry.Collapse
