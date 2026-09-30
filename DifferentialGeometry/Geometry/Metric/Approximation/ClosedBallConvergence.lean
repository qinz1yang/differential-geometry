import DifferentialGeometry.Geometry.Metric.Approximation.CompactComparison
import DifferentialGeometry.Topology.MetricSpace.GeodesicMidpoint
import DifferentialGeometry.Topology.MetricSpace.CurveMidpoint

open Set Filter
open scoped Topology

universe u v

namespace Metric

theorem exists_radial_trimming_of_metric_segments {Y : Type v} [MetricSpace Y]
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (q y : Y) {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hy : dist y q ≤ r + δ) :
    ∃ z : Y, dist z q ≤ r ∧ dist y z ≤ δ := by
  by_cases hyr : dist y q ≤ r
  · exact ⟨y, hyr, by simpa using hδ⟩
  have hD : 0 < dist q y := by rw [dist_comm]; linarith
  have hrD : r ≤ dist q y := by rw [dist_comm]; linarith
  obtain ⟨f, _, hf0, hf1, hdist⟩ := hsegments q y
  let t : Icc (0 : ℝ) 1 :=
    ⟨r / dist q y, div_nonneg hr hD.le, (div_le_one hD).mpr hrD⟩
  have hrad : dist (f t) q = r := by
    rw [← hf0, hdist]
    change dist q y * |r / dist q y - 0| = r
    rw [sub_zero, abs_of_nonneg (div_nonneg hr hD.le)]
    exact mul_div_cancel₀ r hD.ne'
  have hmove : dist y (f t) = dist q y - r := by
    conv_lhs => rw [← hf1, hdist]
    change dist q y * |1 - r / dist q y| = dist q y - r
    rw [abs_of_nonneg (sub_nonneg.mpr t.property.2)]
    dsimp [t]
    field_simp
  refine ⟨f t, hrad.le, ?_⟩
  rw [hmove, dist_comm q y]
  linarith

end Metric

namespace GC.MetricGeometry

instance BallCarrier.compactSpace {X : Type u} [MetricSpace X] [ProperSpace X]
    (p : X) (R : ℝ) : CompactSpace (BallCarrier p R) := by
  change CompactSpace (Metric.closedBall p R)
  infer_instance

theorem PointedBallApprox.ghDist_closedBall_le_of_metric_segments
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    [ProperSpace X] [ProperSpace Y] {p : X} {q : Y} {R ε : ℝ}
    [Nonempty (BallCarrier p R)] [Nonempty (BallCarrier q R)]
    (f : PointedBallApprox p q R ε)
    (hsegments : ∀ a b : Y, ∃ g : Icc (0 : ℝ) 1 → Y, Continuous g ∧
      g ⟨0, by norm_num⟩ = a ∧ g ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (g s) (g t) = dist a b * dist s t) :
    GromovHausdorff.ghDist (BallCarrier p R) (BallCarrier q R) ≤ 9 * ε / 2 := by
  classical
  have hR : 0 ≤ R := (f.error_pos.trans f.error_lt_radius).le
  have htrim : ∀ x : BallCarrier p R, ∃ z : Y,
      dist z q ≤ R ∧ dist (f.toFun x) z ≤ ε := by
    intro x
    apply Metric.exists_radial_trimming_of_metric_segments hsegments q (f.toFun x)
      hR f.error_pos.le
    linarith [f.radial_upper x, x.property]
  choose g hgR hgmove using htrim
  let F : BallCarrier p R → BallCarrier q R := fun x => ⟨g x, hgR x⟩
  have hdist : ∀ x x' : BallCarrier p R,
      |dist (F x) (F x') - dist x x'| ≤ 3 * ε := by
    intro x x'
    have hf := abs_lt.mp (f.distortion x x')
    have h1 := dist_triangle (g x) (f.toFun x) (f.toFun x')
    have h2 := dist_triangle (g x) (f.toFun x') (g x')
    have h3 := dist_triangle (f.toFun x) (g x) (g x')
    have h4 := dist_triangle (f.toFun x) (g x') (f.toFun x')
    rw [dist_comm (g x) (f.toFun x)] at h1
    rw [dist_comm (g x') (f.toFun x')] at h4
    change |dist (g x) (g x') - dist x.val x'.val| ≤ 3 * ε
    apply abs_le.mpr
    constructor <;> linarith [hgmove x, hgmove x']
  have hcover : ∀ y : BallCarrier q R, ∃ x : BallCarrier p R,
      dist y (F x) ≤ 3 * ε := by
    intro y
    obtain ⟨z, hzR, hyz⟩ := Metric.exists_radial_trimming_of_metric_segments
      hsegments q y.val (sub_nonneg.mpr f.error_lt_radius.le) f.error_pos.le
      (r := R - ε) (δ := ε) (by simpa using y.property)
    obtain ⟨x, hx⟩ := f.coverage z hzR
    refine ⟨x, ?_⟩
    have h1 := dist_triangle y.val z (f.toFun x)
    have h2 := dist_triangle y.val (f.toFun x) (g x)
    change dist y.val (g x) ≤ 3 * ε
    linarith [hgmove x]
  have h := GromovHausdorff.ghDist_le_of_map F hdist hcover
  linarith

theorem PointedGHConverges.tendsto_ghDist_closedBall_of_metric_segments
    {X : ℕ → Type u} {Y : Type v} [∀ n, MetricSpace (X n)] [MetricSpace Y]
    [∀ n, ProperSpace (X n)] [ProperSpace Y] {p : ∀ n, X n} {q : Y}
    (h : PointedGHConverges p q) {R : ℝ} (hR : 0 < R)
    (hsegments : ∀ a b : Y, ∃ g : Icc (0 : ℝ) 1 → Y, Continuous g ∧
      g ⟨0, by norm_num⟩ = a ∧ g ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (g s) (g t) = dist a b * dist s t) :
    letI : ∀ n, Nonempty (BallCarrier (p n) R) :=
      fun n => ⟨⟨p n, by simpa using hR.le⟩⟩
    letI : Nonempty (BallCarrier q R) := ⟨⟨q, by simpa using hR.le⟩⟩
    Tendsto (fun n => GromovHausdorff.ghDist (BallCarrier (p n) R) (BallCarrier q R))
      atTop (𝓝 0) := by
  let : ∀ n, Nonempty (BallCarrier (p n) R) :=
    fun n => ⟨⟨p n, by simpa using hR.le⟩⟩
  let : Nonempty (BallCarrier q R) := ⟨⟨q, by simpa using hR.le⟩⟩
  rw [Metric.tendsto_atTop]
  intro η hη
  let ε := min (η / 10) (R / 2)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεR : ε < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually_approx hε hεR)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨f⟩ := hN n hn
  have hb := f.ghDist_closedBall_le_of_metric_segments hsegments
  have hsmall : ε ≤ η / 10 := min_le_left _ _
  have hnonneg : 0 ≤
      GromovHausdorff.ghDist (BallCarrier (p n) R) (BallCarrier q R) := dist_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

theorem PointedGHConverges.tendsto_ghDist_closedBall_of_approximate_midpoints
    {X : ℕ → Type u} {Y : Type v} [∀ n, MetricSpace (X n)] [MetricSpace Y]
    [∀ n, ProperSpace (X n)] [ProperSpace Y] {p : ∀ n, X n} {q : Y}
    (h : PointedGHConverges p q) {R : ℝ} (hR : 0 < R)
    (hmid : ∀ a b : Y, ∀ η : ℝ, 0 < η → ∃ z, dist a z ≤ dist a b / 2 + η ∧
      dist b z ≤ dist a b / 2 + η) :
    letI : ∀ n, Nonempty (BallCarrier (p n) R) :=
      fun n => ⟨⟨p n, by simpa using hR.le⟩⟩
    letI : Nonempty (BallCarrier q R) := ⟨⟨q, by simpa using hR.le⟩⟩
    Tendsto (fun n => GromovHausdorff.ghDist (BallCarrier (p n) R) (BallCarrier q R))
      atTop (𝓝 0) :=
  h.tendsto_ghDist_closedBall_of_metric_segments hR
    (Metric.exists_metric_segment_of_approximate_midpoints hmid)

theorem PointedGHConverges.tendsto_ghDist_closedBall_of_arbitrarily_short_curves
    {X : ℕ → Type u} {Y : Type v} [∀ n, MetricSpace (X n)] [MetricSpace Y]
    [∀ n, ProperSpace (X n)] [ProperSpace Y] {p : ∀ n, X n} {q : Y}
    (h : PointedGHConverges p q) {R : ℝ} (hR : 0 < R)
    (hcurves : ∀ a b : Y, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → Y, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η)) :
    letI : ∀ n, Nonempty (BallCarrier (p n) R) :=
      fun n => ⟨⟨p n, by simpa using hR.le⟩⟩
    letI : Nonempty (BallCarrier q R) := ⟨⟨q, by simpa using hR.le⟩⟩
    Tendsto (fun n => GromovHausdorff.ghDist (BallCarrier (p n) R) (BallCarrier q R))
      atTop (𝓝 0) :=
  h.tendsto_ghDist_closedBall_of_approximate_midpoints hR
    (Metric.approximate_midpoints_of_arbitrarily_short_curves hcurves)

end GC.MetricGeometry
