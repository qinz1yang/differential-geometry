import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Topology.MetricSpace.CurveMidpoint
import DifferentialGeometry.Topology.MetricSpace.GeodesicMidpoint
import DifferentialGeometry.Topology.MetricSpace.ApproximateMidpoint

namespace GC.MetricGeometry

universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]

theorem PointedBallApprox.exists_approximate_midpoint
    {p : X} {q a b : Y} {M ε : ℝ}
    (f : PointedBallApprox p q (4 * M + 4) ε)
    (hM : 1 ≤ M) (ha : dist a q ≤ M) (hb : dist b q ≤ M)
    (hε : ε < 1 / 4)
    (hmid : ∀ x y : X, ∀ t : ℝ, 0 < t →
      ∃ z : X, dist x z ≤ dist x y / 2 + t ∧ dist y z ≤ dist x y / 2 + t) :
    ∃ z : Y, dist a z < dist a b / 2 + 4 * ε ∧
      dist b z < dist a b / 2 + 4 * ε := by
  obtain ⟨x, hx⟩ := f.coverage a (by linarith)
  obtain ⟨y, hy⟩ := f.coverage b (by linarith)
  have hxr := f.radial_lower x
  have hxtri := dist_triangle (f.toFun x) a q
  rw [dist_comm (f.toFun x) a] at hxtri
  have hxrad : dist x.val p < M + 2 * ε := by linarith
  have hxy := (abs_lt.mp (f.distortion x y)).1
  have hxytri := dist_triangle4 (f.toFun x) a b (f.toFun y)
  rw [dist_comm (f.toFun x) a] at hxytri
  have hxydist : dist x.val y.val < dist a b + 3 * ε := by linarith
  obtain ⟨z, hxz, hyz⟩ := hmid x.val y.val (ε / 2) (by linarith [f.error_pos])
  have hL : dist a b ≤ 2 * M := by
    have ht := dist_triangle a q b
    rw [dist_comm q b] at ht
    linarith
  have hzR : dist z p ≤ 4 * M + 4 := by
    have ht := dist_triangle z x.val p
    rw [dist_comm z x.val] at ht
    linarith
  let zR : BallCarrier p (4 * M + 4) := ⟨z, hzR⟩
  have hfxz := (abs_lt.mp (f.distortion x zR)).2
  have hfyz := (abs_lt.mp (f.distortion y zR)).2
  have hatri := dist_triangle a (f.toFun x) (f.toFun zR)
  have hbtri := dist_triangle b (f.toFun y) (f.toFun zR)
  refine ⟨f.toFun zR, ?_, ?_⟩ <;> dsimp only [zR] at * <;> linarith

theorem PointedGHConverges.approximate_midpoints
    {Z : ℕ → Type u} [∀ n, MetricSpace (Z n)] {p : ∀ n, Z n} {q : Y}
    (h : PointedGHConverges p q)
    (hmid : ∀ n, ∀ x y : Z n, ∀ t : ℝ, 0 < t →
      ∃ z : Z n, dist x z ≤ dist x y / 2 + t ∧ dist y z ≤ dist x y / 2 + t) :
    ∀ a b : Y, ∀ t : ℝ, 0 < t →
      ∃ z : Y, dist a z ≤ dist a b / 2 + t ∧ dist b z ≤ dist a b / 2 + t := by
  intro a b t ht
  let M : ℝ := max 1 (max (dist a q) (dist b q))
  let ε : ℝ := min (t / 8) (1 / 8)
  have hM : 1 ≤ M := le_max_left _ _
  have ha : dist a q ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hb : dist b q ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hεpos : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεt : ε ≤ t / 8 := min_le_left _ _
  have hεbound : ε ≤ 1 / 8 := min_le_right _ _
  obtain ⟨n, hn⟩ := (h.eventually_approx (R := 4 * M + 4) hεpos (by linarith)).exists
  obtain ⟨f⟩ := hn
  obtain ⟨z, haz, hbz⟩ := f.exists_approximate_midpoint hM ha hb (by linarith) (hmid n)
  exact ⟨z, by linarith, by linarith⟩

theorem PointedGHConverges.exists_metric_segment_of_source_curves
    {Z : ℕ → Type u} [∀ n, MetricSpace (Z n)] {p : ∀ n, Z n} {q : Y}
    [ProperSpace Y] (h : PointedGHConverges p q)
    (hcurves : ∀ n, ∀ a b : Z n, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → Z n, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c Set.univ < ENNReal.ofReal (dist a b + ε)) (a b : Y) :
    ∃ f : Set.Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  exact Metric.exists_metric_segment_of_approximate_midpoints
    (h.approximate_midpoints (fun n =>
      Metric.approximate_midpoints_of_arbitrarily_short_curves (hcurves n))) a b

theorem PointedGHConverges.arbitrarily_short_curves
    {Z : ℕ → Type u} [∀ n, MetricSpace (Z n)] {p : ∀ n, Z n} {q : Y}
    (h : PointedGHConverges p q)
    (hcurves : ∀ n, ∀ a b : Z n, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → Z n, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c Set.univ < ENNReal.ofReal (dist a b + ε)) :
    ∀ a b : Y, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → Y, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c Set.univ < ENNReal.ofReal (dist a b + ε) := by
  let : CompleteSpace Y := h.complete_space
  intro a b ε hε
  obtain ⟨c, hc, hca, hcb, _, hlen⟩ :=
    Metric.exists_curve_eVariationOn_lt_of_approximate_midpoints
      (h.approximate_midpoints (fun n =>
        Metric.approximate_midpoints_of_arbitrarily_short_curves (hcurves n))) a b hε
  exact ⟨c, hc, hca, hcb, hlen⟩

end GC.MetricGeometry
