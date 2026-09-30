import DifferentialGeometry.Geometry.Comparison.RadialContractionEstimate
import DifferentialGeometry.Geometry.Comparison.LocalBufferComparison
import DifferentialGeometry.Topology.MetricSpace.RadialBall

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem radial_contraction_of_chosen_metric_segments
    {X : Type*} [MetricSpace X] {o q : X} {R δ : ℝ}
    (hcomp : fourPointComparison 1 (ball o (2 * R)))
    (hq : q ∈ ball o (R / 2)) (hδ : δ ∈ Ioo 0 R)
    (t : unitInterval) (ht : (t : ℝ) = δ / (2 * R))
    (f : closedBall o R → unitInterval → X)
    (hf0 : ∀ x, f x 0 = q) (hf1 : ∀ x, f x 1 = x)
    (hdist : ∀ x s t, dist (f x s) (f x t) = dist q (x : X) * dist s t) :
    (∀ x, f x t ∈ ball q δ) ∧
      ∀ x y : closedBall o R, (δ / sinh (2 * R)) * dist (x : X) (y : X) ≤ dist (f x t) (f y t) := by
  have hR : 0 < R := hδ.1.trans hδ.2
  have ht0 : 0 < (t : ℝ) := by rw [ht]; exact div_pos hδ.1 (by positivity)
  have ht1 : (t : ℝ) < 1 := by
    rw [ht]
    apply (div_lt_one (by positivity : 0 < 2 * R)).mpr
    linarith [hδ.2]
  have htR : (t : ℝ) * (2 * R) = δ := by rw [ht]; field_simp
  have hrad (x : closedBall o R) : dist q (x : X) < 2 * R := by
    have ha : dist q o < R / 2 := hq
    have hb : dist (x : X) o ≤ R := x.property
    have hc := dist_triangle q o (x : X)
    rw [dist_comm o (x : X)] at hc
    linarith
  have hqu (x : closedBall o R) : dist q (f x t) = (t : ℝ) * dist q (x : X) := by
    have h := hdist x 0 t
    change dist (f x 0) (f x t) = dist q (x : X) * |0 - (t : ℝ)| at h
    rw [hf0, zero_sub, abs_neg, abs_of_nonneg t.property.1] at h
    simpa only [mul_comm] using h
  have hux (x : closedBall o R) : dist (f x t) (x : X) = (1 - (t : ℝ)) * dist q (x : X) := by
    have h := hdist x t 1
    change dist (f x t) (f x 1) = dist q (x : X) * |(t : ℝ) - 1| at h
    rw [hf1, abs_of_nonpos (sub_nonpos.mpr t.property.2)] at h
    nlinarith
  have hmem (x : closedBall o R) : f x t ∈ ball o (2 * R) := by
    apply mem_two_ball_of_radial_between hq x.property
    rw [hqu, hux]
    ring
  constructor
  · intro x
    change dist (f x t) q < δ
    rw [dist_comm, hqu]
    have h := mul_lt_mul_of_pos_left (hrad x) ht0
    rwa [htR] at h
  · intro x y
    have h := dist_radial_points_lower_including_zero_arms hcomp
      ((show dist q o < R / 2 from hq).trans_le (by linarith))
      ((show dist (x : X) o ≤ R from x.property).trans_lt (by linarith))
      ((show dist (y : X) o ≤ R from y.property).trans_lt (by linarith))
      (hmem x) (hmem y) (by positivity : 0 < 2 * R) (hrad x).le (hrad y).le
      ⟨ht0, ht1⟩ (hqu x) (hux x) (hqu y) (hux y)
    rwa [htR] at h

theorem exists_radial_contraction_of_comparison_buffer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L R δ : ℝ} [LocallyCompactSpace (ball o L)]
    (hmargin : 2 * R < L) (hcomp : fourPointComparison 1 (ball o (2 * R)))
    {q : X} (hq : q ∈ ball o (R / 2)) (hδ : δ ∈ Ioo 0 R) :
    ∃ h : closedBall o R → X, (∀ x, h x ∈ ball q δ) ∧
      ∀ x y : closedBall o R, (δ / sinh (2 * R)) * dist (x : X) (y : X) ≤ dist (h x) (h y) := by
  classical
  have hR : 0 < R := hδ.1.trans hδ.2
  choose f hf hf0 hf1 hmem hdist using fun x : closedBall o R =>
    exists_radial_metric_segment_in_two_ball hcurves o hR hmargin hq x.property
  let t : unitInterval := ⟨δ / (2 * R), by
    constructor
    · exact div_nonneg hδ.1.le (by positivity)
    · apply (div_le_one (by positivity : 0 < 2 * R)).mpr
      linarith [hδ.2]⟩
  have h := radial_contraction_of_chosen_metric_segments hcomp hq hδ t rfl f hf0 hf1 hdist
  exact ⟨fun x => f x t, h⟩

theorem exists_radial_contraction_of_local_256_buffer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {R δ : ℝ} (hR : 0 < R) [LocallyCompactSpace (ball o (256 * R))]
    (hlocal : ∀ z ∈ ball o (256 * R),
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ ball o (R / 2)) (hδ : δ ∈ Ioo 0 R) :
    ∃ h : closedBall o R → X, (∀ x, h x ∈ ball q δ) ∧
      ∀ x y : closedBall o R, (δ / sinh (2 * R)) * dist (x : X) (y : X) ≤ dist (h x) (h y) := by
  exact exists_radial_contraction_of_comparison_buffer hcurves o
    (L := 256 * R) (by linarith)
    (fourPointComparison_two_ball_of_local_256_buffer hcurves o (by norm_num) hR hlocal) hq hδ

end DifferentialGeometry.Geometry.Comparison.Toponogov
