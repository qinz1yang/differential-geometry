import DifferentialGeometry.Geometry.Metric.Approximation.VanishingVolumeDimension
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

set_option autoImplicit false
open Set Metric Real Filter MeasureTheory GC.MetricGeometry
open scoped Topology NNReal ENNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem inner_product_comparison {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : fourPointComparison 0 (univ : Set E) := by
  intro p _ a _ b _ c _ ha hb hc
  have hangle (x y : E) (hx : x ≠ p) (hy : y ≠ p) :
      comparisonAngleNegCurvature 0 (dist p x) (dist p y) (dist x y) =
        InnerProductGeometry.angle (x - p) (y - p) := by
    have hx' : ‖x - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
    have hy' : ‖y - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
    rw [comparisonAngleNegCurvature_zero, comparisonAngle, comparisonCosine,
      dist_comm p x, dist_comm p y, dist_eq_norm x p, dist_eq_norm y p,
      show dist x y = ‖(x - p) - (y - p)‖ by rw [sub_sub_sub_cancel_right, dist_eq_norm],
      norm_sub_sq_real (x - p) (y - p), InnerProductGeometry.angle]
    congr 1
    field_simp
    ring
  rw [hangle a b ha hb, hangle b c hb hc, hangle c a hc ha]
  have h := InnerProductGeometry.angle_le_angle_add_angle (a - p) (-(c - p)) (b - p)
  rw [InnerProductGeometry.angle_neg_right, InnerProductGeometry.angle_neg_left,
    InnerProductGeometry.angle_comm (a - p) (c - p),
    InnerProductGeometry.angle_comm (c - p) (b - p)] at h
  linarith

private theorem short_curves {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ x y : E, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → E, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η) :=
  arbitrarily_short_curves_of_metric_segments (by
    intro x y
    refine ⟨fun t => AffineMap.lineMap x y (t : ℝ),
      AffineMap.lineMap_continuous.comp continuous_subtype_val, ?_, ?_, ?_⟩
    · exact AffineMap.lineMap_apply_zero x y
    · exact AffineMap.lineMap_apply_one x y
    · intro s t
      simpa only [Subtype.dist_eq, mul_comm] using dist_lineMap_lineMap x y (s : ℝ) (t : ℝ))


example : dimH (univ : Set (EuclideanSpace ℝ (Fin 2))) ≤ 2 := by
  let E := EuclideanSpace ℝ (Fin 2)
  have hdim : dimH (univ : Set E) = 2 := by simp [E, Real.dimH_univ_eq_finrank]
  have hzero : normalizedHausdorffMeasure 3 (ball (0 : E) 2) = 0 := by
    have hdB : dimH (ball (0 : E) 2) ≤ dimH (univ : Set E) := dimH_mono (subset_univ _)
    have hdB3 : dimH (ball (0 : E) 2) < (3 : ℝ≥0∞) := hdB.trans_lt (by rw [hdim]; norm_num)
    have hh : MeasureTheory.Measure.hausdorffMeasure (3 : ℝ) (ball (0 : E) 2) = 0 :=
      hausdorffMeasure_of_dimH_lt (d := 3) hdB3
    simp only [normalizedHausdorffMeasure, Measure.smul_apply]
    change euclideanHausdorffFactor 3 • MeasureTheory.Measure.hausdorffMeasure (3 : ℝ) (ball (0 : E) 2) = 0
    rw [hh, smul_zero]
  exact (PointedGHConverges.const (0 : E)).dimH_le_two_of_vanishing_normalizedHausdorffMeasure
    (fun _ => short_curves) (fun R _ => Eventually.of_forall (fun _ =>
      ((inner_product_comparison (E := E)).of_zero (by norm_num)).mono (subset_univ _)))
    inner_product_comparison (by rw [hdim]; norm_num)
    (by simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)))
