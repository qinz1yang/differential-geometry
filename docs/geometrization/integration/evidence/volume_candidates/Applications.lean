import DifferentialGeometry.Geometry.Metric.Approximation.LimitVolumeLowerBound
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

set_option autoImplicit false
open Set Metric Real Filter MeasureTheory GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped ENNReal

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

example : ∃ v : ℝ, 0 < v ∧ ENNReal.ofReal v ≤
    volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 2) := by
  have hd : dimH (univ : Set (EuclideanSpace ℝ (Fin 3))) = 3 := by
    simp [Real.dimH_univ_eq_finrank]
  have hcomp : fourPointComparison 0 (univ : Set (EuclideanSpace ℝ (Fin 3))) := inner_product_comparison
  obtain ⟨v, hv, ht⟩ := (PointedGHConverges.const (0 : EuclideanSpace ℝ (Fin 3))).eventually_normalizedHausdorffMeasure_ball_lower_bound
    (fun _ => short_curves) (fun R _ => Eventually.of_forall (fun _ =>
      (hcomp.of_zero (by norm_num)).mono (subset_univ _))) hcomp
    (by rw [hd]; norm_num) (by rw [hd])
  obtain ⟨n, hn⟩ := ht.exists
  exact ⟨v, hv, by simpa only [normalizedHausdorffMeasure_euclidean] using hn⟩

example : ENNReal.ofReal (1 / (3 * sqrt 3)) ≤
    volume {w : EuclideanSpace ℝ (Fin 3) | ∀ j, |w j| ≤ 1 / 2} := by
  have hf : LipschitzOnWith (NNReal.sqrt 3) (id : EuclideanSpace ℝ (Fin 3) → _) univ :=
    (LipschitzWith.id.weaken (by norm_num)).lipschitzOnWith
  have hf' : LipschitzOnWith (NNReal.sqrt 3) (id : EuclideanSpace ℝ (Fin 3) → _)
      {w | ∀ j, |w j| ≤ 1 / 2} := hf.mono (subset_univ _)
  have h := (cube_le_normalizedHausdorffMeasure_three hf' (v := 0)
    (e := 2) (by norm_num) (by
      intro w hw
      refine ⟨w, ?_, rfl⟩
      intro j
      have hh := hw j
      norm_num at hh ⊢
      exact hh)).1
  simpa using h

example : ∃ q ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4),
    ∃ a b : Fin 3 → EuclideanSpace ℝ (Fin 3),
      PairedComparisonPacket (1 / 320000) {q} a b ∧ Function.Injective (Sum.elim a b) := by
  obtain ⟨q, hq, a, b, hp⟩ := exists_rank_three_packet_near_of_dimH_gt_two
    short_curves inner_product_comparison
    (by norm_num [Real.dimH_univ_eq_finrank]) (by norm_num [Real.dimH_univ_eq_finrank])
    (0 : EuclideanSpace ℝ (Fin 3)) (r := 1 / 4) (ε := 1 / 320000) (by norm_num) (by norm_num)
  exact ⟨q, hq, a, b, hp, hp.injective_anchors (by linarith [Real.pi_gt_three])⟩
