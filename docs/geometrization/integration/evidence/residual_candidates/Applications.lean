import DifferentialGeometry.Geometry.Metric.Approximation.TestedResidualParameter
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.EscapingPoint
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

set_option autoImplicit false
open Set Metric Real Filter GC.MetricGeometry
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


example : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∃ F : KleinerLottApprox (0 : EuclideanSpace ℝ (Fin 2))
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), PUnit.unit)) δ,
      (∀ x, (F.toFun x).fst = x) ∧
      ∀ x, dist x 0 ≤ 201 → dist (F.toFun x).snd PUnit.unit < 1 := by
  let E := EuclideanSpace ℝ (Fin 2)
  obtain ⟨η, hη, hηone, ht⟩ := exists_tested_residual_parameter_of_nonnegative_models
    (n := 2) (by norm_num) 201 1 (by norm_num)
  let e := (IsometryEquiv.withLpProdUnique 2 E PUnit).symm
  have hη1 : η < 1 := by linarith
  let F := e.toKleinerLottApprox (p := (0 : E)) rfl hη hη1
  let g := (IsometryEquiv.refl E).toKleinerLottApprox (p := (0 : E)) rfl hη hη1
  refine ⟨η, hη, hη1, F, fun _ => rfl, ?_⟩
  exact ht E 0 E 0 short_curves (by norm_num [E, Real.dimH_univ_eq_finrank])
    inner_product_comparison PUnit PUnit.unit η η le_rfl le_rfl g F

example : dist (WithLp.toLp 2 ((3 : ℝ), (4 : ℝ))).snd
    (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))).snd ^ 2 ≤ 20 := by
  let x := WithLp.toLp 2 ((3 : ℝ), (4 : ℝ))
  let y := WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))
  have hd : dist x y = 5 := by
    apply (sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 5)).mp
    rw [WithLp.prod_dist_sq_eq_add_sq]
    norm_num [x, y, Real.dist_eq]
  have hh := WithLp.snd_dist_sq_le_of_fst_dist_gap x y (B := 5) (η := 2)
    hd.le (by rw [hd]; norm_num [x, y, Real.dist_eq])
  norm_num at hh
  exact hh

example : ∃ (δ : ℝ) (N : ℕ), 0 < δ ∧ δ < 1 ∧
    1000 < dist (EscapingPoint.farPoint N) (EscapingPoint.basepoint N) ∧
    ∃ F : KleinerLottApprox (0 : EuclideanSpace ℝ (Fin 2))
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), EscapingPoint.basepoint N)) δ,
      ∀ x, dist x 0 ≤ 201 → dist (F.toFun x).snd (EscapingPoint.basepoint N) < 1 := by
  let E := EuclideanSpace ℝ (Fin 2)
  obtain ⟨η, hη, hηone, ht⟩ := exists_tested_residual_parameter_of_nonnegative_models
    (n := 2) (by norm_num) 201 1 (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1000 η⁻¹)
  have hlarge : η⁻¹ < (N : ℝ) + 1 := by linarith [le_max_right (1000 : ℝ) η⁻¹]
  have hη1 : η < 1 := by linarith
  let b := EscapingPoint.basepoint N
  let F : KleinerLottApprox (0 : E) (WithLp.toLp 2 ((0 : E), b)) η := {
    error_pos := hη
    error_lt_one := hη1
    toFun := fun x => WithLp.toLp 2 (x, b)
    basepoint := rfl
    distortion := by
      intro x _ y _
      rw [(WithLp.isometry_prodMk_right (E := E) b).dist_eq x y]
      simpa only [sub_self, abs_zero] using hη.le
    coverage := by
      intro y hy
      have hsy : dist y.snd b ≤ dist y (WithLp.toLp 2 ((0 : E), b)) :=
        WithLp.dist_snd_le y (WithLp.toLp 2 ((0 : E), b))
      have hsyb : y.snd = b := EscapingPoint.eq_basepoint_of_mem_ball hlarge y.snd (by linarith)
      have hyrep : y = WithLp.toLp 2 (y.fst, b) := by
        apply (WithLp.equiv 2 _).injective
        exact Prod.ext rfl hsyb
      have hd : dist y.fst (0 : E) = dist y (WithLp.toLp 2 ((0 : E), b)) := by
        rw [hyrep]
        exact ((WithLp.isometry_prodMk_right (E := E) b).dist_eq y.fst 0).symm
      have hm : y ∈ (fun x : E => WithLp.toLp 2 (x, b)) '' ball 0 η⁻¹ :=
        ⟨y.fst, by rw [mem_ball, hd]; linarith, hyrep.symm⟩
      exact (Metric.infDist_le_dist_of_mem hm).trans (by simpa only [dist_self] using hη.le) }
  let g := (IsometryEquiv.refl E).toKleinerLottApprox (p := (0 : E)) rfl hη hη1
  refine ⟨η, N, hη, hη1, ?_, F, ?_⟩
  · rw [EscapingPoint.dist_farPoint_basepoint]
    linarith [le_max_left (1000 : ℝ) η⁻¹]
  · exact ht E 0 E 0 short_curves (by norm_num [E, Real.dimH_univ_eq_finrank])
      inner_product_comparison (EscapingPoint.Carrier N) b η η le_rfl le_rfl g F
