import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottRescaling
import DifferentialGeometry.Geometry.Metric.Approximation.RealProductRescaling
import DifferentialGeometry.Geometry.Metric.Approximation.IntervalTargetRescaling
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Set Metric
open GC.MetricGeometry

namespace RescalingRegression

private def exactApprox {X : Type*} [MetricSpace X] (p : X) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) : KleinerLottApprox p p ε where
  error_pos := hε
  error_lt_one := hε1
  toFun := id
  basepoint := rfl
  distortion _ _ _ _ := by simp; exact hε.le
  coverage y hy := by
    have hm : y ∈ id '' ball p ε⁻¹ := ⟨y, by change dist y p < ε⁻¹; linarith, rfl⟩
    exact (infDist_le_dist_of_mem hm).trans (by simpa using hε.le)

private noncomputable def realMap :=
  (exactApprox (0 : ℝ) (ε := 1 / 1000) (by norm_num) (by norm_num)).recenterRescale
    1 (c := 2) (δ := 1 / 100) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Real.dist_eq])

theorem rescale_preserves_far_point :
    @KleinerLottApprox.toFun ℝ ℝ
      ((inferInstance : MetricSpace ℝ).rescale 2 (by norm_num))
      ((inferInstance : MetricSpace ℝ).rescale 2 (by norm_num))
      1 1 (1 / 100) realMap 1000000 = 1000000 := rfl

theorem shifted_scaled_coverage :
    letI : MetricSpace ℝ := (inferInstance : MetricSpace ℝ).rescale 2 (by norm_num)
    ∃ x ∈ @ball ℝ (Real.metricSpace.rescale 2 (by norm_num)).toPseudoMetricSpace
      1 (1 / 100 : ℝ)⁻¹,
      @dist ℝ (Real.metricSpace.rescale 2 (by norm_num)).toDist 40 x < 2 * (1 / 100) := by
  let : MetricSpace ℝ := (inferInstance : MetricSpace ℝ).rescale 2 (by norm_num)
  exact realMap.coverage_witness 40 (by norm_num [realMap, exactApprox, MetricSpace.rescale_dist, Real.dist_eq])

private noncomputable def productMap :=
  (exactApprox (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)))
    (ε := 1 / 1000) (by norm_num) (by norm_num)).recenterRescaleRealProduct
    (WithLp.toLp 2 (1, 0)) (c := 2) (δ := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [WithLp.prod_dist_eq_of_L2, Real.dist_eq])

theorem product_preserves_residual (x : WithLp 2 (ℝ × ℝ)) :
    @KleinerLottApprox.toFun _ _
      ((inferInstance : MetricSpace (WithLp 2 (ℝ × ℝ))).rescale 2 (by norm_num))
      (MetricSpace.scaledProduct inferInstance inferInstance 2 (by norm_num))
      (WithLp.toLp 2 (1, 0)) (WithLp.toLp 2 (0, 0)) (1 / 10) productMap x =
        WithLp.toLp 2 (2 * (x.fst - 1), x.snd) := rfl

private noncomputable def endpointMap :=
  exactApprox (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1)
    (ε := 1 / 1000000) (by norm_num) (by norm_num)

private noncomputable def shiftedPoint : Icc (0 : ℝ) 1 := ⟨1 / 1000000, by norm_num⟩

theorem strict_endpoint_after_contraction :
    letI : MetricSpace (Icc (0 : ℝ) 1) :=
      (inferInstance : MetricSpace (Icc (0 : ℝ) 1)).rescale (999 / 1000) (by norm_num)
    ∃ (L : ℝ) (hL : 0 ≤ L), 1 < L ∧ L = 1001 / 1000 ∧
      ∃ g : KleinerLottApprox shiftedPoint (⟨0, le_rfl, hL⟩ : Icc (0 : ℝ) L) (1 / 10),
        (g.toFun shiftedPoint).val = 0 ∧
        (∀ x, x ≠ shiftedPoint → (g.toFun x).val = (999 / 1000) * x.val) ∧
        ∃ x ∈ @ball (Icc (0 : ℝ) 1)
          ((Subtype.metricSpace : MetricSpace (Icc (0 : ℝ) 1)).rescale
            (999 / 1000) (by norm_num)).toPseudoMetricSpace shiftedPoint (1 / 10 : ℝ)⁻¹,
          dist (⟨L, hL, le_rfl⟩ : Icc (0 : ℝ) L) (g.toFun x) < 2 * (1 / 10) := by
  have h := endpointMap.exists_recenterRescaleInterval_strict (H := 1) (by norm_num)
    shiftedPoint (c := 999 / 1000) (δ := 1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [shiftedPoint, Subtype.dist_eq, Real.dist_eq])
    (by norm_num [shiftedPoint, Subtype.dist_eq, Real.dist_eq])
  let : MetricSpace (Icc (0 : ℝ) 1) :=
    (inferInstance : MetricSpace (Icc (0 : ℝ) 1)).rescale (999 / 1000) (by norm_num)
  obtain ⟨L, hL, hLt, hEq, g, hg, hvalues⟩ := h
  have heq : L = 1001 / 1000 := by norm_num at hEq; exact hEq
  refine ⟨L, hL, hLt, heq, g, congrArg Subtype.val hg, hvalues, ?_⟩
  apply g.coverage_witness
  simp only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hL]
  rw [heq]
  norm_num

#print axioms rescale_preserves_far_point
#print axioms shifted_scaled_coverage
#print axioms product_preserves_residual
#print axioms strict_endpoint_after_contraction
end RescalingRegression
