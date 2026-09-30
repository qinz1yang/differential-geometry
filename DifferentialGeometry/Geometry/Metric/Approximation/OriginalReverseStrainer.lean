import DifferentialGeometry.Geometry.Metric.Approximation.QuantitativeReverseStrainer
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalProperness

set_option autoImplicit false

open Set Metric

open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

theorem KleinerLottApprox.exists_exact_scale_strainer_of_nonnegative_comparison
    {X Y : Type*} [MetricSpace X] [CompleteSpace X] [MetricSpace Y]
    {p : X} {y : Y} {n k : ℕ} {δ ε : ℝ}
    (φ : KleinerLottApprox p
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), y)) ε)
    (hδ : 0 < δ)
    (hbound : ε ≤ reverseStrainerTolerance δ⁻¹ (min δ 1))
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ n) :
    ∃ a : Fin k × Bool → X,
      (∀ j, dist p (a j) = δ⁻¹) ∧
      (∀ j, dist (φ.toFun (a j))
        (WithLp.toLp 2 (PiLp.single 2 j.1 (if j.2 then δ⁻¹ else -δ⁻¹), y)) < 14 * ε) ∧
      (∀ j l, |dist (a j) (a l) - δ⁻¹ *
        ‖(PiLp.single 2 j.1 (if j.2 then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin k)) -
          PiLp.single 2 l.1 (if l.2 then (1 : ℝ) else -1)‖| < 27 * ε) ∧
      (∀ j, Real.pi - δ < metricComparisonAngle (a (j, true)) p (a (j, false))) ∧
      (∀ j l, j ≠ l → ∀ b c : Bool,
        Real.pi / 2 - δ < metricComparisonAngle (a (j, b)) p (a (l, c))) ∧
      Function.Injective a ∧ ∀ j, a j ≠ p := by
  let : ProperSpace X := properSpace_of_local_comparison_and_dimH hcurves
    (le_refl (0 : ℝ)) hdim (fun x => ⟨univ, isOpen_univ, hcomp, mem_univ x⟩)
  have hsegments := Metric.exists_metric_segment_of_approximate_midpoints
    (Metric.approximate_midpoints_of_arbitrarily_short_curves hcurves)
  obtain ⟨a, hrad, hmap, hpair, hopp, hcross, hinj, hne⟩ :=
    φ.exists_exact_radius_strainer_of_le_reverseStrainerTolerance hsegments
      (inv_pos.mpr hδ) (lt_min hδ zero_lt_one) (min_le_right _ _) hbound
  refine ⟨a, hrad, hmap, hpair, ?_, ?_, hinj, hne⟩
  · intro j
    exact (sub_le_sub_left (min_le_left δ 1) Real.pi).trans_lt (hopp j)
  · intro j l hjl b c
    exact (sub_le_sub_left (min_le_left δ 1) (Real.pi / 2)).trans_lt (hcross j l hjl b c)

end GC.MetricGeometry
