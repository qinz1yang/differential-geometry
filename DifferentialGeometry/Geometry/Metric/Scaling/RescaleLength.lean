import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace MetricSpace

theorem rescale_eVariationOn_le {X α : Type*} [m : MetricSpace X] [LinearOrder α]
    (c : ℝ) (hc : 0 < c) (f : α → X) (s : Set α) :
    @eVariationOn α inferInstance X (m.rescale c hc).toUniformSpace.toTopologicalSpace
      (@PseudoEMetricSpace.toWeakPseudoEMetricSpace X (m.rescale c hc).toPseudoEMetricSpace) f s ≤
        ENNReal.ofReal c * eVariationOn f s := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  change (∑ i ∈ Finset.range n,
    @edist X (m.rescale c hc).toEDist (f (u (i + 1))) (f (u i))) ≤
      ENNReal.ofReal c * eVariationOn f s
  simp_rw [@edist_dist X (m.rescale c hc).toPseudoMetricSpace, rescale_dist,
    ENNReal.ofReal_mul hc.le, ← edist_dist]
  rw [← Finset.mul_sum]
  exact mul_le_mul le_rfl (eVariationOn.sum_le (f := f) hu hus) zero_le zero_le

theorem rescale_arbitrarily_short_curves {X : Type*} [m : MetricSpace X]
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ f : unitInterval → X, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
        eVariationOn f univ < ENNReal.ofReal (dist x y + η))
    (c : ℝ) (hc : 0 < c) (x y : X) {η : ℝ} (hη : 0 < η) :
    ∃ f : unitInterval → X,
      @Continuous unitInterval X inferInstance (m.rescale c hc).toUniformSpace.toTopologicalSpace f ∧
      f 0 = x ∧ f 1 = y ∧
      @eVariationOn unitInterval inferInstance X (m.rescale c hc).toUniformSpace.toTopologicalSpace
        (@PseudoEMetricSpace.toWeakPseudoEMetricSpace X (m.rescale c hc).toPseudoEMetricSpace) f univ <
          ENNReal.ofReal (@dist X (m.rescale c hc).toDist x y + η) := by
  obtain ⟨f, hf, hf0, hf1, hlen⟩ := hcurves x y (η / c) (div_pos hη hc)
  refine ⟨f, hf, hf0, hf1, ?_⟩
  have ht := (rescale_eVariationOn_le c hc f univ).trans_lt
    (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top hlen)
  rw [← ENNReal.ofReal_mul hc.le] at ht
  have heq : c * (dist x y + η / c) = @dist X (m.rescale c hc).toDist x y + η := by
    rw [rescale_dist]
    field_simp
  rwa [heq] at ht

end MetricSpace
