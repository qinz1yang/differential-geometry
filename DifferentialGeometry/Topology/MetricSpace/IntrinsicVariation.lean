import DifferentialGeometry.Topology.MetricSpace.IntrinsicEDist
import DifferentialGeometry.Topology.MetricSpace.VariationIsometry

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace Metric

theorem intrinsicEDist_le_eVariationOn_Icc
    {X : Type*} [PseudoEMetricSpace X] {c : unitInterval → X} (hc : Continuous c)
    {s t : unitInterval} (hst : s ≤ t) :
    intrinsicEDist (c s) (c t) ≤ eVariationOn c (Icc s t) := by
  let φ : unitInterval → unitInterval := fun u => min (max u s) t
  have hφ : Continuous φ := by fun_prop
  have h0 : (c ∘ φ) 0 = c s := by
    apply congrArg c
    change min (max (0 : unitInterval) s) t = s
    rw [max_eq_right unitInterval.nonneg', min_eq_left hst]
  have h1 : (c ∘ φ) 1 = c t := by
    apply congrArg c
    change min (max (1 : unitInterval) s) t = t
    rw [max_eq_left unitInterval.le_one', min_eq_right unitInterval.le_one']
  apply (intrinsicEDist_le_curve_variation (hc.comp hφ) h0 h1).trans
  apply eVariationOn.comp_le_of_monotoneOn c φ
  · intro u hu v hv huv
    exact min_le_min (max_le_max huv le_rfl) le_rfl
  · intro u hu
    exact ⟨le_min (le_max_right _ _) hst, min_le_right _ _⟩

theorem intrinsicEMetricSpace_eVariationOn
    {X : Type*} [EMetricSpace X] {c : unitInterval → X} (hc : Continuous c) :
    @eVariationOn unitInterval inferInstance X
      (intrinsicEMetricSpace X).toUniformSpace.toTopologicalSpace
      (@PseudoEMetricSpace.toWeakPseudoEMetricSpace X
        (intrinsicEMetricSpace X).toPseudoEMetricSpace) c univ = eVariationOn c univ := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, hu, hus⟩
    change (∑ i ∈ Finset.range n, intrinsicEDist (c (u (i + 1))) (c (u i))) ≤ eVariationOn c univ
    calc
      (∑ i ∈ Finset.range n, intrinsicEDist (c (u (i + 1))) (c (u i))) ≤
          ∑ i ∈ Finset.range n, eVariationOn c (Icc (u i) (u (i + 1))) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [intrinsicEDist_comm]
        exact intrinsicEDist_le_eVariationOn_Icc hc (hu (Nat.le_succ i))
      _ = eVariationOn c (Icc (u 0) (u n)) := eVariationOn.sum' c hu
      _ ≤ eVariationOn c univ := eVariationOn.mono c (subset_univ _)
  · exact @eVariationOn.le_of_edist_le unitInterval X X inferInstance inferInstance
      (intrinsicEMetricSpace X).toPseudoEMetricSpace c c univ
      (fun a ha b hb => edist_le_intrinsicEDist (c a) (c b))

theorem intrinsicMetricSpace_eVariationOn
    {X : Type*} [EMetricSpace X] (hfinite : ∀ x y : X, intrinsicEDist x y ≠ ⊤)
    {c : unitInterval → X} (hc : Continuous c) :
    @eVariationOn unitInterval inferInstance X
      (intrinsicMetricSpace X hfinite).toUniformSpace.toTopologicalSpace
      (@PseudoEMetricSpace.toWeakPseudoEMetricSpace X
        (intrinsicMetricSpace X hfinite).toPseudoEMetricSpace) c univ = eVariationOn c univ :=
  intrinsicEMetricSpace_eVariationOn hc

end Metric
