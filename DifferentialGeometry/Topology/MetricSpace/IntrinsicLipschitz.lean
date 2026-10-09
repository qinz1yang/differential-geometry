import DifferentialGeometry.Topology.MetricSpace.IntrinsicEDist
import DifferentialGeometry.Topology.LocalLipschitzVariation

set_option autoImplicit false

open Set
open scoped Topology ENNReal NNReal

namespace Metric

theorem edist_map_le_intrinsicEDist_of_locally_nonexpanding
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {f : X → Y} (hf : ∀ x, ∃ V ∈ 𝓝 x, LipschitzOnWith 1 f V) (x y : X) :
    edist (f x) (f y) ≤ intrinsicEDist x y := by
  apply le_iInf
  intro p
  have hdist := eVariationOn.edist_le (f ∘ p.extend)
    (s := Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Icc 0 1 by simp)
  have hvar := DifferentialGeometry.Topology.eVariationOn_comp_le_of_locally_lipschitzOn
    (a := 0) (b := 1) p.continuous_extend.continuousOn (fun z _ => hf z)
  simpa only [Function.comp_apply, p.extend_zero, p.extend_one, ENNReal.coe_one,
    one_mul, p.eVariationOn_extend] using hdist.trans hvar

end Metric
