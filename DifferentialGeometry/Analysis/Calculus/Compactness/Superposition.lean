import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.FiniteDimension



noncomputable section

open Set Metric

namespace DifferentialGeometry.Analysis

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [PseudoMetricSpace F]



theorem exists_uniform_superposition_radius {c : K → E} {g : E → F} {U : Set E}
    (hc : Continuous c) (hU : IsOpen U) (hcU : range c ⊆ U) (hg : ContinuousOn g U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k z, dist z (c k) < δ →
      z ∈ U ∧ dist (g z) (g (c k)) < ε := by
  have hS : IsCompact (range c) := isCompact_range hc
  obtain ⟨η, hη, hηU⟩ := hS.exists_cthickening_subset_open hU hcU
  obtain ⟨ρ, hρ, hρK⟩ := hS.exists_isCompact_cthickening
  let d := min η ρ
  have hd : 0 < d := lt_min hη hρ
  let A := cthickening d (range c)
  have hAU : A ⊆ U := (cthickening_mono (min_le_left η ρ) _).trans hηU
  have hA : IsCompact A := hρK.of_isClosed_subset isClosed_cthickening
    (cthickening_mono (min_le_right η ρ) _)
  obtain ⟨a, ha, hag⟩ := Metric.uniformContinuousOn_iff.mp
    (hA.uniformContinuousOn_of_continuous (hg.mono hAU)) ε hε
  refine ⟨min d a, lt_min hd ha, fun k z hz => ?_⟩
  have hzA : z ∈ A := mem_cthickening_of_dist_le z (c k) d (range c)
    (mem_range_self k) (hz.trans_le (min_le_left _ _)).le
  have hkA : c k ∈ A := self_subset_cthickening (range c) (mem_range_self k)
  exact ⟨hAU hzA, hag z hzA (c k) hkA (hz.trans_le (min_le_right _ _))⟩

end DifferentialGeometry.Analysis
