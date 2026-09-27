import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.FiniteDimension



noncomputable section

open Set Metric
open scoped ENNReal

namespace DifferentialGeometry.Analysis

variable {F Q : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [PseudoEMetricSpace Q] [CompactSpace Q]



theorem exists_uniform_retraction_radius {e : Q → F} {r : F → Q} {U : Set F}
    (he : Continuous e) (hU : IsOpen U) (heU : range e ⊆ U)
    (hr : ContinuousOn r U) (hleft : ∀ q, r (e q) = q)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q z, dist z (e q) < δ → z ∈ U ∧ edist (r z) q < ε := by
  have hS : IsCompact (range e) := isCompact_range he
  obtain ⟨η, hη, hηU⟩ := hS.exists_cthickening_subset_open hU heU
  obtain ⟨ρ, hρ, hρK⟩ := hS.exists_isCompact_cthickening
  let d := min η ρ
  have hd : 0 < d := lt_min hη hρ
  let K := cthickening d (range e)
  have hKU : K ⊆ U := (cthickening_mono (min_le_left η ρ) _).trans hηU
  have hK : IsCompact K := hρK.of_isClosed_subset isClosed_cthickening
    (cthickening_mono (min_le_right η ρ) _)
  have hur := hK.uniformContinuousOn_of_continuous (hr.mono hKU)
  obtain ⟨τ, hτ, hτr⟩ := EMetric.uniformContinuousOn_iff.mp hur ε hε
  obtain ⟨a, ha, haτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hτ
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  refine ⟨min d (a : ℝ), lt_min hd ha0, ?_⟩
  intro q z hz
  have hzK : z ∈ K := mem_cthickening_of_dist_le z (e q) d (range e)
    (mem_range_self q) (hz.trans_le (min_le_left _ _)).le
  have hqK : e q ∈ K := self_subset_cthickening (range e) (mem_range_self q)
  refine ⟨hKU hzK, ?_⟩
  rw [← hleft q]
  apply hτr hzK hqK
  apply lt_trans _ haτ
  rw [edist_dist]
  simpa only [ENNReal.ofReal_coe_nnreal] using
    (ENNReal.ofReal_lt_ofReal_iff ha0).mpr (hz.trans_le (min_le_right _ _))

end DifferentialGeometry.Analysis
