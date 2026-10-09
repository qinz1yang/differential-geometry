import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false

open Set Metric Topology

namespace Metric

theorem locallyCompactSpace_subtype_of_compact_closedBalls
    {X : Type*} [MetricSpace X] {U : Set X}
    (hcompact : ∀ p ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ U ∧ IsCompact (closedBall p r)) :
    LocallyCompactSpace U := by
  let : WeaklyLocallyCompactSpace U := ⟨fun p => by
    obtain ⟨r, hr, hsub, hK⟩ := hcompact p p.property
    refine ⟨(Subtype.val : U → X) ⁻¹' closedBall (p : X) r, ?_, ?_⟩
    · exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
        (by simpa only [Subtype.range_val] using hsub)
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ hr)⟩
  infer_instance

end Metric
