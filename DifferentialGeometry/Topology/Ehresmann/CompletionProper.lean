import DifferentialGeometry.Topology.Ehresmann.IntervalCompletionSpace
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Compactness.SigmaCompact

noncomputable section
open Set Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {M : Type*} [TopologicalSpace M] [CompactSpace M]

theorem isProperMap_intervalCompletionHeight {u : M → ℝ} (hu : Continuous u) (a b : ℝ) :
    IsProperMap (intervalCompletionHeight u a b) := by
  have hc : Continuous (intervalCompletionHeight u a b) :=
    continuous_snd.comp continuous_subtype_val
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hc, ?_⟩
  intro K hK
  obtain ⟨r, hr⟩ := hK.bddBelow
  obtain ⟨s, hs⟩ := hK.bddAbove
  exact (isCompact_preimage_Icc_intervalCompletionHeight hu a b r s).of_isClosed_subset
    (hK.isClosed.preimage hc) (fun q hq ↦ ⟨hr hq, hs hq⟩)

theorem sigmaCompactSpace_intervalCompletionSpace {u : M → ℝ} (hu : Continuous u) (a b : ℝ) :
    SigmaCompactSpace (IntervalCompletionSpace u a b) := by
  apply SigmaCompactSpace_iff_exists_compact_covering.mpr
  refine ⟨fun n ↦ intervalCompletionHeight u a b ⁻¹' Icc (-(n : ℝ)) n,
    (fun n ↦ isCompact_preimage_Icc_intervalCompletionHeight hu a b (-(n : ℝ)) n), ?_⟩
  apply eq_univ_of_forall
  intro q
  obtain ⟨n, hn⟩ := exists_nat_ge |intervalCompletionHeight u a b q|
  exact mem_iUnion.mpr ⟨n, abs_le.mp hn⟩

end DifferentialGeometry.Topology.Ehresmann
