import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapMaps
import DifferentialGeometry.Topology.Collar.Complement

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry.Topology.ThreeManifold.Surgery

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem exists_pos_negative_half_collar_mem_discardedCap
    (b : (H.event i).transition.trace.tubes.Boundary)
    (hb : (H.event i).transition.trace.capDiscarded b) {r : ℝ} (hr : 0 < r)
    {f : Sphere 2 × Ioo (-r) r → (H.event i).discarded.Carrier}
    (hf : Continuous f) (hinj : Injective f)
    (hmatch : ∀ (s : Sphere 2) (t : Ioo (-r) r) (ht : 0 ≤ t.val)
      (htw : t.val < cuttingCollarWidth (G.delta b.1)),
      f (s, t) = G.discardedCoreCollar b hb (s, ⟨t.val, ht, htw⟩)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧
      ∀ (s : Sphere 2) (t : Ioo (-r) r), -ε < t.val → t.val < 0 →
        f (s, t) ∈ range ((H.event i).transition.trace.discardedCap b hb) \
          range (H.event i).transition.trace.discardedCoreInclusion := by
  classical
  let E := (H.event i).transition.trace
  have hcore : IsCompact E.tubes.core := by
    rw [← G.cutCore_ambientNeckMap]
    exact isCompact_cutCore G.ambientNeckMap G.ambientNeckMap_isOpenEmbedding
  let : CompactSpace E.tubes.core := isCompact_iff_compactSpace.mp hcore
  let : CompactSpace {x : E.tubes.core // x ∉ E.retainedCore} :=
    isCompact_iff_compactSpace.mp E.isClopen_retainedCore.isOpen.isClosed_compl.isCompact
  have hk : _root_.Topology.IsClosedEmbedding E.discardedCoreInclusion :=
    E.discardedCoreInclusion.continuous.isClosedEmbedding
      E.discardedCoreInclusion_isEmbedding.injective
  let c : Sphere 2 × Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1)) →
      {x : E.tubes.core // x ∉ E.retainedCore} := fun q =>
    ⟨G.coreCollar b q, G.coreCollar_not_mem_retainedCore_of_capDiscarded b hb sphereNorth q⟩
  have hc : IsOpenMap c := by
    intro V hV
    have himage : c '' V = Subtype.val ⁻¹' (G.coreCollar b '' V) := by
      ext x
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q, hq, rfl⟩
      · rintro ⟨q, hq, hx⟩
        exact ⟨q, hq, Subtype.ext hx⟩
    rw [himage]
    exact ((G.coreCollar_isOpenEmbedding b).isOpenMap V hV).preimage continuous_subtype_val
  let B := {d : {d : E.tubes.Boundary // E.capDiscarded d} // d ≠ ⟨b, hb⟩}
  let T : Set (H.event i).discarded.Carrier :=
    ⋃ d : B, range (E.discardedCap d.1.1 d.1.2)
  have hT : IsClosed T := isClosed_iUnion_of_finite fun d =>
    (isCompact_range (E.discardedCap d.1.1 d.1.2).continuous).isClosed
  have hzero (s : Sphere 2) : f (s, ⟨0, neg_lt_zero.mpr hr, hr⟩) ∉ T := by
    intro hx
    obtain ⟨d, hd⟩ := mem_iUnion.mp hx
    have hselected : f (s, ⟨0, neg_lt_zero.mpr hr, hr⟩) ∈
        range (E.discardedCap b hb) := by
      refine ⟨sphereToThreeBall ((E.capping.attaching b).symm s), ?_⟩
      rw [G.discardedCap_eq_discardedCoreCollar_zero,
        (E.capping.attaching b).apply_symm_apply]
      exact (hmatch s ⟨0, neg_lt_zero.mpr hr, hr⟩ le_rfl
        (cuttingCollarWidth_pos (G.delta_pos b.1))).symm
    exact disjoint_left.mp (E.pairwise_disjoint_discardedCaps d.2) hd hselected
  obtain ⟨ε, hε, hεr, havoid⟩ :=
    DifferentialGeometry.Topology.Collar.exists_pos_negative_half_collar_subset_compl
      hr (cuttingCollarWidth_pos (G.delta_pos b.1)) hk hc hf hinj hmatch hT hzero
  refine ⟨ε, hε, hεr, ?_⟩
  intro s t ht htn
  have hnot := havoid s t ht htn
  have hcover : f (s, t) ∈ range E.discardedCoreInclusion ∪
      (⋃ d : {d : E.tubes.Boundary // E.capDiscarded d},
        range (E.discardedCap d.1 d.2)) := by
    rw [E.discardedCoreInclusion_union_discardedCaps]
    exact mem_univ _
  refine ⟨?_, fun hx => hnot (Or.inl hx)⟩
  rcases hcover with hx | hx
  · exact (hnot (Or.inl hx)).elim
  · obtain ⟨d, hd⟩ := mem_iUnion.mp hx
    by_cases hdb : d = ⟨b, hb⟩
    · simpa only [hdb] using hd
    · exact (hnot (Or.inr (mem_iUnion.mpr ⟨⟨d, hdb⟩, hd⟩))).elim

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
