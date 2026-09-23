import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph


set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ThreeSpace M] [ChartedSpace ThreeSpace N]

private theorem compactDomain_isImage (U : CompactDomain M)
    (F : PartialDiffeomorph I3 I3 M N ∞) (hU : U.carrier ⊆ F.source) :
    F.toOpenPartialHomeomorph.IsImage U.carrier (F '' U.carrier) := by
  apply OpenPartialHomeomorph.IsImage.of_image_eq
  change F '' (F.source ∩ U.carrier) = F.target ∩ (F '' U.carrier)
  have htarget : F '' U.carrier ⊆ F.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact F.map_source' (hU hx)
  rw [inter_eq_right.mpr hU, inter_eq_right.mpr htarget]


theorem CompactDomain.image_interior (U : CompactDomain M)
    (F : PartialDiffeomorph I3 I3 M N ∞) (hU : U.carrier ⊆ F.source) :
    F '' interior U.carrier = interior (F '' U.carrier) := by
  have h := (compactDomain_isImage U F hU).interior.image_eq
  change F '' (F.source ∩ interior U.carrier) =
    F.target ∩ interior (F '' U.carrier) at h
  have hs : interior U.carrier ⊆ F.source := interior_subset.trans hU
  have ht : interior (F '' U.carrier) ⊆ F.target := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := interior_subset hy
    exact F.map_source' (hU hx)
  simpa only [inter_eq_right.mpr hs, inter_eq_right.mpr ht] using h

def CompactDomain.restrictOpen (K : CompactDomain M)
    (O : TopologicalSpace.Opens M) (hKO : K.carrier ⊆ O) : CompactDomain O := by
  have himage : Subtype.val '' (Subtype.val ⁻¹' K.carrier : Set O) = K.carrier := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hKO hx⟩, hx, rfl⟩
  have hi : interior (Subtype.val ⁻¹' K.carrier : Set O) =
      Subtype.val ⁻¹' interior K.carrier :=
    (O.isOpenEmbedding'.isOpenMap.preimage_interior_eq_interior_preimage
      O.isOpenEmbedding'.continuous K.carrier).symm
  have hf : frontier (Subtype.val ⁻¹' K.carrier : Set O) =
      Subtype.val ⁻¹' frontier K.carrier :=
    (O.isOpenEmbedding'.isOpenMap.preimage_frontier_eq_frontier_preimage
      O.isOpenEmbedding'.continuous K.carrier).symm
  refine {
    carrier := Subtype.val ⁻¹' K.carrier
    compact := Topology.IsInducing.subtypeVal.isCompact_preimage' K.compact
      (by simpa only [Subtype.range_coe] using hKO)
    connected := ?_
    regular_closed := ?_
    boundary_chart := ?_ }
  · refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := K.connected.nonempty
      exact ⟨⟨x, hKO hx⟩, hx⟩
    · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      change IsPreconnected ((Subtype.val : O → M) '' (Subtype.val ⁻¹' K.carrier : Set O))
      exact himage.symm ▸ K.connected.isPreconnected
  · rw [hi, ← O.isOpenEmbedding'.isOpenMap.preimage_closure_eq_closure_preimage
      O.isOpenEmbedding'.continuous, K.regular_closed]
  · intro x hx
    have hx' : (x : M) ∈ frontier K.carrier := hf.subset hx
    obtain ⟨F, hsrc, hzero, hside⟩ := K.boundary_chart x hx'
    let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) O ⟨x⟩
    refine ⟨inc.trans F, ⟨mem_univ _, hsrc⟩, hzero, ?_⟩
    intro y hy
    exact hside y hy.2

@[simp] theorem CompactDomain.restrictOpen_carrier (K : CompactDomain M)
    (O : TopologicalSpace.Opens M) (hKO : K.carrier ⊆ O) :
    (K.restrictOpen O hKO).carrier = Subtype.val ⁻¹' K.carrier := rfl

theorem CompactDomain.image_restrictOpen_carrier (K : CompactDomain M)
    (O : TopologicalSpace.Opens M) (hKO : K.carrier ⊆ O) :
    Subtype.val '' (K.restrictOpen O hKO).carrier = K.carrier := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hKO hx⟩, hx, rfl⟩

theorem CompactDomain.interior_restrictOpen_carrier (K : CompactDomain M)
    (O : TopologicalSpace.Opens M) (hKO : K.carrier ⊆ O) :
    interior (K.restrictOpen O hKO).carrier = Subtype.val ⁻¹' interior K.carrier :=
  (O.isOpenEmbedding'.isOpenMap.preimage_interior_eq_interior_preimage
    O.isOpenEmbedding'.continuous K.carrier).symm

theorem CompactDomain.frontier_restrictOpen_carrier (K : CompactDomain M)
    (O : TopologicalSpace.Opens M) (hKO : K.carrier ⊆ O) :
    frontier (K.restrictOpen O hKO).carrier = Subtype.val ⁻¹' frontier K.carrier :=
  (O.isOpenEmbedding'.isOpenMap.preimage_frontier_eq_frontier_preimage
    O.isOpenEmbedding'.continuous K.carrier).symm


variable [T2Space M] [T2Space N]


theorem CompactDomain.image_frontier (U : CompactDomain M)
    (F : PartialDiffeomorph I3 I3 M N ∞) (hU : U.carrier ⊆ F.source) :
    F '' frontier U.carrier = frontier (F '' U.carrier) := by
  have hc : IsCompact (F '' U.carrier) :=
    U.compact.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hU)
  have hs0 : frontier U.carrier ⊆ U.carrier := by
    simpa only [U.compact.isClosed.closure_eq] using
      (frontier_subset_closure : frontier U.carrier ⊆ closure U.carrier)
  have ht0 : frontier (F '' U.carrier) ⊆ F '' U.carrier := by
    simpa only [hc.isClosed.closure_eq] using
      (frontier_subset_closure : frontier (F '' U.carrier) ⊆ closure (F '' U.carrier))
  have hs : frontier U.carrier ⊆ F.source := hs0.trans hU
  have ht : frontier (F '' U.carrier) ⊆ F.target := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := ht0 hy
    exact F.map_source' (hU hx)
  have h := (compactDomain_isImage U F hU).frontier.image_eq
  change F '' (F.source ∩ frontier U.carrier) =
    F.target ∩ frontier (F '' U.carrier) at h
  simpa only [inter_eq_right.mpr hs, inter_eq_right.mpr ht] using h


def CompactDomain.map (U : CompactDomain M)
    (F : PartialDiffeomorph I3 I3 M N ∞) (hU : U.carrier ⊆ F.source) :
    CompactDomain N := by
  have hcont : ContinuousOn F U.carrier := F.contMDiffOn_toFun.continuousOn.mono hU
  have hc : IsCompact (F '' U.carrier) := U.compact.image_of_continuousOn hcont
  refine {
    carrier := F '' U.carrier
    compact := hc
    connected := U.connected.image F hcont
    regular_closed := ?_
    boundary_chart := ?_ }
  · rw [← U.image_interior F hU]
    apply subset_antisymm
    · exact closure_minimal (image_mono interior_subset) hc.isClosed
    · have hcont' : ContinuousOn F (closure (interior U.carrier)) := by
        simpa only [U.regular_closed] using hcont
      simpa only [U.regular_closed] using hcont'.image_closure
  · intro y hy
    rw [← U.image_frontier F hU] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxU : x ∈ U.carrier := by
      simpa only [U.compact.isClosed.closure_eq] using frontier_subset_closure hx
    have hxs : x ∈ F.source := hU hxU
    obtain ⟨G, hxG, hzero, hdomain⟩ := U.boundary_chart x hx
    have hleft : F.symm (F x) = x := F.left_inv' hxs
    refine ⟨F.symm.trans G, ?_, ?_, ?_⟩
    · change F x ∈ F.target ∧ F.symm (F x) ∈ G.source
      rw [hleft]
      exact ⟨F.map_source' hxs, hxG⟩
    · change (G (F.symm (F x))) 0 = 0
      rw [hleft]
      exact hzero
    · intro z hz
      change z ∈ F.target ∧ F.symm z ∈ G.source at hz
      change z ∈ F '' U.carrier ↔ (G (F.symm z)) 0 ≤ 0
      exact ((compactDomain_isImage U F hU).symm_apply_mem_iff hz.1).symm.trans
        (hdomain (F.symm z) hz.2)


@[simp] theorem CompactDomain.map_carrier (U : CompactDomain M)
    (F : PartialDiffeomorph I3 I3 M N ∞) (hU : U.carrier ⊆ F.source) :
    (U.map F hU).carrier = F '' U.carrier := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
