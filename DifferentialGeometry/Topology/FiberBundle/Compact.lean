import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Compactness.LocallyCompact

noncomputable section
open Set Bundle
open scoped Topology

namespace Poincare.Topology.FiberBundle

variable {J B F : Type*} [TopologicalSpace B] [TopologicalSpace F]

theorem isCompact_preimage_of_subset_baseSet [CompactSpace F]
    (Z : FiberBundleCore J B F) (i : J) {K : Set B} (hK : IsCompact K)
    (hsub : K ⊆ Z.baseSet i) : IsCompact (Z.proj ⁻¹' K) := by
  let t := Z.localTriv i
  have hprod : IsCompact (K ×ˢ (univ : Set F)) := hK.prod isCompact_univ
  have hmaps : (K ×ˢ (univ : Set F)) ⊆ t.target := fun _ hp => t.mem_target.mpr (hsub hp.1)
  have hc := hprod.image_of_continuousOn (t.toOpenPartialHomeomorph.continuousOn_symm.mono hmaps)
  have heq : t.toOpenPartialHomeomorph.symm '' (K ×ˢ (univ : Set F)) = Z.proj ⁻¹' K := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, _⟩, rfl⟩
      change Z.proj (t.toOpenPartialHomeomorph.symm (x, y)) ∈ K
      rwa [t.proj_symm_apply' (hsub hx)]
    · intro hz
      have hsrc : z ∈ t.source := t.mem_source.mpr (hsub hz)
      refine ⟨t z, ⟨?_, mem_univ _⟩, t.toOpenPartialHomeomorph.left_inv hsrc⟩
      change (t.toOpenPartialHomeomorph z).1 ∈ K
      rwa [t.proj_toFun z hsrc]
  rwa [heq] at hc

theorem compactSpace_totalSpace [T2Space B] [CompactSpace B] [CompactSpace F]
    (Z : FiberBundleCore J B F) : CompactSpace Z.TotalSpace := by
  choose K hKc hKint hKsub using fun x : B =>
    exists_compact_subset (Z.isOpen_baseSet (Z.indexAt x)) (Z.mem_baseSet_at x)
  obtain ⟨s, _, hs⟩ := isCompact_univ.elim_nhds_subcover K
    (fun x _ => mem_interior_iff_mem_nhds.mp (hKint x))
  have hc : IsCompact (⋃ x ∈ s, Z.proj ⁻¹' K x) :=
    s.isCompact_biUnion fun x _ => isCompact_preimage_of_subset_baseSet Z (Z.indexAt x) (hKc x) (hKsub x)
  have heq : (⋃ x ∈ s, Z.proj ⁻¹' K x) = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ (Z.proj z)))
    obtain ⟨hxs, hz⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxs, hz⟩⟩
  exact ⟨heq ▸ hc⟩

end Poincare.Topology.FiberBundle
