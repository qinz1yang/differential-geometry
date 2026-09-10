import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

namespace Poincare.Topology.Compactness

open Set

theorem isCompact_coordinate_band_of_product_chart
    {N M : Type*} [TopologicalSpace N] [CompactSpace N] [TopologicalSpace M]
    (e : OpenPartialHomeomorph (N × ℝ) M) (a b : ℝ)
    (hsource : (univ : Set N) ×ˢ Icc a b ⊆ e.source) :
    IsCompact (e.target ∩ (fun x ↦ (e.symm x).2) ⁻¹' Icc a b) := by
  have heq : e '' ((univ : Set N) ×ˢ Icc a b) =
      e.target ∩ (fun x ↦ (e.symm x).2) ⁻¹' Icc a b := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨e.map_source (hsource hp), ?_⟩
      change (e.symm (e p)).2 ∈ Icc a b
      rw [e.left_inv (hsource hp)]
      exact hp.2
    · rintro ⟨hx, hband⟩
      exact ⟨e.symm x, ⟨mem_univ _, hband⟩, e.right_inv hx⟩
  rw [← heq]
  exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (e.continuousOn.mono hsource)

theorem closure_coordinate_band_subset_target_of_product_chart
    {N M : Type*} [TopologicalSpace N] [CompactSpace N] [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph (N × ℝ) M) (a b : ℝ)
    (hsource : (univ : Set N) ×ˢ Icc a b ⊆ e.source) :
    closure (e.target ∩ (fun x ↦ (e.symm x).2) ⁻¹' Icc a b) ⊆ e.target := by
  rw [(isCompact_coordinate_band_of_product_chart e a b hsource).isClosed.closure_eq]
  exact inter_subset_left

end Poincare.Topology.Compactness
