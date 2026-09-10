import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

namespace DifferentialGeometry.Topology.Compactness

open Set

theorem isCompact_coordinate_band_of_opens_product_chart
    {N M : Type*} [TopologicalSpace N] [CompactSpace N] [TopologicalSpace M]
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (e : O ≃ₜ V) (U : Set O) (χ : ℝ ≃ₜ ℝ) (q : M → ℝ)
    (hq : ∀ p : O, q (e p) = χ (p : N × ℝ).2) (l r : ℝ)
    (hband : (univ : Set N) ×ˢ (χ ⁻¹' Icc l r) ⊆ Subtype.val '' U) :
    IsCompact ((Subtype.val '' (e '' U)) ∩ q ⁻¹' Icc l r) := by
  let B : Set (N × ℝ) := univ ×ˢ (χ ⁻¹' Icc l r)
  have hB : IsCompact B := isCompact_univ.prod (χ.isCompact_preimage.mpr isCompact_Icc)
  have hBO : B ⊆ range (Subtype.val : O → N × ℝ) := by
    intro p hp
    obtain ⟨z, _, hz⟩ := hband hp
    exact ⟨z, hz⟩
  have hcompact : IsCompact ((Subtype.val : O → N × ℝ) ⁻¹' B) :=
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hB hBO
  have heq : (fun p : O ↦ (e p : M)) '' ((Subtype.val : O → N × ℝ) ⁻¹' B) =
      (Subtype.val '' (e '' U)) ∩ q ⁻¹' Icc l r := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨z, hz, he⟩ := hband hp
      have hzp : z = p := Subtype.val_injective he
      subst z
      refine ⟨⟨e p, ⟨p, hz, rfl⟩, rfl⟩, ?_⟩
      change q (e p) ∈ Icc l r
      rw [hq]
      exact hp.2
    · rintro ⟨⟨y, ⟨p, hp, rfl⟩, rfl⟩, hqband⟩
      refine ⟨p, ⟨mem_univ _, ?_⟩, rfl⟩
      change χ (p : N × ℝ).2 ∈ Icc l r
      rwa [← hq]
  rw [← heq]
  exact hcompact.image (continuous_subtype_val.comp e.continuous)

end DifferentialGeometry.Topology.Compactness
