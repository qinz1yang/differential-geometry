import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions.SumProd
import DifferentialGeometry.Topology.CylinderBoundarySide
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Set
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]

theorem isClopen_preimage_of_boundary_collar
    {K S : Set X} (hK : IsClosed K)
    (e : OpenPartialHomeomorph (B × ℝ) X)
    (hfront : frontier K ⊆ e.target)
    (hneg : ∀ p ∈ e.source, p.2 ≤ 0 → e p ∈ K)
    (hpos : ∀ p ∈ e.source, 0 < p.2 → e p ∉ S) :
    IsClopen ((Subtype.val : S → X) ⁻¹' K) := by
  refine ⟨hK.preimage continuous_subtype_val, ?_⟩
  rw [isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxi : x.val ∈ interior K
  · exact Filter.mem_of_superset
      ((isOpen_interior.preimage continuous_subtype_val).mem_nhds hxi)
      (fun _ hy => (interior_subset (s := K)) hy)
  · have hxt : x.val ∈ e.target := hfront ⟨subset_closure hx, hxi⟩
    apply Filter.mem_of_superset
      ((e.open_target.preimage continuous_subtype_val).mem_nhds hxt)
    intro y hy
    have hsrc : e.symm y.val ∈ e.source := e.map_target hy
    have he : e (e.symm y.val) = y.val := e.right_inv hy
    rcases le_or_gt (e.symm y.val).2 0 with hn | hp
    · change y.val ∈ K
      rw [← he]
      exact hneg (e.symm y.val) hsrc hn
    · exact False.elim ((he ▸ hpos (e.symm y.val) hsrc hp) y.property)

private theorem connectedComponent_eq_preimage_of_boundary_collar
    {K S : Set X} (hK : IsClosed K) (hc : IsPreconnected K) (hKS : K ⊆ S)
    (e : OpenPartialHomeomorph (B × ℝ) X)
    (hfront : frontier K ⊆ e.target)
    (hneg : ∀ p ∈ e.source, p.2 ≤ 0 → e p ∈ K)
    (hpos : ∀ p ∈ e.source, 0 < p.2 → e p ∉ S)
    (x : S) (hx : x.val ∈ K) :
    connectedComponent x = (Subtype.val : S → X) ⁻¹' K := by
  have hcl := isClopen_preimage_of_boundary_collar hK e hfront hneg hpos
  have hpre : IsPreconnected ((Subtype.val : S → X) ⁻¹' K) := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hKS]
  exact Set.Subset.antisymm (hcl.connectedComponent_subset hx)
    (hpre.subset_connectedComponent hx)


theorem connectedComponent_eq_preimage_of_outward_collar
    [PreconnectedSpace B] {K S : Set X}
    (hregular : closure (interior K) = K) (hconn : IsPreconnected K) (hcore : K ⊆ S)
    (e : OpenPartialHomeomorph (B × ℝ) X)
    {r : ℝ} (hr : 0 < r) (hsource : univ ×ˢ Ioo (-r) r ⊆ e.source)
    (hfront : frontier K = range (fun z : B => e (z, 0)))
    (hpos : ∀ z : B, ∀ t ∈ Ioo (0 : ℝ) r, e (z, t) ∉ S)
    (x : S) (hx : x.val ∈ K) :
    connectedComponent x = (Subtype.val : S → X) ⁻¹' K := by
  cases isEmpty_or_nonempty B with
  | inl h =>
    let _ : IsEmpty B := h
    have hcl : IsClopen ((Subtype.val : S → X) ⁻¹' K) :=
      (isClopen_iff_frontier_eq_empty.mpr (hfront.trans (by ext y; exact ⟨fun ⟨z, _⟩ => h.false z, False.elim⟩))).preimage continuous_subtype_val
    have hpre : IsPreconnected ((Subtype.val : S → X) ⁻¹' K) := by
      apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hcore]
    exact Set.Subset.antisymm (hcl.connectedComponent_subset hx)
      (hpre.subset_connectedComponent hx)
  | inr h =>
    let _ : Nonempty B := h
    have hclosed : IsClosed K := hregular ▸ isClosed_closure
    have hin (z : B) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) r) :
        e (z, -t) ∈ interior K := by
      obtain h | h := exists_cylinder_orientation_of_frontier_eq
        e hr hsource hregular hfront
      · exact (h z t ht).2
      · exact False.elim (hpos z t ht (hcore (interior_subset (h z t ht).2)))
    let f := e.restrOpen (univ ×ˢ Ioo (-r) r) (isOpen_univ.prod isOpen_Ioo)
    apply connectedComponent_eq_preimage_of_boundary_collar hclosed hconn hcore f _ _ _ x hx
    · rw [hfront]
      rintro _ ⟨z, rfl⟩
      apply f.map_source
      exact ⟨hsource ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩,
        mem_univ _, neg_lt_zero.mpr hr, hr⟩
    · rintro ⟨z, t⟩ hp ht
      change (z, t) ∈ e.source ∩ (univ ×ˢ Ioo (-r) r) at hp
      change e (z, t) ∈ K
      rcases lt_or_eq_of_le ht with hlt | rfl
      · have ht' : -t ∈ Ioo (0 : ℝ) r :=
          ⟨neg_pos.mpr hlt, neg_lt.mp hp.2.2.1⟩
        simpa only [neg_neg] using interior_subset (hin z (-t) ht')
      · exact hclosed.frontier_subset (hfront.symm ▸ mem_range_self z)
    · rintro ⟨z, t⟩ hp ht
      change (z, t) ∈ e.source ∩ (univ ×ˢ Ioo (-r) r) at hp
      exact hpos z t ⟨ht, hp.2.2.2⟩

end DifferentialGeometry.Topology
