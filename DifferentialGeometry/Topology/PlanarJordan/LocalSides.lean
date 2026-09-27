import DifferentialGeometry.External.Schoenflies.JordanClosed
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

theorem flowBox_halves_in_opposite_regions
    {X : Type*} [TopologicalSpace X] {C U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = Cᶜ) (hfrU : frontier U = C) (hfrV : frontier V = C)
    (e : OpenPartialHomeomorph (ℝ × ℝ) X) {a b ε : ℝ}
    (hab : a < b) (hε : 0 < ε)
    (hsource : Ioo a b ×ˢ Ioo (-ε) ε ⊆ e.source)
    (hcurve : ∀ p ∈ Ioo a b ×ˢ Ioo (-ε) ε, e p ∈ C ↔ p.2 = 0) :
    (e '' (Ioo a b ×ˢ Ioo 0 ε) ⊆ U ∧
      e '' (Ioo a b ×ˢ Ioo (-ε) 0) ⊆ V) ∨
    (e '' (Ioo a b ×ˢ Ioo 0 ε) ⊆ V ∧
      e '' (Ioo a b ×ˢ Ioo (-ε) 0) ⊆ U) := by
  let S : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-ε) ε
  let P : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo 0 ε
  let N : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-ε) 0
  have hPS : P ⊆ S := fun p hp ↦ ⟨hp.1, ⟨by linarith [hp.2.1], hp.2.2⟩⟩
  have hNS : N ⊆ S := fun p hp ↦ ⟨hp.1, ⟨hp.2.1, by linarith [hp.2.2]⟩⟩
  have hPconn : IsPreconnected (e '' P) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image e
      (e.continuousOn.mono (hPS.trans hsource))
  have hNconn : IsPreconnected (e '' N) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image e
      (e.continuousOn.mono (hNS.trans hsource))
  have hPcover : e '' P ⊆ U ∪ V := by
    rintro z ⟨p, hp, rfl⟩
    rw [hcover]
    exact fun hc ↦ hp.2.1.ne' ((hcurve p (hPS hp)).mp hc)
  have hNcover : e '' N ⊆ U ∪ V := by
    rintro z ⟨p, hp, rfl⟩
    rw [hcover]
    exact fun hc ↦ hp.2.2.ne ((hcurve p (hNS hp)).mp hc)
  have hUc : U ⊆ Cᶜ := by rw [← hcover]; exact subset_union_left
  have hVc : V ⊆ Cᶜ := by rw [← hcover]; exact subset_union_right
  have hnot (W Z : Set X) (hfr : frontier Z = C) (hdisj : Disjoint W Z)
      (hZc : Z ⊆ Cᶜ) (hP : e '' P ⊆ W) (hN : e '' N ⊆ W) : False := by
    let p : ℝ × ℝ := ((a + b) / 2, 0)
    have hp : p ∈ S := ⟨⟨by dsimp [p]; linarith, by dsimp [p]; linarith⟩,
      ⟨neg_neg_of_pos hε, hε⟩⟩
    have hpC : e p ∈ C := (hcurve p hp).mpr rfl
    have hpZ : e p ∈ closure Z := frontier_subset_closure (hfr.symm ▸ hpC)
    have hopen : IsOpen (e '' S) :=
      e.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hsource
    obtain ⟨z, ⟨q, hq, rfl⟩, hz⟩ :=
      mem_closure_iff.mp hpZ (e '' S) hopen ⟨p, hp, rfl⟩
    have hqzero : q.2 ≠ 0 := fun heq ↦ hZc hz ((hcurve q hq).mpr heq)
    have hznot : e q ∉ W := fun hw ↦ disjoint_left.mp hdisj hw hz
    apply hznot
    rcases lt_or_gt_of_ne hqzero with hneg | hpos
    · exact hN ⟨q, ⟨hq.1, hq.2.1, hneg⟩, rfl⟩
    · exact hP ⟨q, ⟨hq.1, hpos, hq.2.2⟩, rfl⟩
  rcases hPconn.subset_or_subset hU hV hUV hPcover with hPU | hPV <;>
    rcases hNconn.subset_or_subset hU hV hUV hNcover with hNU | hNV
  · exact (hnot U V hfrV hUV hVc hPU hNU).elim
  · exact Or.inl ⟨hPU, hNV⟩
  · exact Or.inr ⟨hPV, hNU⟩
  · exact (hnot V U hfrU hUV.symm hUc hPV hNV).elim

end DifferentialGeometry.Topology.PlanarJordan

namespace Schoenflies

theorem IsSeparating.local_side_sign
    {C U : Set Plane} (hC : IsSeparating C) (hU : IsOpen U) {a : Plane}
    (haC : a ∈ C) (haU : a ∈ U) (g : Plane → ℝ)
    (hzero : ∀ p ∈ U, p ∈ C ↔ g p = 0)
    (hpos : IsPreconnected (U ∩ {p | 0 < g p}))
    (hneg : IsPreconnected (U ∩ {p | g p < 0})) :
    (∀ p ∈ U, p ∈ inside C ↔ 0 < g p) ∨
      (∀ p ∈ U, p ∈ inside C ↔ g p < 0) := by
  have hcover : ∀ p ∈ U, g p ≠ 0 → p ∈ inside C ∪ outside C := by
    intro p hp hne
    rw [inside_union_outside]
    exact fun hpC => hne ((hzero p hp).mp hpC)
  have hsplitpos : U ∩ {p | 0 < g p} ⊆ inside C ∨
      U ∩ {p | 0 < g p} ⊆ outside C :=
    hpos.subset_or_subset hC.isOpen_inside hC.isOpen_outside disjoint_inside_outside
      (fun p hp => hcover p hp.1 hp.2.ne')
  have hsplitneg : U ∩ {p | g p < 0} ⊆ inside C ∨
      U ∩ {p | g p < 0} ⊆ outside C :=
    hneg.subset_or_subset hC.isOpen_inside hC.isOpen_outside disjoint_inside_outside
      (fun p hp => hcover p hp.1 hp.2.ne)
  have hi : (U ∩ inside C).Nonempty := by
    have ha : a ∈ closure (inside C) := (IsRegionOf.inside C).subset_closure hC haC
    exact (mem_closure_iff.mp ha U hU haU)
  have ho : (U ∩ outside C).Nonempty := by
    have ha : a ∈ closure (outside C) := (IsRegionOf.outside C).subset_closure hC haC
    exact (mem_closure_iff.mp ha U hU haU)
  have hsign : ∀ p ∈ U, p ∉ C → g p < 0 ∨ 0 < g p := by
    intro p hp hpC
    exact lt_or_gt_of_ne (fun he => hpC ((hzero p hp).mpr he))
  rcases hsplitpos with hpi | hpo <;> rcases hsplitneg with hni | hno
  · obtain ⟨p, hpU, hpO⟩ := ho
    rcases hsign p hpU hpO.1 with hn | hp
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside (hni ⟨hpU, hn⟩) hpO)
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside (hpi ⟨hpU, hp⟩) hpO)
  · refine Or.inl fun p hpU => ⟨?_, fun hp => hpi ⟨hpU, hp⟩⟩
    intro hpI
    rcases hsign p hpU hpI.1 with hn | hp
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside hpI (hno ⟨hpU, hn⟩))
    · exact hp
  · refine Or.inr fun p hpU => ⟨?_, fun hp => hni ⟨hpU, hp⟩⟩
    intro hpI
    rcases hsign p hpU hpI.1 with hn | hp
    · exact hn
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside hpI (hpo ⟨hpU, hp⟩))
  · obtain ⟨p, hpU, hpI⟩ := hi
    rcases hsign p hpU hpI.1 with hn | hp
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside hpI (hno ⟨hpU, hn⟩))
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside hpI (hpo ⟨hpU, hp⟩))

end Schoenflies
