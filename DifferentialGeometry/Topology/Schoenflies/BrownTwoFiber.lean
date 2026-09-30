import DifferentialGeometry.Topology.Cellular.CellularFiber
import DifferentialGeometry.Topology.Cellular.CellNeighborhood

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

section

variable {n : ℕ}
    {f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}
    {A B : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}

theorem isCellular_second_fiber_of_two_fibers (hf : Continuous f)
    (hfs : Function.Surjective f)
    (hfAB : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hAB : Disjoint A B) (hproper : A ∪ B ≠ univ) : isCellular n B := by
  classical
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  obtain ⟨c, hABC, hcproper⟩ := exists_embeddedClosedCell_sphere_of_isCompact (hA.union hB) hproper
  let A' : Set (Disk n) := c.map ⁻¹' A
  let B' : Set (Disk n) := c.map ⁻¹' B
  let F := f ∘ c.map
  have hF : Continuous F := hf.comp c.isClosedEmbedding.continuous
  have hFA'B' : ∀ x y, F x = F y ↔ x = y ∨ (x ∈ A' ∧ y ∈ A') ∨ (x ∈ B' ∧ y ∈ B') := by
    intro x y
    simpa only [F, A', B', mem_preimage, Function.comp_apply,
      c.isClosedEmbedding.injective.eq_iff] using
      hfAB (c.map x) (c.map y)
  have hA'I : A' ⊆ diskInterior n := by
    intro x hx
    have hm := hABC (Or.inl hx)
    exact c.isClosedEmbedding.injective.mem_set_image.mp hm
  have hB'I : B' ⊆ diskInterior n := by
    intro x hx
    have hm := hABC (Or.inr hx)
    exact c.isClosedEmbedding.injective.mem_set_image.mp hm
  have hA'B' : Disjoint A' B' := hAB.preimage c.map
  have hB' : IsCompact B' :=
    (hB.isClosed.preimage c.isClosedEmbedding.continuous).isCompact
  have hneA' : A'.Nonempty := by
    obtain ⟨a, ha⟩ := hneA
    obtain ⟨x, -, hx⟩ := hABC (Or.inl ha)
    exact ⟨x, show c.map x ∈ A from hx.symm ▸ ha⟩
  have hneB' : B'.Nonempty := by
    obtain ⟨b, hb⟩ := hneB
    obtain ⟨x, -, hx⟩ := hABC (Or.inr hb)
    exact ⟨x, show c.map x ∈ B from hx.symm ▸ hb⟩
  have hFproper : range F ≠ univ := by
    obtain ⟨q, hq⟩ := Set.nonempty_compl.mpr hcproper
    have hqA : q ∉ A := fun h => hq (c.interiorSet_subset_carrier (hABC (Or.inl h)))
    have hqB : q ∉ B := fun h => hq (c.interiorSet_subset_carrier (hABC (Or.inr h)))
    intro hu
    have hqF : f q ∈ range F := hu ▸ mem_univ _
    obtain ⟨x, hx⟩ := hqF
    rcases (hfAB (c.map x) q).mp hx with heq | ⟨-, hqa⟩ | ⟨-, hqb⟩
    · exact hq ⟨x, heq⟩
    · exact hqA hqa
    · exact hqB hqb
  have hFI : IsOpen (F '' diskInterior n) := by
    change IsOpen ((f ∘ c.map) '' diskInterior n)
    rw [image_comp]
    apply isOpen_image_of_saturated hf c.isOpen_interior isOpen_univ
      (subset_univ _) (by rw [hfs.range_eq])
    intro x y hxy hx
    rcases (hfAB x y).mp hxy with rfl | ⟨-, hy⟩ | ⟨-, hy⟩
    · exact hx
    · exact hABC (Or.inl hy)
    · exact hABC (Or.inr hy)
  obtain ⟨a, ha⟩ := hneA'
  have haavoid : F a ∉ F '' B' := by
    rintro ⟨b, hb, hba⟩
    rcases (hFA'B' b a).mp hba with rfl | ⟨hbA, -⟩ | ⟨-, haB⟩
    · exact disjoint_left.mp hA'B' ha hb
    · exact disjoint_left.mp hA'B' hbA hb
    · exact disjoint_left.mp hA'B' ha haB
  let U := F '' diskInterior n \ F '' B'
  have hU : IsOpen U := hFI.sdiff (hB'.image hF).isClosed
  have haU : F a ∈ U := ⟨⟨a, hA'I ha, rfl⟩, haavoid⟩
  obtain ⟨h, hmove, V, hV, haV, hfix⟩ := exists_sphere_compression
    (isCompact_range hF) hFproper (mem_range_self a) hU haU
  have hAV : F '' A' ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    have heq : F x = F a := (hFA'B' x a).mpr (Or.inr (Or.inl ⟨hx, ha⟩))
    rwa [heq]
  have hmoveI : h '' range F ⊆ F '' diskInterior n := fun x hx => (hmove hx).1
  have havoid : Disjoint (h '' range F) (F '' B') :=
    disjoint_left.mpr (fun x hx hxb => (hmove hx).2 hxb)
  obtain ⟨g, hg, hgB, hgf, -, -, -, hgrange⟩ := exists_continuous_restoreFirstFiber
    hF hFA'B' hA'B' h hV hAV hfix (hmoveI.trans (image_subset_range _ _)) havoid
  have hsatI : F ⁻¹' (F '' diskInterior n) = diskInterior n :=
    preimage_image_eq_of_two_fibers hFA'B' hA'I hB'I
  have hgIeq : g '' diskInterior n = F ⁻¹' (h '' (F '' diskInterior n)) :=
    image_of_restored_range_two hFA'B' hA'I hB'I h hgf hgrange
  have hgI : IsOpen (g '' diskInterior n) := by
    rw [hgIeq]
    exact (h.isOpenMap _ hFI).preimage hF
  have hgrangeI : range g ⊆ diskInterior n := by
    intro x hx
    rw [hgrange] at hx
    have : x ∈ F ⁻¹' (F '' diskInterior n) := hmoveI hx
    rwa [hsatI] at this
  let G := c.map ∘ g
  have hG : Continuous G := c.isClosedEmbedding.continuous.comp hg
  have hGB : collapsesExactly G B' := hgB.comp_injective c.isClosedEmbedding.injective
  have hGproper : range G ≠ univ := by
    intro heq
    apply hcproper
    apply eq_univ_of_univ_subset
    intro x hx
    obtain ⟨y, rfl⟩ : x ∈ range G := heq ▸ hx
    exact ⟨g y, rfl⟩
  have hGI : IsOpen (G '' diskInterior n) := by
    change IsOpen ((c.map ∘ g) '' diskInterior n)
    rw [image_comp]
    exact c.isOpen_image_of_subset_interior hgI
      ((image_subset_range _ _).trans hgrangeI)
  have hcell := c.isCellular_image_of_collapsesExactly_sphere hG hGB hB' hneB' hB'I hGproper hGI
  have hBeq : c.map '' B' = B := image_preimage_eq_of_subset (fun x hx =>
    c.interiorSet_subset_carrier (hABC (Or.inr hx)))
  rwa [hBeq] at hcell

theorem isCellular_two_fibers (hf : Continuous f) (hfs : Function.Surjective f)
    (hfAB : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hAB : Disjoint A B) (hproper : A ∪ B ≠ univ) :
    isCellular n A ∧ isCellular n B := by
  refine ⟨?_, isCellular_second_fiber_of_two_fibers hf hfs hfAB hA hB hneA hneB hAB hproper⟩
  apply isCellular_second_fiber_of_two_fibers hf hfs
    (fun x y => (hfAB x y).trans (by tauto)) hB hA hneB hneA hAB.symm
  rwa [union_comm]

end

end DifferentialGeometry.Topology
