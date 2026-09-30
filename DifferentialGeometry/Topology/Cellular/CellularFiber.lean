import DifferentialGeometry.Topology.Cellular.Cellular
import DifferentialGeometry.Topology.Cellular.RestoreFiber
import DifferentialGeometry.Topology.Schoenflies.SaturatedImage
import DifferentialGeometry.Topology.Schoenflies.SphereCompression

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

section Restore

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : Disk n → Y} {K U : Set (Disk n)}

theorem exists_embeddedClosedCell_of_restored_compression (hf : Continuous f)
    (hfK : collapsesExactly f K) (hKI : K ⊆ diskInterior n)
    (hfI : IsOpen (f '' diskInterior n)) (hKU : K ⊆ U)
    (h : Y ≃ₜ Y) (hmove : h '' range f ⊆ f '' U)
    {V : Set Y} (hV : IsOpen V) (hKV : f '' K ⊆ V)
    (hfix : ∀ y ∈ V, h y = y) :
    ∃ c : EmbeddedClosedCell n (Disk n), K ⊆ c.interiorSet ∧ c.carrier ⊆ U := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  obtain ⟨g, hg, hgf, hgfix, -, hgrange⟩ := exists_closedEmbedding_restoreFiber hf hfK h
    hV hKV hfix (hmove.trans (image_subset_range f U))
  have hI : g '' diskInterior n = f ⁻¹' (h '' (f '' diskInterior n)) :=
    image_of_restored_range hfK hKI h hgf hgrange
  let c : EmbeddedClosedCell n (Disk n) := {
    map := g
    isClosedEmbedding := hg
    isOpen_interior := by rw [hI]; exact (h.isOpenMap _ hfI).preimage hf }
  refine ⟨c, ?_, ?_⟩
  · intro x hx
    exact ⟨x, hKI hx, hgfix x (hKV ⟨x, hx, rfl⟩)⟩
  · intro x hx
    have hx' : f x ∈ h '' range f := by
      change x ∈ range g at hx
      rwa [hgrange] at hx
    have : x ∈ f ⁻¹' (f '' U) := hmove hx'
    rwa [hfK.preimage_image_eq_of_subset hKU] at this

end Restore

namespace EmbeddedClosedCell

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem isOpen_image_of_subset_interior (c : EmbeddedClosedCell n X) {U : Set (Disk n)}
    (hU : IsOpen U) (hUI : U ⊆ diskInterior n) : IsOpen (c.map '' U) := by
  obtain ⟨V, hV, heq⟩ := c.isClosedEmbedding.isEmbedding.isInducing.image_eq_isOpen_inter_range hU
  have hsub : c.map '' U ⊆ c.interiorSet := image_mono hUI
  have himage : c.map '' U = V ∩ c.interiorSet := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨(heq ▸ hx).1, hsub hx⟩
    · intro x hx
      rw [heq]
      exact ⟨hx.1, c.interiorSet_subset_carrier hx.2⟩
  rw [himage]
  exact hV.inter c.isOpen_interior

def nest (c : EmbeddedClosedCell n X) (d : EmbeddedClosedCell n (Disk n))
    (hd : d.carrier ⊆ diskInterior n) : EmbeddedClosedCell n X where
  map := c.map ∘ d.map
  isClosedEmbedding := c.isClosedEmbedding.comp d.isClosedEmbedding
  isOpen_interior := by
    rw [image_comp]
    exact c.isOpen_image_of_subset_interior d.isOpen_interior
      (d.interiorSet_subset_carrier.trans hd)

@[simp]
theorem nest_carrier (c : EmbeddedClosedCell n X) (d : EmbeddedClosedCell n (Disk n))
    (hd : d.carrier ⊆ diskInterior n) : (c.nest d hd).carrier = c.map '' d.carrier :=
  range_comp c.map d.map

@[simp]
theorem nest_interiorSet (c : EmbeddedClosedCell n X) (d : EmbeddedClosedCell n (Disk n))
    (hd : d.carrier ⊆ diskInterior n) : (c.nest d hd).interiorSet = c.map '' d.interiorSet :=
  image_comp c.map d.map (diskInterior n)

end EmbeddedClosedCell

section Sphere

variable {n : ℕ} {f : Disk n → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}
    {K : Set (Disk n)}

theorem exists_cell_neighborhood_of_collapsesExactly_sphere
    (hf : Continuous f) (hfK : collapsesExactly f K) (hKne : K.Nonempty)
    (hKI : K ⊆ diskInterior n) (hproper : range f ≠ univ)
    (hfI : IsOpen (f '' diskInterior n))
    (U : Set (Disk n)) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ c : EmbeddedClosedCell n (Disk n), K ⊆ c.interiorSet ∧
      c.carrier ⊆ U ∩ diskInterior n := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let W := U ∩ diskInterior n
  have hKW : K ⊆ W := subset_inter hKU hKI
  have hW : IsOpen W := hU.inter (isOpen_diskInterior n)
  have hfW : IsOpen (f '' W) := isOpen_image_of_saturated hf hW hfI
    (image_mono inter_subset_right) (image_subset_range _ _) (by
      intro x y hxy hx
      rcases (hfK x y).mp hxy with rfl | ⟨-, hy⟩
      · exact hx
      · exact hKW hy)
  obtain ⟨x, hx⟩ := hKne
  obtain ⟨h, hmove, V, hV, haV, hfix⟩ := exists_sphere_compression
    (isCompact_range hf) hproper (mem_range_self x) hfW ⟨x, hKW hx, rfl⟩
  have hKV : f '' K ⊆ V := by
    rintro y ⟨z, hz, rfl⟩
    have heq : f z = f x := (hfK z x).mpr (Or.inr ⟨hz, hx⟩)
    rwa [heq]
  exact exists_embeddedClosedCell_of_restored_compression hf hfK hKI hfI hKW h hmove hV hKV hfix

theorem isCellular_of_collapsesExactly_sphere
    (hf : Continuous f) (hfK : collapsesExactly f K) (hK : IsCompact K)
    (hKne : K.Nonempty) (hKI : K ⊆ diskInterior n) (hproper : range f ≠ univ)
    (hfI : IsOpen (f '' diskInterior n)) : isCellular n K := by
  apply isCellular_of_cell_neighborhoods hK.isClosed hKne
  intro U hU hKU
  obtain ⟨c, hKc, hcU⟩ := exists_cell_neighborhood_of_collapsesExactly_sphere
    hf hfK hKne hKI hproper hfI U hU hKU
  exact ⟨c, hKc, hcU.trans inter_subset_left⟩

theorem EmbeddedClosedCell.isCellular_image_of_collapsesExactly_sphere
    {X : Type*} [MetricSpace X] (c : EmbeddedClosedCell n X)
    (hf : Continuous f) (hfK : collapsesExactly f K) (hK : IsCompact K)
    (hKne : K.Nonempty) (hKI : K ⊆ diskInterior n) (hproper : range f ≠ univ)
    (hfI : IsOpen (f '' diskInterior n)) : isCellular n (c.map '' K) := by
  apply isCellular_of_cell_neighborhoods
    (hK.image c.isClosedEmbedding.continuous).isClosed (hKne.image c.map)
  intro U hU hKU
  have hKpre : K ⊆ c.map ⁻¹' U := fun x hx => hKU ⟨x, hx, rfl⟩
  obtain ⟨d, hKd, hd⟩ := exists_cell_neighborhood_of_collapsesExactly_sphere
    hf hfK hKne hKI hproper hfI (c.map ⁻¹' U)
    (hU.preimage c.isClosedEmbedding.continuous) hKpre
  refine ⟨c.nest d (hd.trans inter_subset_right), ?_, ?_⟩
  · rw [EmbeddedClosedCell.nest_interiorSet]
    exact image_mono hKd
  · rw [EmbeddedClosedCell.nest_carrier]
    rintro x ⟨y, hy, rfl⟩
    exact (hd hy).1

end Sphere

end DifferentialGeometry.Topology
