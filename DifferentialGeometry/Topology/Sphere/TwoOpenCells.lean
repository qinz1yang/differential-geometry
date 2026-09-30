import DifferentialGeometry.Topology.Schoenflies.OpenEmbeddingCollapse
import DifferentialGeometry.Topology.Cellular.CellNeighborhood
import DifferentialGeometry.Topology.Cellular.CellularFiber
import DifferentialGeometry.Topology.Cellular.CellularCollapse
import Mathlib.Topology.Compactification.OnePoint.Sphere

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

theorem nonempty_homeomorph_sphere_of_two_open_cells {n : ℕ} (hn : 1 ≤ n)
    {X : Type*} [MetricSpace X] [CompactSpace X]
    {φ₀ φ₁ : EuclideanSpace ℝ (Fin n) → X}
    (hφ₀ : IsOpenEmbedding φ₀) (hφ₁ : IsOpenEmbedding φ₁)
    (hcover : range φ₀ ∪ range φ₁ = univ) :
    Nonempty (X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hproper {φ : EuclideanSpace ℝ (Fin n) → X} (hφ : IsOpenEmbedding φ) :
      range φ ≠ univ := by
    intro heq
    apply noncompact_univ (EuclideanSpace ℝ (Fin n))
    apply hφ.isEmbedding.isCompact_iff.mpr
    rw [image_univ, heq]
    exact isCompact_univ
  obtain ⟨f₀, hfs₀, hfK₀, -, -⟩ := exists_collapse_of_openEmbedding hφ₀ (hproper hφ₀)
  let H : OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let f := H ∘ f₀
  have hf : Continuous f := H.continuous.comp f₀.continuous
  have hfs : Function.Surjective f := H.surjective.comp hfs₀
  let K := (range φ₀)ᶜ
  have hfK : collapsesExactly f K := hfK₀.comp_injective H.injective
  have hK : IsCompact K := hφ₀.isOpen_range.isClosed_compl.isCompact
  have hKne : K.Nonempty := nonempty_compl.mpr (hproper hφ₀)
  have hKφ₁ : K ⊆ range φ₁ := by
    intro x hx
    have hxcover : x ∈ range φ₀ ∪ range φ₁ := hcover ▸ mem_univ x
    exact hxcover.resolve_left hx
  obtain ⟨c, hKc, hcφ₁⟩ := exists_embeddedClosedCell_in_openEmbedding hφ₁ hK hKφ₁
  let K' := c.map ⁻¹' K
  let F := f ∘ c.map
  have hF : Continuous F := hf.comp c.isClosedEmbedding.continuous
  have hFK : collapsesExactly F K' := by
    intro x y
    simpa only [F, K', Function.comp_apply, mem_preimage,
      c.isClosedEmbedding.injective.eq_iff] using hfK (c.map x) (c.map y)
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hK' : IsCompact K' := (hK.isClosed.preimage c.isClosedEmbedding.continuous).isCompact
  have hK'ne : K'.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨y, hy⟩ := c.interiorSet_subset_carrier (hKc hx)
    refine ⟨y, ?_⟩
    change c.map y ∈ K
    rwa [hy]
  have hK'I : K' ⊆ diskInterior n := by
    intro x hx
    exact c.isClosedEmbedding.injective.mem_set_image.mp (hKc hx)
  have hFproper : range F ≠ univ := by
    intro hall
    obtain ⟨x, hx⟩ := nonempty_compl.mpr (hproper hφ₁)
    obtain ⟨y, hy⟩ : f x ∈ range F := hall ▸ mem_univ _
    rcases (hfK (c.map y) x).mp hy with heq | ⟨-, hxK⟩
    · exact hx (heq ▸ hcφ₁ (mem_range_self y))
    · exact hx (hKφ₁ hxK)
  have hFI : IsOpen (F '' diskInterior n) := by
    change IsOpen ((f ∘ c.map) '' diskInterior n)
    rw [image_comp]
    apply isOpen_image_of_saturated hf c.isOpen_interior isOpen_univ (subset_univ _)
      (by rw [hfs.range_eq])
    intro x y hxy hx
    rcases (hfK x y).mp hxy with rfl | ⟨-, hy⟩
    · exact hx
    · exact hKc hy
  have hcell := c.isCellular_image_of_collapsesExactly_sphere
    hF hFK hK' hK'ne hK'I hFproper hFI
  have hKimage : c.map '' K' = K :=
    image_preimage_eq_of_subset (hKc.trans c.interiorSet_subset_carrier)
  rw [hKimage] at hcell
  exact hcell.nonempty_homeomorph_of_collapsesExactly hf hfs hfK

end DifferentialGeometry.Topology
