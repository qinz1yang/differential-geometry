import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleHalfSpace

/-!
# FC42 packet G1: consumers on the certificate pieces

Lane ASM-CYC2. The interior / boundary criteria and the half-space normal form of
`AssemblyCycleHalfSpace.lean`, stated for the certificate's vertices and product disk handles at a
point of `W` (the form the no-third-piece arguments of packets G2/H1 consume):

* `Vertex.mem_interior_image_iff`: on `W.interior`, a point of a vertex image is an ambient interior
  point of it iff it is not in its model-boundary image;
* `EdgeHandle.endDisk_disjoint_interior`, `EdgeHandle.vertical_disjoint_interior`: the end disks
  and the vertical face of a handle contain no ambient interior point of the handle image;
* `Vertex.exists_entering`: the entering cone at a model-boundary-image point of a vertex, in the
  ambient chart at that point (the handle forms are `EdgeHandle.exists_entering_vertical` /
  `EdgeHandle.exists_entering_endDisk` of the main file).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsG1A_ASMCYC2 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothG1A_ASMCYC2 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {W : CompactCarrier.{u}}

/-- On `W.interior`, a point of a vertex image is an ambient interior point of the image iff it is
not in the model-boundary image. -/
theorem Vertex.mem_interior_image_iff {v : Vertex W} {x : W.Carrier} (hx : x ∈ v.image)
    (hxW : x ∈ W.interior) : x ∈ interior v.image ↔ x ∉ v.boundaryImage := by
  rw [Vertex.image_eq_range_piece] at hx ⊢
  obtain ⟨q, rfl⟩ := hx
  rw [PieceEmbedding.map_mem_interior_range_iff hxW]
  constructor
  · rintro hq ⟨q', hq', hqq'⟩
    rw [v.piece.injective hqq'] at hq'
    exact ((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint q).mp hq hq'
  · intro hq
    rw [(𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint]
    exact fun hb => hq ⟨q, hb, rfl⟩

/-- The model-boundary image of a vertex contains no ambient interior point of the vertex image
inside `W.interior`. -/
theorem Vertex.boundaryImage_inter_interior_subset (v : Vertex W) :
    v.boundaryImage ∩ interior v.image ⊆ (W.interior : Set W.Carrier)ᶜ := by
  rintro x ⟨hxb, hxi⟩ hxW
  have hx : x ∈ v.image := interior_subset hxi
  exact ((Vertex.mem_interior_image_iff hx hxW).mp hxi) hxb

/-- The end disks of a handle contain no ambient interior point of the handle image. -/
theorem EdgeHandle.endDisk_disjoint_interior (H : EdgeHandle W) (b : Bool) :
    Disjoint (H.endDisk b) (_root_.interior (range H.map)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩
  apply H.map_not_mem_interior_range
  rw [handle_isBoundaryPoint_iff]
  cases b <;> simp

/-- The vertical face of a handle contains no ambient interior point of the handle image. -/
theorem EdgeHandle.vertical_disjoint_interior (H : EdgeHandle W) :
    Disjoint H.vertical (_root_.interior (range H.map)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
  apply H.map_not_mem_interior_range
  rw [handle_isBoundaryPoint_iff]
  exact Or.inl hp

/-- **Entering cone at a boundary-image point of a vertex**, in the ambient chart at the point. -/
theorem Vertex.exists_entering {v : Vertex W} {x : W.Carrier} (hx : x ∈ v.boundaryImage) :
    ∃ κ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, κ ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 (extChartAt W.model x x),
        ε * ‖y - extChartAt W.model x x‖ < κ (y - extChartAt W.model x x) →
          (extChartAt W.model x).symm y ∈ interior v.image := by
  obtain ⟨q, hq, rfl⟩ := hx
  rw [Vertex.image_eq_range_piece]
  exact v.piece.toPieceFold.exists_entering hq

end GC.GraphManifold.Assembly
