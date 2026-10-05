import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleThirdPiece

/-!
# FC42 packet G2: consumers on the certificate

Lane ASM-CYC2.

* `DecompositionCertificate.not_mem_vertex_of_mem_boundaryImage_two`: three distinct vertices
  never meet at a point of the model-boundary images of two of them (no third piece, with the
  half-space normal form of two vertex pieces and the germ of the third).
* `DecompositionCertificate.rimChart_target_inter_iUnion_vertex`: inside a rim chart target, the
  union of all vertex images is the rim's own vertex image (the full rim chart excludes the others).
* `DecompositionCertificate.region_trichotomy`: a point of the circle region is an ambient interior
  point of it, or the region enters there along a half-space (depth one), or the point lies on a
  rim circle inside its rim chart target (corner fibre).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsG2A_ASMCYC2 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothG2A_ASMCYC2 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **No three vertices at a boundary point.** A point of the model-boundary images of two distinct
vertices lies in no third vertex image. -/
theorem not_mem_vertex_of_mem_boundaryImage_two {k₁ k₂ k₃ : Fin D.vertexCount} (h12 : k₁ ≠ k₂)
    (h13 : k₁ ≠ k₃) (h23 : k₂ ≠ k₃) {x : W.Carrier} (hx1 : x ∈ (D.vertex k₁).boundaryImage)
    (hx2 : x ∈ (D.vertex k₂).boundaryImage) : x ∉ (D.vertex k₃).image := by
  intro hx3
  rw [Vertex.image_eq_range_piece] at hx3
  obtain ⟨q, rfl⟩ := hx3
  have hd13 : Disjoint (interior (D.vertex k₁).image)
      (interior (range (D.vertex k₃).piece.map)) := by
    rw [← Vertex.image_eq_range_piece]
    exact D.vertex_disjoint h13
  have hd23 : Disjoint (interior (D.vertex k₂).image)
      (interior (range (D.vertex k₃).piece.map)) := by
    rw [← Vertex.image_eq_range_piece]
    exact D.vertex_disjoint h23
  exact false_of_two_entering_and_piece finrank_euclideanSpace_fin (D.vertex k₃).piece.smooth
    (D.vertex k₃).piece.mfderiv_bijective q (Vertex.exists_entering hx1)
    (Vertex.exists_entering hx2) (D.vertex_disjoint h12) hd13 hd23

/-- Inside a rim chart target, the vertex images are the rim's own vertex image. -/
theorem rimChart_target_inter_iUnion_vertex (h : Fin D.handleCount) (b : Bool) :
    (D.rimChart h b).target ∩ ⋃ k, (D.vertex k).image =
      (D.rimChart h b).target ∩ (D.vertex (D.handleEnd h b)).image := by
  apply Subset.antisymm
  · rintro z ⟨hzT, hz⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    by_cases hke : k = D.handleEnd h b
    · exact ⟨hzT, hke ▸ hk⟩
    · exact (Set.disjoint_left.mp (D.disjoint_vertex_rimChart_target h b k hke) hk hzT).elim
  · rintro z ⟨hzT, hz⟩
    exact ⟨hzT, mem_iUnion.mpr ⟨_, hz⟩⟩

/-- **Region trichotomy.** A point of the circle region is an ambient interior point of it, or the
region enters there along a half-space, or the point lies on a rim circle inside its rim chart
target. -/
theorem region_trichotomy {x : W.Carrier} (hx : x ∈ D.circ.region) :
    x ∈ interior D.circ.region ∨
      (∃ κ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, κ ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
        ∀ᶠ y in 𝓝 (extChartAt W.model x x),
          ε * ‖y - extChartAt W.model x x‖ < κ (y - extChartAt W.model x x) →
            (extChartAt W.model x).symm y ∈ interior D.circ.region) ∨
      ∃ h b, x ∈ (fun z : ClosedCell 2 => (D.handle h).map (z, iccEnd b)) '' diskRim ∧
        x ∈ (D.rimChart h b).target := by
  obtain ⟨z, hz, rfl⟩ := hx
  rcases D.circ.depth_cases hz with h0 | ⟨l, hl, hother⟩ | ⟨k, hk⟩
  · exact Or.inl (D.circ.mem_interior_region_of_defining_neg z.2 h0)
  · exact Or.inr (Or.inl (D.circ.exists_entering z.2 hl hother))
  · obtain ⟨h, b, -, hrim, hT⟩ := D.exists_rimCircle_of_proj_eq_corner z.2 hk
    exact Or.inr (Or.inr ⟨h, b, hrim, hT⟩)

end DecompositionCertificate

end GC.GraphManifold.Assembly
