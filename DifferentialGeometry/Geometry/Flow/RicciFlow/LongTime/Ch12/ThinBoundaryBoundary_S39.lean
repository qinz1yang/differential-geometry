import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryPieceLift_S34
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryRightLift_S34
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationMain

/-!
# CH12-S39 G1: boundary of a non-core block of the real cut

For a block `j` of the cut presentation `(cutPresentation_S12 M F).toTorusDecomposition`
which owns no left torus `σ_i(·, -1/2)` (`hnoleft`), its boundary is exactly the union of the
right torus slices `σ_i(·, 1/2)` it owns; the slices of distinct `i` are disjoint.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- Boundary of an open piece = boundary of the ambient carrier intersected with the piece. -/
theorem mem_boundary_piece_S39 {C : CompactCarrier.{u}} {D : C.Components} {j : Fin D.count}
    {x : (componentCarrier C D j).Carrier} :
    x ∈ (componentCarrier C D j).model.boundary (componentCarrier C D j).Carrier ↔
      x.val ∈ C.model.boundary C.Carrier := by
  have h := C.model.boundary_open (u := D.piece j)
  exact (Set.ext_iff.mp h x)

section Cut

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)

/-- **G1 (generic).** Boundary of a block of the cut which owns no left torus. -/
theorem mem_boundary_block_iff_S39 {F : CollaredTorusFamily_C2a M.Carrier}
    {j : Fin (cutPresentation_S12 M F).toTorusDecomposition.components.count}
    (hnoleft : ∀ x : ((cutPresentation_S12 M F).toTorusDecomposition.component j).Carrier,
      ∀ (i : Fin F.count) (t : Torus), x.val.1 ≠ F.collar i (t, -1 / 2))
    {x : ((cutPresentation_S12 M F).toTorusDecomposition.component j).Carrier} :
    x ∈ ((cutPresentation_S12 M F).toTorusDecomposition.component j).model.boundary
        ((cutPresentation_S12 M F).toTorusDecomposition.component j).Carrier ↔
      ∃ (i : Fin F.count) (t : Torus), x.val.1 = F.collar i (t, 1 / 2) := by
  refine mem_boundary_piece_S39.trans ((cutIncl_boundary_iff_C2a F x.val).trans ?_)
  constructor
  · rintro ⟨i, ⟨t, ht⟩ | ⟨t, ht⟩⟩
    · exact ⟨i, t, ht⟩
    · exact absurd ht (hnoleft x i t)
  · rintro ⟨i, t, ht⟩
    exact ⟨i, Or.inl ⟨t, ht⟩⟩

/-- Distinct right tori are disjoint. -/
theorem right_torus_injective_S39 {i k : Fin F.count} {t t' : Torus}
    (h : F.collar i (t, 1 / 2) = F.collar k (t', 1 / 2)) : i = k := by
  by_contra hik
  have hs : ((t, (1 / 2 : ℝ)) : Torus × ℝ) ∈ (F.collar i).source := by
    rw [F.source_eq]; simp [signedCollarSource]; norm_num
  have hs' : ((t', (1 / 2 : ℝ)) : Torus × ℝ) ∈ (F.collar k).source := by
    rw [F.source_eq]; simp [signedCollarSource]; norm_num
  exact Set.disjoint_left.mp (F.disjoint hik) ((F.collar i).map_source hs)
    (h ▸ (F.collar k).map_source hs')

end Cut

end GC.LongTime.Ch12
