import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels

/-!
Intrinsic boundary of an actual circle fibration, including open total-space domains.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.CircleFibration

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
    (F : CircleFibration C U)

theorem interiorPoint_iff_projection (x : U) :
    C.model.IsInteriorPoint x.val ↔
      (SurfaceModel.model F.base.kind).IsInteriorPoint (F.projection x) := by
  let b := F.projection x
  let V := F.neighborhood b
  let y : TopologicalSpace.Opens.comap F.projection V := ⟨x, F.mem_neighborhood b⟩
  let d := F.trivialization b
  have ht := (d.isLocalDiffeomorph y).isInteriorPoint_iff
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hy : C.model.IsInteriorPoint y ↔ C.model.IsInteriorPoint x.val :=
    C.model.isInteriorPoint_iff_isInteriorPoint_val.trans
      C.model.isInteriorPoint_iff_isInteriorPoint_val
  rw [← hy, ht]
  change d y ∈ ((SurfaceModel.model F.base.kind).prod (𝓡 1)).interior (V × Circle) ↔ _
  rw [ModelWithCorners.interior_prod]
  change (SurfaceModel.model F.base.kind).IsInteriorPoint (d y).1 ∧
    (𝓡 1).IsInteriorPoint (d y).2 ↔ _
  rw [and_iff_left (BoundarylessManifold.isInteriorPoint (I := 𝓡 1))]
  rw [(SurfaceModel.model F.base.kind).isInteriorPoint_iff_isInteriorPoint_val]
  exact (F.projection_trivialization b y) ▸ Iff.rfl

theorem boundaryPoint_iff_projection (x : U) :
    C.model.IsBoundaryPoint x.val ↔
      (SurfaceModel.model F.base.kind).IsBoundaryPoint (F.projection x) := by
  rw [C.model.isBoundaryPoint_iff_not_isInteriorPoint,
    (SurfaceModel.model F.base.kind).isBoundaryPoint_iff_not_isInteriorPoint,
    F.interiorPoint_iff_projection]

theorem boundary_preimage :
    C.model.boundary C.Carrier ∩ U =
      Subtype.val ''
        (F.projection ⁻¹' (SurfaceModel.model F.base.kind).boundary F.base.Carrier) := by
  ext x
  constructor
  · rintro ⟨hx, hu⟩
    exact ⟨⟨x, hu⟩, (F.boundaryPoint_iff_projection ⟨x, hu⟩).mp hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(F.boundaryPoint_iff_projection y).mpr hy, y.property⟩

end GC.GraphManifold.CircleFibration
