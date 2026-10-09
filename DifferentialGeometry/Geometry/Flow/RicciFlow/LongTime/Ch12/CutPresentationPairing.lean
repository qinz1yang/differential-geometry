import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationMapOrient
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensGluing

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)

theorem rmapK_leftCollar_S12 (i : Fin F.count) {y : Torus × EuclideanHalfSpace 1}
    (hy : y ∈ halfCollarSource) :
    rmapK_S12 F (sideCollar_S12 F i hL_C2a y) = F.collar i (y.1, -(y.2.val 0)) := by
  have h0 : 0 ≤ y.2.val 0 := y.2.2
  have hq : (y.1, sideParam_S12 (-1) (y.2.val 0)) ∈ signedCollarSource :=
    sideParam_mem_source_S12 hL_C2a y.1 h0 hy
  have hx : (sideCollar_S12 F i hL_C2a y).1 = F.collar i (y.1, sideParam_S12 (-1) (y.2.val 0)) :=
    sideCollar_val_S12 F i hL_C2a hy
  change rmap_S12 (sideCollar_S12 F i hL_C2a y) = _
  rw [rmap_collar_S12 i hq hx]
  have hneg : sideParam_S12 (-1) (y.2.val 0) < 0 := by
    have := half_le_psi_S12 h0
    simp only [sideParam_S12]; linarith
  rw [rhoHat_of_neg_S12 hneg]
  have : -(sideParam_S12 (-1) (y.2.val 0)) = psi_S12 (y.2.val 0) := by
    simp only [sideParam_S12]; ring
  rw [this, rho_psi_S12]

theorem rmapK_rightCollar_S12 (i : Fin F.count) {y : Torus × EuclideanHalfSpace 1}
    (hy : y ∈ halfCollarSource) :
    rmapK_S12 F (sideCollar_S12 F i hR_C2a y) = F.collar i (y.1, y.2.val 0) := by
  have h0 : 0 ≤ y.2.val 0 := y.2.2
  have hq : (y.1, sideParam_S12 1 (y.2.val 0)) ∈ signedCollarSource :=
    sideParam_mem_source_S12 hR_C2a y.1 h0 hy
  have hx : (sideCollar_S12 F i hR_C2a y).1 = F.collar i (y.1, sideParam_S12 1 (y.2.val 0)) :=
    sideCollar_val_S12 F i hR_C2a hy
  change rmap_S12 (sideCollar_S12 F i hR_C2a y) = _
  rw [rmap_collar_S12 i hq hx]
  have hpos : 0 ≤ sideParam_S12 1 (y.2.val 0) := by
    have := half_le_psi_S12 h0
    simp only [sideParam_S12]; linarith
  rw [rhoHat_of_nonneg_S12 hpos]
  have : sideParam_S12 1 (y.2.val 0) = psi_S12 (y.2.val 0) := by
    simp only [sideParam_S12]; ring
  change F.collar i (y.1, rho_S12 (sideParam_S12 1 (y.2.val 0))) = _
  rw [this, rho_psi_S12]

/-- **The torus pairing of the cut** (reversing proved from the stretch map). -/
def cutPairing_S12 : GC.GraphManifold.TorusPairing (cutCarrier_C2a F) where
  count := F.count
  gluing := (cutGluing_C2a F).gluing
  leftParam := (cutGluing_C2a F).leftParam
  rightParam := (cutGluing_C2a F).rightParam
  matching := (cutGluing_C2a F).matching
  matching_eq := (cutGluing_C2a F).matching_eq
  leftCollar := fun i => sideCollar_S12 F i hL_C2a
  rightCollar := fun i => sideCollar_S12 F i hR_C2a
  left_source := fun i => rfl
  right_source := fun i => rfl
  left_zero := fun i t => by
    rw [sideCollar_zero_S12]; rfl
  right_zero := fun i t => by
    rw [sideCollar_zero_S12]; rfl
  reversing := fun i =>
    GC.GraphManifold.reversesBoundaryOrientation_of_seam (contMDiff_rmapK_S12 F)
      (rmapK_mfderiv_bijective_S12 F) M.orientation (rmapK_oriented_S12 F)
      (l := sideCollar_S12 F i hL_C2a) (r := sideCollar_S12 F i hR_C2a)
      (sideCollar_source_S12 F i hL_C2a) (sideCollar_source_S12 F i hR_C2a)
      ((cutGluing_C2a F).matching i) (S := F.collar i) (F.source_eq i)
      (fun y hy => rmapK_leftCollar_S12 F i hy)
      (fun y hy => rmapK_rightCollar_S12 F i hy)

end GC.LongTime.Ch12
