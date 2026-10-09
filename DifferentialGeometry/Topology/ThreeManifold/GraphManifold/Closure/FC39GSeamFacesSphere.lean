import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeNeighbourhoods
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GVertexPortLayers
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersAdapted

/-!
# FC39 GROUP G (lane FC39-G-SF): the S³ regression of the joint seam–face layers

The general theorem `exists_seams_faces_GSF` applied to the wide S³ rows `sphereRowsW J` (the rows
of the non-vacuous strong certificate) with the GENERAL safe neighbourhoods
(`exists_sharedSafe_GSAFE`), the general vertex layer (`exists_vertexLayer_G1`) and port layer
(`exists_portLayer_G1`), for an arbitrary circle region. Non-vacuity: the S³ rows have exactly one
actual shared face, a sphere (`eq_sphereSharedFace`, `sphereSharedFace_shape`), so EVERY joint
seam–face output over these rows has exactly one sphere seam and no torus seam
(`sphere_sphereSeamCount_GSF`, `sphere_torusSeamCount_GSF`), and the general one exists
(`sphere_exists_seams_faces_GSF`): its sphere seam is the shared sphere `r = 1/2`
(`sphere_seam_zeroSlice_GSF`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

variable (J : JunctionsV2 sphereW (BoundaryTori.empty sphereW) sphereZeroDomains sphereCuspCores
  sphereSlimPieces sphereEdgeBundle sphereCircleBundle)

/-- The S³ rows have exactly one sphere-shaped shared face. -/
theorem sphere_nat_card_sphereShared_GSF : Nat.card (sphereRowsW J).SphereShared_GSF = 1 := by
  have : Unique (sphereRowsW J).SphereShared_GSF :=
    { default := ⟨sphereSharedFace, sphereSharedFace_shape⟩
      uniq := fun τ => Subtype.ext (eq_sphereSharedFace τ.1) }
  exact Nat.card_unique

/-- The S³ rows have no torus-shaped shared face. -/
theorem sphere_isEmpty_torusShared_GSF : IsEmpty (sphereRowsW J).TorusShared_GSF := by
  refine ⟨fun τ => ?_⟩
  have h := τ.2
  change sphereSlimPieces.endShape τ.1.1 = .torus at h
  rw [eq_sphereSharedFace τ.1, sphereSharedFace_shape] at h
  cases h

/-- **Regression.** Every joint seam–face output over the S³ rows has exactly one sphere seam. -/
theorem sphere_sphereSeamCount_GSF {V : VertexLayer sphereW}
    {vlink : VertexModelLink (sphereRowsW J) V} {O : PortLayer sphereW (BoundaryTori.empty sphereW) V}
    {circ : CircleRegion sphereW} {S : SeamLayer sphereW V circ}
    {F : FaceLayer sphereW (BoundaryTori.empty sphereW) V S O}
    {N : (sphereRowsW J).SharedFace → TopologicalSpace.Opens sphereW.Carrier}
    (L : SeamFacesLink (sphereRowsW J) V vlink O S F N) : S.sphereSeamCount = 1 := by
  rw [← Nat.card_fin S.sphereSeamCount, Nat.card_congr L.sphereEquiv]
  exact sphere_nat_card_sphereShared_GSF J

/-- **Regression.** Every joint seam–face output over the S³ rows has no torus seam. -/
theorem sphere_torusSeamCount_GSF {V : VertexLayer sphereW}
    {vlink : VertexModelLink (sphereRowsW J) V} {O : PortLayer sphereW (BoundaryTori.empty sphereW) V}
    {circ : CircleRegion sphereW} {S : SeamLayer sphereW V circ}
    {F : FaceLayer sphereW (BoundaryTori.empty sphereW) V S O}
    {N : (sphereRowsW J).SharedFace → TopologicalSpace.Opens sphereW.Carrier}
    (L : SeamFacesLink (sphereRowsW J) V vlink O S F N) : S.torusSeamCount = 0 := by
  have := sphere_isEmpty_torusShared_GSF J
  rw [← Nat.card_fin S.torusSeamCount, Nat.card_congr L.torusEquiv]
  exact Nat.card_of_isEmpty

/-- **Consumer.** The general seams and faces of the S³ rows, over the general safe
neighbourhoods, vertex layer and port layer: one sphere seam, no torus seam. -/
theorem sphere_exists_seams_faces_GSF (circ : CircleRegion sphereW) :
    ∃ (N : (sphereRowsW J).SharedFace → TopologicalSpace.Opens sphereW.Carrier)
      (_ : SharedSafe (sphereRowsW J) N) (V : VertexLayer sphereW)
      (vlink : VertexModelLink (sphereRowsW J) V)
      (O : PortLayer sphereW (BoundaryTori.empty sphereW) V) (_ : PortModelLink _ vlink O)
      (S : SeamLayer sphereW V circ) (F : FaceLayer sphereW (BoundaryTori.empty sphereW) V S O),
      Nonempty (SeamFacesLink (sphereRowsW J) V vlink O S F N) ∧ S.sphereSeamCount = 1 ∧
        S.torusSeamCount = 0 := by
  obtain ⟨N, hN⟩ := exists_sharedSafe_GSAFE (sphereRowsW J)
  obtain ⟨V, ⟨vlink⟩⟩ := exists_vertexLayer_G1 (sphereRowsW J)
  obtain ⟨O, olink⟩ := exists_portLayer_G1 (sphereRowsW J) V vlink
  obtain ⟨S, F, ⟨L⟩⟩ := exists_seams_faces_GSF (sphereRowsW J) V vlink circ O olink N hN
  exact ⟨N, hN, V, vlink, O, olink, S, F, ⟨L⟩, sphere_sphereSeamCount_GSF J L,
    sphere_torusSeamCount_GSF J L⟩

/-- **Regression.** The zero slice of the sphere seam of any joint output over the S³ rows is the
shared sphere `r = 1/2` (height `-15/17`). -/
theorem sphere_seam_zeroSlice_GSF {V : VertexLayer sphereW}
    {vlink : VertexModelLink (sphereRowsW J) V} {O : PortLayer sphereW (BoundaryTori.empty sphereW) V}
    {circ : CircleRegion sphereW} {S : SeamLayer sphereW V circ}
    {F : FaceLayer sphereW (BoundaryTori.empty sphereW) V S O}
    {N : (sphereRowsW J).SharedFace → TopologicalSpace.Opens sphereW.Carrier}
    (L : SeamFacesLink (sphereRowsW J) V vlink O S F N) (c : Fin S.sphereSeamCount) :
    (range fun z => (S.sphereSeam c).collar (z, 0)) = {x | sphereHeight x = -15 / 17} := by
  rw [L.sphere_slim c]
  change sphereSlimPieces.endSet (L.sphereEquiv c).1.1 = _
  rw [eq_sphereSharedFace (L.sphereEquiv c).1]
  exact sphereSharedFace_set

end GC.GraphManifold.Assembly.FC39P0
