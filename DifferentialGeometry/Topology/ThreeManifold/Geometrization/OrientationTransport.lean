import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Statement
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLawInstances
import DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

def CompactCarrier.opposite (C : CompactCarrier.{u}) : CompactCarrier.{u} :=
  { C with orientation := C.orientation.opposite }

def CompactCarrier.Components.opposite {C : CompactCarrier.{u}} (D : C.Components) :
    C.opposite.Components where
  count := D.count
  count_pos := D.count_pos
  piece := D.piece
  closed := D.closed
  connected := D.connected
  disjoint := D.disjoint
  covers := D.covers
  interior_connected := D.interior_connected

def TorusGluing.opposite {C : CompactCarrier.{u}} (G : TorusGluing C) :
    TorusGluing C.opposite where
  count := G.count
  gluing := G.gluing
  leftParam := G.leftParam
  rightParam := G.rightParam
  matching := G.matching
  matching_eq := G.matching_eq
  torusOrientation := G.torusOrientation
  leftCollar := G.leftCollar
  rightCollar := G.rightCollar
  left_source := G.left_source
  right_source := G.right_source
  left_zero := G.left_zero
  right_zero := G.right_zero
  boundary_exhausted := G.boundary_exhausted

set_option backward.isDefEq.respectTransparency false in
def SmoothAssembly.opposite {C : CompactCarrier.{u}} {G : TorusGluing C}
    (A : SmoothAssembly G) : SmoothAssembly G.opposite := by
  let := A.charts
  let := A.smooth
  refine {
    charts := A.charts
    smooth := A.smooth
    orientation := A.orientation.opposite
    quotient_smooth := A.quotient_smooth
    quotient_oriented := by
      intro x
      obtain ⟨L, hL, ho⟩ := A.quotient_oriented x
      refine ⟨L, hL, ?_⟩
      change Orientation.map (Fin 3) L (-C.orientation.orientation x) =
        -A.orientation.orientation (G.quotientMap x)
      rw [Orientation.map_neg]
      exact congrArg Neg.neg ho
    boundary_reversing := by
      intro i t
      obtain ⟨L, R, hL, hR, ho⟩ := A.boundary_reversing i t
      refine ⟨L, R, hL, hR, ?_⟩
      change Orientation.map (Fin 3) L.symm
          (-C.orientation.orientation (G.leftCollar i (t, halfZero))) =
        -Orientation.map (Fin 3) R.symm
          (-C.orientation.orientation (G.rightCollar i (G.matching i t, halfZero)))
      rw [Orientation.map_neg, Orientation.map_neg, neg_neg]
      simpa only [neg_neg] using congrArg Neg.neg ho
    interiorImage := A.interiorImage
    interiorDiffeomorph := A.interiorDiffeomorph
    interior_map := A.interior_map
    seam := A.seam
    seam_source := A.seam_source
    seam_zero := A.seam_zero
    seam_positive := A.seam_positive
    seam_negative := A.seam_negative }

def GeometricDecomposition.opposite {P : ConnectedClosedOrientedManifold.{u} 3}
    (D : GeometricDecomposition P) : GeometricDecomposition P.opposite where
  carrier := D.carrier.opposite
  components := D.components.opposite
  boundary := D.boundary.opposite
  assembly := D.assembly.opposite
  reconstruction := ⟨D.reconstruction.val,
    Diffeomorph.preservesOrientation_opposite D.reconstruction.property⟩
  incompressible := D.incompressible
  leftPiece := D.leftPiece
  rightPiece := D.rightPiece
  left_owned := D.left_owned
  right_owned := D.right_owned
  geometry := D.geometry

theorem GeometricDecomposition.opposite_geometry
    {P : ConnectedClosedOrientedManifold.{u} 3} (D : GeometricDecomposition P) :
    D.opposite.geometry = D.geometry := rfl

theorem GeometricDecomposition.opposite_torus_maps
    {P : ConnectedClosedOrientedManifold.{u} 3} (D : GeometricDecomposition P)
    (i : Fin D.boundary.count) :
    D.opposite.assembly.torusInPrime D.opposite.reconstruction i =
      D.assembly.torusInPrime D.reconstruction i := rfl

def GeometrizationCertificate.opposite {M : ConnectedClosedOrientedManifold.{u} 3}
    (C : GeometrizationCertificate M) : GeometrizationCertificate M.opposite := by
  let L := C.primeData.factors
  let f : ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).opposite.toClosedOrientedManifold
      M.opposite.toClosedOrientedManifold :=
    ⟨C.primeData.reconstruction.val,
      Diffeomorph.preservesOrientation_opposite C.primeData.reconstruction.property⟩
  refine {
    primeData := {
      factors := L.map ConnectedClosedOrientedManifold.opposite
      factors_nonempty := by
        intro h
        have hlen := congrArg List.length h
        simp only [List.length_map, List.length_nil] at hlen
        exact C.primeData.factors_nonempty (List.length_eq_zero_iff.mp hlen)
      prime := ?_
      reconstruction := (finiteConnectedSum_opposite L).some.symm.trans f }
    geometricFactors := ?_ }
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
    exact C.primeData.prime Q hQ
  · intro i
    let j : Fin L.length := ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
    simpa only [List.get_eq_getElem, List.getElem_map] using (C.geometricFactors j).opposite

theorem GeometrizationCertificate.opposite_factor_count
    {M : ConnectedClosedOrientedManifold.{u} 3} (C : GeometrizationCertificate M) :
    C.opposite.primeData.factors.length = C.primeData.factors.length :=
  List.length_map _

theorem geometrizes_of_diffeomorph
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (f : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier) (h : Geometrizes M) :
    Geometrizes N := by
  rcases f.preservesOrientation_or_preservesOrientation_opposite
    M.orientation N.orientation with hf | hf
  · exact geometrizes_of_orientedDiffeomorph ⟨f, hf⟩ h
  · obtain ⟨C⟩ := h
    have hp : f.preservesOrientation M.orientation.opposite N.orientation := by
      simpa only [ManifoldOrientation.opposite_opposite] using
        Diffeomorph.preservesOrientation_opposite hf
    exact geometrizes_of_orientedDiffeomorph (M := M.opposite) (N := N) ⟨f, hp⟩ ⟨C.opposite⟩

end GC.Endpoint
