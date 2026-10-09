import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Decomposition

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

theorem SmoothAssembly.Incompressible.toPiece
    {C : CompactCarrier.{u}} {G : TorusGluing C} {S : SmoothAssembly G}
    {P : ConnectedClosedOrientedManifold.{u} 3} {r : S.Reconstruction P}
    (h : S.Incompressible r) (i : Fin G.count)
    {Y : Type*} [TopologicalSpace Y] (port : C(Torus, Y)) (inclusion : C(Y, P.Carrier))
    (hmap : inclusion.comp port = S.torusInPrime r i) (x : Torus) :
    Function.Injective (FundamentalGroup.map port x) := by
  apply injective_inner_of_composite port inclusion x
  rw [hmap]
  exact h i x

def GeometricDecomposition.transport
    {M N : ConnectedClosedOrientedManifold.{u} 3} (D : GeometricDecomposition M)
    (e : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold N.toClosedOrientedManifold) :
    GeometricDecomposition N where
  carrier := D.carrier
  components := D.components
  boundary := D.boundary
  assembly := D.assembly
  reconstruction := D.reconstruction.trans e
  incompressible := by
    intro i x
    let f : C(M.Carrier, N.Carrier) := ⟨e.val, e.val.continuous⟩
    let b : C(N.Carrier, M.Carrier) := ⟨e.val.symm, e.val.symm.continuous⟩
    have hf : Function.Injective (FundamentalGroup.map f (D.assembly.torusInPrime D.reconstruction i x)) := by
      exact injective_fundamentalGroup_map_of_leftInverse f b e.val.symm_apply_apply _
    change Function.Injective (FundamentalGroup.map (f.comp (D.assembly.torusInPrime D.reconstruction i)) x)
    rw [fundamentalGroup_map_comp]
    exact hf.comp (D.incompressible i x)
  leftPiece := D.leftPiece
  rightPiece := D.rightPiece
  left_owned := D.left_owned
  right_owned := D.right_owned
  geometry := D.geometry

end GC.Endpoint
