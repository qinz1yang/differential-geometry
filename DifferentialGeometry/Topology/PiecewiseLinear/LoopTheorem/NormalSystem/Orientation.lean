import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.OrientableCoverDescent
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem NormalSystem.isOrientableManifold_of_isSubdivision
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hsubdiv : IsSubdivision S.ambientComplex K) (hor : IsOrientable 3 K) :
    S.IsOrientableManifold := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  have hamb : IsCombinatorialManifoldWithBoundary 3 S.ambientComplex :=
    hK.of_isSubdivision hsubdiv
  exact IsOrientable.of_space_subset (derivedNeighborhood S.ambientComplex S.imageComplex)
    S.manifoldComplex S.manifold_space.subset (hamb.derivedNeighborhood S.imageComplex)
    S.isManifold (IsOrientable.derivedNeighborhood hamb (hor.subdivision hK hsubdiv))

end DifferentialGeometry.Topology.PiecewiseLinear
