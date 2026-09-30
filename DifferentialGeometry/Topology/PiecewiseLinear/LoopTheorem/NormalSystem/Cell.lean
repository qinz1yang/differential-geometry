import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryComponent.SurfaceNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace NormalSystem

open Classical in
noncomputable def boundaryComponent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : NormalSystem E) : Set E :=
  connectedComponentIn S.boundaryComplex.space (S.boundaryLoop 0 : E)

open Classical in
noncomputable def IsOrientableManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : NormalSystem E) : Prop := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  exact IsOrientable 3 S.manifoldComplex

open Classical in
structure NonsingularCell
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : NormalSystem E) where
  sourceComplex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))
  finite_source : sourceComplex.faces.Finite
  source_isPLBall : IsPLBall 2 sourceComplex.space
  vertexMap : EuclideanSpace ℝ (Fin 2) → E
  source_faces_map :
    ∀ s ∈ sourceComplex.faces, s.image vertexMap ∈ S.manifoldComplex.faces
  nonsingular : InjOn (simplicialMap sourceComplex vertexMap) sourceComplex.space
  boundaryLoop : freeLoop S.boundaryNeighborhoodSpace
  boundary_range :
    Set.range (fun θ => (boundaryLoop θ : E)) =
      simplicialMap sourceComplex vertexMap '' frontier sourceComplex.space
  connector : Path S.basepoint (boundaryLoop 0)
  loopClass_avoids_normal :
    ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass S.basepoint boundaryLoop connector) S.normalSubgroup

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
