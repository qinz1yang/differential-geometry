import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalSystem.Cell
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialComplexity.Factorization
import Mathlib.Topology.Covering.Basic

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace NormalSystem

open Classical in
structure DoubleCoverDiagram
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : NormalSystem E) (T : NormalSystem F) where
  projection : F → E
  projection_mapsTo : MapsTo projection T.ambientComplex.space S.manifoldComplex.space
  isCoveringMap : IsCoveringMap
    (projection_mapsTo.restrict projection T.ambientComplex.space S.manifoldComplex.space)
  fiber_card : ∀ x,
    ((projection_mapsTo.restrict projection T.ambientComplex.space S.manifoldComplex.space)
      ⁻¹' {x}).encard = 2
  isPiecewiseAffineOn_projection : IsPiecewiseAffineOn projection T.ambientComplex.space
  sourceComplex_eq : T.sourceComplex = S.sourceComplex
  source_lift : EqOn (projection ∘ T.singularMap) S.singularMap S.sourceComplex.space
  boundaryMap : C(T.boundaryNeighborhoodSpace, S.boundaryNeighborhoodSpace)
  boundaryMap_eq : ∀ x, (boundaryMap x : E) = projection (x : F)
  basepoint_eq : boundaryMap T.basepoint = S.basepoint
  normalSubgroup_eq : T.normalSubgroup =
    S.normalSubgroup.comap (FundamentalGroup.mapOfEq boundaryMap basepoint_eq)

open Classical in
structure DoubleCoverReduction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (S : NormalSystem E)
    (T : NormalSystem (EuclideanSpace ℝ (Fin N))) extends DoubleCoverDiagram S T where
  complexity_lt : T.complexity < S.complexity

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
