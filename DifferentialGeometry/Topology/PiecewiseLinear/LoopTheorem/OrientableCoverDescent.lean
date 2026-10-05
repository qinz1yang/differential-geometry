import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.RelativeCoverDescent

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem NormalSystem.isOrientable_double_manifoldComplex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) (hor : S.IsOrientableManifold) :
    letI : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
    IsOrientable 3 (double 3 S.manifoldComplex) := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  exact IsOrientable.double S.manifoldComplex S.isManifold hor

end DifferentialGeometry.Topology.PiecewiseLinear
