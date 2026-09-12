import DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import DifferentialGeometry.Topology.Manifold.ChartedSpaceHomeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace AddCircle

instance instChartedSpaceUnitAddCircle :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle (1 : ℝ)) :=
  (homeomorphCircle (T := (1 : ℝ)) (by norm_num)).symm.chartedSpace

instance instIsManifoldUnitAddCircle : IsManifold (𝓡 1) ∞ (AddCircle (1 : ℝ)) := by
  have hcirc : IsManifold (𝓡 1) ∞ Circle := IsManifold.of_le (le_top : (∞ : ℕ∞ω) ≤ ω)
  exact DifferentialGeometry.Manifold.isManifold_homeomorphChartedSpace (I := 𝓡 1) (n := ∞)
    (M := Circle) (f := (homeomorphCircle (T := (1 : ℝ)) (by norm_num)).symm)

noncomputable def euclideanSpaceFinOneContinuousLinearEquivReal :
    EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

noncomputable def euclideanSpaceFinOneHomeomorphReal : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
  euclideanSpaceFinOneContinuousLinearEquivReal.toHomeomorph

instance instChartedSpaceRealUnitAddCircle : ChartedSpace ℝ (AddCircle (1 : ℝ)) :=
  DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := AddCircle (1 : ℝ))
    euclideanSpaceFinOneHomeomorphReal

instance instIsManifoldRealUnitAddCircle : IsManifold 𝓘(ℝ, ℝ) ∞ (AddCircle (1 : ℝ)) :=
  DifferentialGeometry.Manifold.isManifold_transHomeomorph (I := 𝓡 1) (J := 𝓘(ℝ, ℝ))
    euclideanSpaceFinOneHomeomorphReal euclideanSpaceFinOneContinuousLinearEquivReal
    (fun _ => rfl)

end AddCircle

end
