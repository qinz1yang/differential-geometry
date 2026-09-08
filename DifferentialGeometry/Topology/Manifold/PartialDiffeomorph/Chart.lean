import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

open scoped Manifold ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

noncomputable def extChartAt (n : WithTop ℕ∞) [IsManifold I n M] (x : M) :
    PartialDiffeomorph I 𝓘(𝕜, E) M E n where
  toPartialEquiv := _root_.extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [_root_.extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (n := n) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

@[simp]
theorem extChartAt_toPartialEquiv (n : WithTop ℕ∞) [IsManifold I n M] (x : M) :
    (extChartAt I n x).toPartialEquiv = _root_.extChartAt I x := rfl

end DifferentialGeometry.PartialDiffeomorph
