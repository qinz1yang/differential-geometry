import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance scalarZeroTopology : TopologicalSpace F.M := F.topology
local instance scalarZeroCharted : ChartedSpace H F.M := F.charted
local instance scalarZeroSmooth : IsManifold I ∞ F.M := F.smooth

theorem scalar_slice_zero_of_nonnegative_slab
    (hconnected : ConnectedSpace F.M) {a b t : ℝ}
    (hat : a < t) (htb : t < b) (hregular : Set.Icc a b ⊆ D.regular)
    (hnonnegative : ∀ s ∈ Set.Icc a b, ∀ y : F.M, 0 ≤ F.S.scalar s y)
    (x : F.M) (hzero : F.S.scalar t x = 0) :
    ∀ y : F.M, F.S.scalar t y = 0 := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
