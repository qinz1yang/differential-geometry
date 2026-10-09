import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorProducers
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.A08OfHNT_MYN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.A11OfHNT_MYN

/-!
# HNT consumer contracts

The conditional HNT wrappers are checked against the explicit original A08/A11 conclusions.
The removed admission declarations are not required to state or check these contracts.
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.MinimalSurface DifferentialGeometry.Analysis
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u

/-- A08：`hNT → (A08 的结论)`，结论显式写出（`hNT` 由 `_` 推断）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {cores : PersistentHyperbolicCores F (K + 4)} (M : PrescribedCuspMeridian cores) :=
  (exists_attained_leastExteriorDiskArea_of_hNT_MYN (F := F) M :
    _ → (∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀, ∀ T : ℝ, ∀ h : T₀ ≤ T,
      hasExteriorDiskMinimizersAfter F.observation M.exterior.region T
        (M.loopAfter T (h₀.trans h)) ∧
      ∀ t ∈ Ici T, 0 < exteriorDiskArea F.observation M.exterior.region T
        (M.loopAfter T (h₀.trans h)) t))

/-- A11：`hNT → (A11 的结论)`，前提与 A11 逐字相同。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime
        (L.decomposition j C).reconstruction s) x)) :=
  (exists_primitive_meridian_of_compressible_seam_of_hNT_MYN K hK δ hadm hdec L j hj C s x hcomp :
    _ → Nonempty (PrescribedCuspMeridian L.cores))

end GC.LongTime.CuspP1
