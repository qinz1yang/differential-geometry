import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorProducers
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.A08OfHNT_MYN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.A11OfHNT_MYN

/-!
# S-MY-NT G3 consumer：wrapper 的结论与 A08 / A11 skeleton 的陈述 `type_of%` 对齐

本文件 import `CuspExteriorProducers`（A08、A11 的 skeleton admission 所在），所以**不登记**；
两个 wrapper（`A08OfHNT_MYN`、`A11OfHNT_MYN`）本身不 import 它，仍然不经 skeleton。
下面两个 `example` 把 wrapper 的"`hNT` → 结论"形状与 skeleton 声明在**同一组实参**下的类型
（`type_of%`）逐字对齐：结论完全一致，wrapper 只多一个前提 `hNT`（A08 另外不带 `hK δ hadm hdec`，
它们在 `_HC2` 路线里没有被用到）。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.MinimalSurface DifferentialGeometry.Analysis
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u

/-- A08：`hNT → (A08 的结论)`，结论用 skeleton 的 `type_of%` 给出（`hNT` 由 `_` 推断）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {cores : PersistentHyperbolicCores F (K + 4)} (M : PrescribedCuspMeridian cores) :=
  (exists_attained_leastExteriorDiskArea_of_hNT_MYN (F := F) M :
    _ → type_of% (exists_attained_leastExteriorDiskArea K hK δ hadm hdec M))

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
    _ → type_of% (exists_primitive_meridian_of_compressible_seam K hK δ hadm hdec L j hj C s x
      hcomp))

end GC.LongTime.CuspP1
