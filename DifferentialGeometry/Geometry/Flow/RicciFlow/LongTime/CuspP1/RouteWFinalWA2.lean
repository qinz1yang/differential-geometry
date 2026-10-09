import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWAssemblyWA10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Ims05HC2ClosedIM6

/-!
# Route W 主定理：零显式义务（O-W-ASSEMBLY-2 G_final，后缀 `_WA`）

`hasAttainedExteriorAreaObstructionAfter_of_routeW_final_WA` 的 binder 与
`LateDecomposition.lean` 的 `hasExteriorAreaObstructionAfter_of_producers` **逐字相同**
（`K hK δ hadm hdec L j hj C`，外审 R5 D-R5-16：端点声明不变、不新增假设），结论同为
`hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C)`。

证明 = G9 `hasAttainedExteriorAreaObstructionAfter_of_routeW_WA10`（`hadm` 取出 `H`）+ 最后一个叶子
⑥ `h6E` ⇐ O-W-IMS06 G16 `h6_of_HC2_closed_IM6`（S-W-STAB-2 G1/G4 逐盘 + IMS06 G9/G15）。

不经 `P2AdapterImported{Lemmas,Top,MorreyHC}`（镜像），不经四个 team skeleton admission
`exists_attained_leastExteriorDiskArea`（A08）、
`exists_local_upper_barrier_of_exteriorDiskArea`（A10）、
`exists_primitive_meridian_of_compressible_seam`（A11）、
`local_disk_comparisons_of_cusp_exterior`（A14）；
审计 `#print axioms` = `propext, Classical.choice, Quot.sound`（0 `sorryAx`）。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime

namespace GC.LongTime.CuspP1

universe u

/-- **Route W 主定理（零显式义务）**：`hasExteriorAreaObstructionAfter_of_producers` 的同一陈述，
sorry-free。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_routeW_final_WA
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) := by
  obtain ⟨H⟩ := hadm
  exact hasAttainedExteriorAreaObstructionAfter_of_routeW_WA10 K hK δ H hdec L j hj C
    fun M => h6_of_HC2_closed_IM6 M

/-- consumer：`.toObstruction`（`hasExteriorAreaObstructionAfter` 形，供 `incompressible` 方向）。 -/
theorem hasExteriorAreaObstructionAfter_of_routeW_final_WA
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier) :
    hasExteriorAreaObstructionAfter F (L.decomposition j C) :=
  (hasAttainedExteriorAreaObstructionAfter_of_routeW_final_WA K hK δ hadm hdec L j hj
    C).toObstruction

/-- 型对齐：G_final 与 `hasExteriorAreaObstructionAfter_of_producers` 的类型逐字相同（同一个 `∀`）。 -/
example : type_of% @hasAttainedExteriorAreaObstructionAfter_of_routeW_final_WA.{u} =
    ExteriorAreaObstructionStatement.{u} := rfl

end GC.LongTime.CuspP1
