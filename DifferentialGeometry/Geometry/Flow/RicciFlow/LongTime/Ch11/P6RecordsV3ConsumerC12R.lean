import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRecordsV3C12R
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeCoreExclusionC11SP

set_option autoImplicit false

/-!
# records v3 的 consumer（CH12 C12-1 / C12-2，后缀 `_C12R`）

`exists_records_of_prepared_chain_v3_C12R` 的 radial 合取项喂 `P6NativeCoreExclusionC11SP` 的
`window_ne_of_regularCrossing_of_radial_C11SP`（CE ⇐ radial）：同一批 `records` 同时满足
canonical / linked / radial 与 core exclusion。

注意量词形状：`native_trace_window_of_CC_CE_C11SP` 的 `hCE` binder 对 *任意* `records`（只带
`hasCanonicalWindow`）量化，而 radial 只对 producer 选出的这一批 records 成立；因此这里的 CE
结论按 "radial 作为前件" 的形状给出（`hCE_of_radial_C12R`），并与 v3 的存在性合取在一起。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch11

universe u

/-- CE 以 radial 为前件的形状（`hCE` 的 radial 版）。 -/
theorem hCE_of_radial_C12R {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (params : CutoffParameters)
    (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
      GeometricCutoffRecord (F.tower.history n).toHistory e params)
    (hrad : ∀ n e b, ((records n e).static b).witness.HasRadialCoordinates) :
    ∀ (n : ℕ) (e : Fin (F.tower.history n).eventCount)
      (pm : ((F.tower.history n).toHistory.stage e.castSucc).Carrier)
      (pp : ((F.tower.history n).toHistory.stage e.succ).Carrier),
      ((F.tower.history n).toHistory.event e).RegularCrossing pm pp →
      ∀ (b : ((F.tower.history n).toHistory.event e).RetainedBoundaryIndex)
        (z : standardCapWindow params.modelRadius),
        ‖z.val‖ ≤ StandardCap.transitionEnd → ((records n e).static b).window z ≠ pp :=
  fun n e _ _ hcross b z hz =>
    window_ne_of_regularCrossing_of_radial_C11SP _ ((records n e).static b) (hrad n e b) z hz
      hcross

/-- **consumer**：v3 的同一批 records 同时带 canonical / linked / radial，并满足 core
exclusion（CE ⇐ radial，来自该批 records 自己的 radial 合取项）。 -/
theorem exists_records_v3_with_CE_C12R
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) :
    ∃ (params : CutoffParameters)
      (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory e params),
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) ∧
      (∀ n e b, ((records n e).static b).hasLinkedCanonicalWindow_C12X) ∧
      (∀ n e b, ((records n e).static b).witness.HasRadialCoordinates) ∧
      ∀ (n : ℕ) (e : Fin (F.tower.history n).eventCount)
        (pm : ((F.tower.history n).toHistory.stage e.castSucc).Carrier)
        (pp : ((F.tower.history n).toHistory.stage e.succ).Carrier),
        ((F.tower.history n).toHistory.event e).RegularCrossing pm pp →
        ∀ (b : ((F.tower.history n).toHistory.event e).RetainedBoundaryIndex)
          (z : standardCapWindow params.modelRadius),
          ‖z.val‖ ≤ StandardCap.transitionEnd → ((records n e).static b).window z ≠ pp := by
  obtain ⟨params, records, -, -, -, -, hcan, hlink, hrad, -, -, -⟩ :=
    exists_records_of_prepared_chain_v3_C12R S F hTower q hdiag
  exact ⟨params, records, hcan, hlink, hrad, hCE_of_radial_C12R F params records hrad⟩

end GC.LongTime.Ch11

end
