import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialProviders
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecursion
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ClosedBirthConstantsStrongC12X

/-!
# S-CH11-FIX11 port of astra `PreparedSpatialExistence`（`PortC11P`）

来源：donor `PreparedSpatialExistence.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 主证明里 `have distanceProjectionh8 := @(distanceProjectionh6.2) budget distanceProjectionx7`
  （`@( … )` 本树 parser 报 "unexpected syntax"，其后的 "No goals" 是级联）→ 去掉 `@( )`，直接
  `distanceProjectionh6.2 budget distanceProjectionx7`（该处无隐式实参需显式化）。

原路径 `PreparedSpatialExistence` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open scoped NNReal

namespace GC.GeneralFlow
universe u

/-- Genuine prepared spatial chains from arbitrary original initial data. The
uniform constants precede all data. One original prepared base is retained for
any positive online accuracy budget evaluated on the chosen future class/radius. -/
theorem exists_prepared_spatial_chains_from_initial_with_distance_scalars :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    C.epsilon ≤ DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.εStrong_C12X.{u} ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase C P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧ base.radius ≤ 1 ∧
      base.DistanceData Cdist ∧
      ∀ (budget : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) → ℝ → ℝ),
      (∀ n L future r, 0 < budget n L future r) →
    ∃ S : PreparedSpatialChain pBase C P g,
      S.state 0 = base ∧ (∀ n, (S.state n).DistanceData Cdist) ∧
      ∀ n, ∃ (future : ClosedBirthPreparedClass pBase C
          ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
          ((3 : ℝ) ^ (n + 1) -
            (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
        0 < r ∧ (S.state (n + 1)).radius = r ∧
        HEq (S.state (n + 1)).prepared future ∧ S.accuracy n ≤ budget n (S.state n) future r := by
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hεs, _, prepareClass, analytic, makeBase⟩ :=
    exists_closedBirthConstants_strong_C12X.{u} 1 1 one_pos one_pos
  refine ⟨Cdist, hCdist, C, hεs, ?_⟩
  intro P g
  obtain ⟨pBase, prepared, base, _, _, hfixed, hrc, _, _, hDistance, hS⟩ := makeBase P g
  rcases hS with ⟨hbase, _, _, _, _, _, _, _, _, _, hrbase, _, _⟩
  refine ⟨pBase, base, hbase, hrbase, hDistance, ?_⟩
  intro budget hbudget
  exact exists_prepared_spatial_chain_with_distance_scalars Cdist pBase C
    (by simpa only [hfixed, hrc] using prepareClass)
    analytic base hbase hDistance hrbase budget hbudget

/-- Forget only certificates from this same genuine chain construction. -/
theorem exists_prepared_spatial_chains_from_initial :
    ∃ C : ClosedBirthConstants,
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase C P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧ base.radius ≤ 1 ∧
      ∀ (budget : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) → ℝ → ℝ),
      (∀ n L future r, 0 < budget n L future r) →
    ∃ S : PreparedSpatialChain pBase C P g,
      S.state 0 = base ∧
      ∀ n, ∃ (future : ClosedBirthPreparedClass pBase C
          ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
          ((3 : ℝ) ^ (n + 1) -
            (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
        0 < r ∧ (S.state (n + 1)).radius = r ∧
        HEq (S.state (n + 1)).prepared future ∧ S.accuracy n ≤ budget n (S.state n) future r := by
  obtain ⟨_, _, distanceResult⟩ :=
    exists_prepared_spatial_chains_from_initial_with_distance_scalars.{u}
  obtain ⟨C, -, distanceProjectionh1⟩ := distanceResult
  refine ⟨C, ?_⟩
  intro P g
  have distanceProjectionh2 := @distanceProjectionh1 P g
  obtain ⟨pBase, base, distanceProjectionh3⟩ := distanceProjectionh2
  refine ⟨pBase, base, ?_⟩
  obtain ⟨distanceProjectionfield4, distanceProjectionfield5, distanceProjectionh6⟩ :=
    distanceProjectionh3
  refine ⟨distanceProjectionfield4, distanceProjectionfield5, ?_⟩
  intro budget distanceProjectionx7
  have distanceProjectionh8 := distanceProjectionh6.2 budget distanceProjectionx7
  obtain ⟨S, distanceProjectionh9⟩ := distanceProjectionh8
  refine ⟨S, ?_⟩
  obtain ⟨distanceProjectionfield10, distanceProjectionh11⟩ := distanceProjectionh9
  refine ⟨distanceProjectionfield10, ?_⟩
  exact (distanceProjectionh11.2)

end GC.GeneralFlow
