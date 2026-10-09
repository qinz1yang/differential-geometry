import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRecordsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.LinkedWindowsWireC11SL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.RadialWindowTransportC12X

set_option autoImplicit false

/-!
# records 合取 v3 = +linked +radial（CH12 C12-1 / C12-2，后缀 `_C12R`）

`exists_records_of_prepared_chain_v3_C12R`：`exists_records_of_prepared_chain_CXSP` 的孪生（原件不改）。
同一个 producer `S.exists_surgery_with_spatial_control_and_decay`，同一批 `records`、同一个 `F`，
结论 = 原 8 条 + `hasLinkedCanonicalWindow_C12X` + `witness.HasRadialCoordinates`。

**同一批 records、同一 witness**：linked 与 radial 都是对 *同一个* `records`（tuple 里取出的那一族）
的逐点陈述，分别经 tuple 的 `hbridge`（`HEq` static）从 `(S.observation n).records` 搬回；而
`(S.observation n)` 的 linked / radial 都是 `S.state (n+1)` 的字段（`PreparedSpatialState.linked`、
`PreparedSpatialState.radial`），后者在 `PreparedSpatialStep` 的同一次 step 构造里与 `linked` 并列
产出（见 tracked diff 块）。所以不是 "∃ linked records" 与 "∃ radial records" 的拼接。

前提：本文件依赖 tracked 改动块 `PreparedSpatialState.radial`（State / Base / Step 三文件）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch11

universe u

/-- narrow tuple 的出口（radial 版，`hlink_of_narrowTuple_C11SL` 的孪生）：
tuple 的 `records` 每个 static cap 的 witness 有径向坐标。 -/
theorem hradial_of_narrowTuple_C12R {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i q)
    (hTower : F.tower = S.tower)
    (hstatic : q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
      q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
      q.recenterConstant = pBase.recenterConstant)
    (hbridge : ∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
      (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) :
    ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      ((records n i).static b).witness.HasRadialCoordinates := by
  rcases F with ⟨K, hcontrol⟩
  change K = S.tower at hTower
  subst hTower
  intro n i
  have hs := (S.observation n).static_eq
  exact MetricCutCapEvent.PresentedStaticCap.hasRadialCoordinates_of_family_heq
    rfl rfl rfl rfl HEq.rfl (hstatic.1.trans hs.1.symm) (hstatic.2.1.trans hs.2.1.symm)
    (hstatic.2.2.1.trans hs.2.2.1.symm) (hstatic.2.2.2.1.trans hs.2.2.2.1.symm)
    ((S.observation n).records i).static (records n i).static (hbridge n i i rfl).2.2.2.2
    (fun b => (S.state (n + 1)).radial
      (Fin.castLE (Nat.le_of_lt_succ ((S.state (n + 1)).history.toHistory.activeStage
        (S.observationTime n)).isLt) i) b)

/-- **C12-1 / C12-2（v3）**：G21 `exists_records_of_prepared_chain_CXSP` 的孪生，同一批 records
同时带 `hasLinkedCanonicalWindow_C12X`（第 6 条）与 `HasRadialCoordinates`（第 7 条）。
原 8 条的次序保持（5 → canonical；8 → old = retainedCore；9 → δ → 0；10 → recent）。 -/
theorem exists_records_of_prepared_chain_v3_C12R
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) :
    ∃ (params : CutoffParameters)
      (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory e params),
      params.modelRadius = pBase.modelRadius ∧ params.modelOrder = pBase.modelOrder ∧
      params.modelAccuracy = pBase.modelAccuracy ∧
      (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
        params.neckRadius t = q.neckRadius t) ∧
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) ∧
      (∀ n e b, ((records n e).static b).hasLinkedCanonicalWindow_C12X) ∧
      (∀ n e b, ((records n e).static b).witness.HasRadialCoordinates) ∧
      (∀ n e, ((F.tower.history n).toHistory.event e).old =
        ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) ∧
      Tendsto params.delta atTop (𝓝 0) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
          ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t := by
  obtain ⟨F₀, params, _κ, records, hTower₀, hstatic, -, -, -, -, hpref, hbridge, -, hcan, -, -,
    hdecay, hrecent⟩ := S.exists_surgery_with_spatial_control_and_decay
  have hF : F₀ = F := by
    have hT := hTower₀.trans hTower.symm
    cases F₀
    cases F
    congr 1
  subst F₀
  have hlinked := hlink_of_narrowTuple_C11SL S F params records hTower hstatic hbridge
  have hradial := hradial_of_narrowTuple_C12R S F params records hTower hstatic hbridge
  refine ⟨params, records, hstatic.2.1, hstatic.2.2.1, hstatic.2.2.2.1, ?_, hcan, hlinked,
    hradial, fun n e => (records n e).old_eq_retained, hdecay, hrecent⟩
  intro t ht
  have hp := hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩
  have hδ : params.delta t = (chainDiagonal_C11A S).delta t := hp.1
  have hnr : params.neckRadius t = (chainDiagonal_C11A S).neckRadius t := hp.2.1
  exact ⟨hδ.trans (hdiag t ht).1.symm, hnr.trans (hdiag t ht).2.symm⟩

end GC.LongTime.Ch11

end
