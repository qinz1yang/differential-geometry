import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRecordsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LinkedBirthJetsCXSP

set_option autoImplicit false

/-!
# linked records producer（O-CH11-NATIVE-BORN G3d = O1 repair 的 producer 半边，后缀 `_C11SP`）

`exists_linked_records_of_prepared_chain_C11SP`：CX-SPINE G21 `exists_records_of_prepared_chain_CXSP`
的孪生，同一 producer `S.exists_surgery_with_spatial_control_and_decay`，第 5 条结论
`hasCanonicalWindow` 换成 `hasLinkedCanonicalWindow_C12X`（经 `hlink_of_narrowTuple_C11SL`，与 G63
`exists_prepared_linked_birth_jets_CXSP` 同源）。其余 7 条逐字。
NJSlot v3 的 records 侧接口：用本定理取 records，一份同时喂
* hBorn′（G3 `hBorn_linked_C11SP`，要 linked）；
* hSL1 rev2（要 `hasCanonicalWindow`）：`hasLinkedCanonicalWindow_C12X.hasCanonicalWindow` 逐点降级，
  见文件末 consumer（降级后的元组与 G21 结论逐字相同）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch11

universe u

/-- **G3d（PROVED）**：G21 孪生，records 带 linked canonical window。 -/
theorem exists_linked_records_of_prepared_chain_C11SP
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
      (∀ n e b, ((records n e).static b).hasLinkedCanonicalWindow_C12X) ∧
      (∀ n e, ((F.tower.history n).toHistory.event e).old =
        ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) ∧
      Tendsto params.delta atTop (𝓝 0) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
          ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t := by
  obtain ⟨F₀, params, _κ, records, hTower₀, hstatic, -, -, -, -, hpref, hbridge, -, -, -, -,
    hdecay, hrecent⟩ := S.exists_surgery_with_spatial_control_and_decay
  have hF : F₀ = F := by
    have hT := hTower₀.trans hTower.symm
    cases F₀
    cases F
    congr 1
  subst F₀
  have hlinked := hlink_of_narrowTuple_C11SL S F params records hTower hstatic hbridge
  refine ⟨params, records, hstatic.2.1, hstatic.2.2.1, hstatic.2.2.2.1, ?_, hlinked,
    fun n e => (records n e).old_eq_retained, hdecay, hrecent⟩
  intro t ht
  have hp := hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩
  have hδ : params.delta t = (chainDiagonal_C11A S).delta t := hp.1
  have hnr : params.neckRadius t = (chainDiagonal_C11A S).neckRadius t := hp.2.1
  exact ⟨hδ.trans (hdiag t ht).1.symm, hnr.trans (hdiag t ht).2.symm⟩

/-- consumer（NJSlot v3 records 侧接口）：linked 元组逐点降级后 = G21 结论逐字，所以同一份 records
同时满足 hSL1 rev2（canonical）与 hBorn′（linked）的 records 前提。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) :
    ∃ (params : CutoffParameters)
      (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory e params),
      (∀ n e b, ((records n e).static b).hasLinkedCanonicalWindow_C12X) ∧
      params.modelRadius = pBase.modelRadius ∧ params.modelOrder = pBase.modelOrder ∧
      params.modelAccuracy = pBase.modelAccuracy ∧
      (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
        params.neckRadius t = q.neckRadius t) ∧
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) ∧
      (∀ n e, ((F.tower.history n).toHistory.event e).old =
        ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) ∧
      Tendsto params.delta atTop (𝓝 0) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
          ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t := by
  obtain ⟨params, records, hmR, hmO, hmA, hpar, hlink, hold, hdel, hrec⟩ :=
    exists_linked_records_of_prepared_chain_C11SP S F hTower q hdiag
  exact ⟨params, records, hlink, hmR, hmO, hmA, hpar, fun n e b => (hlink n e b).hasCanonicalWindow,
    hold, hdel, hrec⟩

end GC.LongTime.Ch11
