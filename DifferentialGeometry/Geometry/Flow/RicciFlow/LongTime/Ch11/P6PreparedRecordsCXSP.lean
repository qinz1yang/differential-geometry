import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialSurgeryDecayPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfNarrowTupleC11A

set_option autoImplicit false

/-!
# CX-SPINE G21：任意 prepared chain 的同源实际 records

保留生产者选择的 params；它的 model 字段来自 pBase。用户 q 仅用于在非负时间
识别 delta/neckRadius，不把 q 的其余字段假定等于实际记录参数。
同 tower 的 RawSurgery 因 proof irrelevance 相等，故是原 F 上的同一批 records。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch11

universe u

/-- 同一 F 上的 actual records、model 识别、canonical windows 与 recent decay。 -/
theorem exists_records_of_prepared_chain_CXSP
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
      (∀ n e, ((F.tower.history n).toHistory.event e).old =
        ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) ∧
      Tendsto params.delta atTop (𝓝 0) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
          ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t := by
  obtain ⟨F₀, params, κ, records, hTower₀, ⟨-, hrad, hord, hacc, -⟩, -, -, -, -,
    hpref, -, -, hcan, -, -, hdecay, hrecent⟩ :=
    S.exists_surgery_with_spatial_control_and_decay
  have hF : F₀ = F := by
    have hT := hTower₀.trans hTower.symm
    cases F₀
    cases F
    congr 1
  subst F₀
  refine ⟨params, records, hrad, hord, hacc, ?_, hcan,
    fun n e => (records n e).old_eq_retained, hdecay, hrecent⟩
  intro t ht
  have hp := hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩
  have hδ : params.delta t = (chainDiagonal_C11A S).delta t := hp.1
  have hnr : params.neckRadius t = (chainDiagonal_C11A S).neckRadius t := hp.2.1
  exact ⟨hδ.trans (hdiag t ht).1.symm, hnr.trans (hdiag t ht).2.symm⟩

end GC.LongTime.Ch11
