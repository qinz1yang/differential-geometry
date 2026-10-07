import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedObservationEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IdentifiedHistoryPinching

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal

namespace GC.GeneralFlow

universe u

/-- Select the actual outgoing incoming slab of the active stage. Its end is
strictly after the query, its birth metric is the actual initialMetric, and
its metric agrees with the actual stageMetric at every real time. All four
certificates retain their original thresholds. This theorem does not extend
any open estimate to the stage birth. -/
theorem NativeEstimates.exists_outgoingSlab_of_lt_horizon
    {K : RetainedCoreHistory.{u}}
    {ε C1 C2 C1s C2s qcan qs τmin : ℝ} {Ctime Cgrad : ℝ≥0}
    (hEst : NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad)
    (t : Icc (0 : ℝ) K.horizon) (htop : (t : ℝ) < K.horizon) :
    ∃ (s : ℝ)
      (G : (K.stage (K.toHistory.activeStage t)).IncomingSlab
        (K.time (K.toHistory.activeStage t)) s),
      (t : ℝ) < s ∧ s ≤ K.horizon ∧
      G.flow.base.metric (K.time (K.toHistory.activeStage t)) =
        K.initialMetric (K.toHistory.activeStage t) ∧
      (∀ v : ℝ,
        G.flow.base.metric v = K.toHistory.stageMetric (K.toHistory.activeStage t) v) ∧
      G.DerivativeBoundBefore Ctime qcan s ∧
      G.GradientBoundBefore Cgrad qcan s ∧
      G.CanonicalBefore ε C1 C2 qcan τmin s ∧
      G.SpatiallyCanonicalBefore ε C1s C2s qs s := by
  have hdom := K.toHistory.activeStage_mem t
  generalize hj : K.toHistory.activeStage t = j at hdom ⊢
  cases j using Fin.lastCases with
  | last =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc] at hdom
    have hfinal : K.time (Fin.last K.eventCount) < K.horizon := hdom.1.trans_lt htop
    let G := (K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl
    refine ⟨K.horizon, G, htop, le_rfl, K.final_initial hfinal, ?_, hEst.2 hfinal⟩
    intro v
    exact (ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfinal) v).symm
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hdom
    refine ⟨K.time i.succ, (K.toHistory.event i).incoming, hdom.2,
      K.toHistory.time_le_horizon_at i.succ, K.event_initial i, ?_, hEst.1 i⟩
    intro v
    exact (ObservedHistory.stageMetric_castSucc_apply (H := K.toHistory) i v).symm

/-- Extract the incoming fields of the finite birth argument at one explicit
query threshold Q. The actual history and all four native estimates remain
unchanged. The strict observation buffer pays a positive final slab whenever
the active stage is last; no strict-birth assumption is needed here. -/
theorem NativeEstimates.buffered_incoming_certificates
    {K : RetainedCoreHistory.{u}}
    {ε C1 C2 C1s C2s qcan qs τmin κ : ℝ} {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ}
    (hEst : NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad)
    (hnc : K.NoncollapsedBefore κ ε K.horizon)
    (hpinch : K.EventSlabsPinched phi ∧
      ∀ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
        Perelman.PhiAlmostNonnegative (K.finalSlab hfinal).flow
          (Icc (K.time (Fin.last K.eventCount)) K.horizon) phi)
    (t : Icc (0 : ℝ) K.horizon) {T : ℝ}
    (htT : (t : ℝ) ≤ T) (hTK : T < K.horizon)
    (Q : ℝ) (hcanQ : qcan ≤ Q) (hsQ : qs ≤ Q) :
    NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
    K.EventSlabsPinched phi ∧
    K.EventSlabsSpatiallyCanonical ε C1s C2s Q (K.toHistory.activeStage t) ∧
    K.EventSlabsDerivative Ctime Q (K.toHistory.activeStage t) ∧
    K.EventSlabsGradient Cgrad Q (K.toHistory.activeStage t) ∧
    K.NoncollapsedBefore κ ε (t : ℝ) ∧
    (K.toHistory.activeStage t = Fin.last K.eventCount →
      ∃ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
        Perelman.PhiAlmostNonnegative (K.finalSlab hfinal).flow
          (Icc (K.time (Fin.last K.eventCount)) K.horizon) phi) := by
  refine ⟨hEst, hpinch.1, ?_, ?_, ?_, K.noncollapsedBefore_mono t.property.2 hnc, ?_⟩
  · intro j _ x v hv hQ
    exact (hEst.1 j).2.2.2 x v hv (hsQ.trans_lt hQ)
  · intro j _ x v hv hQ
    exact (hEst.1 j).1 x v hv (hcanQ.trans_lt hQ)
  · intro j _ x v hv hQ
    exact (hEst.1 j).2.1 x v hv (hcanQ.trans_lt hQ)
  · intro hlast
    have hbirth := K.toHistory.activeStage_time_le t
    rw [hlast] at hbirth
    have hfinal : K.time (Fin.last K.eventCount) < K.horizon :=
      hbirth.trans_lt (htT.trans_lt hTK)
    exact ⟨hfinal, hpinch.2 hfinal⟩

end GC.GeneralFlow
