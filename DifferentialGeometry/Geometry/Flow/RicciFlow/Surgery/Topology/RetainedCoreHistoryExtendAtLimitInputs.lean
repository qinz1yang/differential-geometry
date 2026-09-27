import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAtBefore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitDerivativeCutoff

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (SpatialCanonicalWitness)
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

variable {P₀ : OrientedThreeStage.{u}}

theorem extendAt_traced_limit_inputs (H : RetainedCoreHistory P₀)
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {τ : ℝ}
    (hat : H.time (Fin.last H.eventCount) < τ) (hτs : τ < s)
    {κ ε ε₁ C1 C2 qcan : ℝ} {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hpinch : H.EventSlabsPinched phi)
    (hpinchG : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi)
    (hderiv : H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount))
    (hderivG : G.DerivativeBoundBefore Ctime qcan s)
    (hclass : H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last H.eventCount))
    (hcanG : H.StronglyCanonicalBefore (Fin.last H.eventCount) G ε ε₁ C1 C2 qcan s)
    (hnc : H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)))
    (hncG : H.TerminalNoncollapsedBefore hend G hG κ ε τ) :
    (∀ (v : Icc (0 : ℝ) (H.extendAt hend G hG hat hτs).toHistory.horizon)
        (p : ((H.extendAt hend G hG hat hτs).toHistory.stageAt v).Carrier) (r : ℝ),
      (v : ℝ) < H.extendAtTime hend G hG hat hτs → r ≤ ε →
      (H.extendAt hend G hG hat hτs).toHistory.isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel
          ((H.extendAt hend G hG hat hτs).toHistory.stageAt v).Carrier
          ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
            ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) v)
          (riemannianBallOf ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
            ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) v) p r)) ∧
    (∀ v : Icc (0 : ℝ) (H.extendAt hend G hG hat hτs).toHistory.horizon,
      (v : ℝ) ≤ H.extendAtTime hend G hG hat hτs →
      ∀ x : ((H.extendAt hend G hG hat hτs).toHistory.stageAt v).Carrier,
        curvatureOperatorLowerBoundAt ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
            ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
            ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) v) x)
          (phi (metricScalarAt ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
            ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) v) x))) ∧
    (∀ v : Icc (0 : ℝ) (H.extendAt hend G hG hat hτs).toHistory.horizon,
      (v : ℝ) ≤ H.extendAtTime hend G hG hat hτs →
      (H.extendAt hend G hG hat hτs).toHistory.time
        ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) < v →
      ∀ p : ((H.extendAt hend G hG hat hτs).toHistory.stageAt v).Carrier,
        qcan < metricScalarAt ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
          ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) v) p →
        ∃ Wt : SpatialCanonicalWitness ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
          ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) v) ε C1 C2 p,
          Wt.capTubeHasNeckChart ε) ∧
    (∀ v : Icc (0 : ℝ) (H.extendAt hend G hG hat hτs).toHistory.horizon,
      (v : ℝ) < H.extendAtTime hend G hG hat hτs →
      (H.extendAt hend G hG hat hτs).toHistory.time
        ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) < v →
      ∀ p : ((H.extendAt hend G hG hat hτs).toHistory.stageAt v).Carrier,
        qcan < metricScalarAt ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
          ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) v) p →
        |derivWithin (fun v' => metricScalarAt ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
            ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) v') p) (Iic (v : ℝ)) v| ≤
          Ctime * metricScalarAt ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
            ((H.extendAt hend G hG hat hτs).toHistory.activeStage v) v) p ^ 2) := by
  have hlastt : (H.extendAt hend G hG hat hτs).toHistory.activeStage
      (H.extendAtTime hend G hG hat hτs) = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last (hend ▸ hat.le) (G.closedPrefix τ hat hτs) hG
      (H.extendAtTime hend G hG hat hτs) hat.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v p r hv hr hball
    exact H.volume_ge_extendAt_of_terminalNoncollapsedBefore hend G hG hat hτs hnc hncG v p r hv
      hr hball
  · intro v _ x
    exact H.curvatureOperatorLowerBoundAt_extendAt_of_pinched hend G hG hat hτs hpinch hpinchG v x
  · intro v hv hev p hq
    exact H.exists_spatialCanonicalWitness_extendAt_of_before hend G hG hat hτs
      (fun j hj => (hclass j hj).spatiallyCanonicalBefore) hcanG.spatiallyCanonicalBefore v
      (hv.trans_lt hτs) hev p hq
  · intro v hv hev p hq
    refine (H.extendAt hend G hG hat
      hτs).abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt
      (t := H.extendAtTime hend G hG hat hτs) (t₀ := τ) le_rfl ?_ ?_ ?_ v hv hev p hq
    · rw [hlastt]
      exact hderiv
    · intro j hj
      exact absurd (hj.trans hlastt) (Fin.castSucc_lt_last j).ne
    · intro h _
      exact extendHorizon_finalSlab_derivativeBoundBefore hderivG hτs.le h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
