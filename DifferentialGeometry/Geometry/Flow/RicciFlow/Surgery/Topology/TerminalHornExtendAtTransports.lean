import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAtStageTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornPointSliceGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeck

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (SpatialCanonicalWitness SpatialCanonicalAlternative SpatialNeck SpatialLocalNeck)
open scoped NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

variable (H : RetainedCoreHistory.{u})
  (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
  (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
  (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
    H.initialMetric (Fin.last H.eventCount)) {τ : ℝ}
  (hat : H.time (Fin.last H.eventCount) < τ) (hτs : τ < s) (x : G.terminalRegularOpen)
  (y : ((H.extendAt hend G hG hat hτs).toHistory.stageAt
    (H.extendAtTime hend G hG hat hτs)).Carrier) (hy : HEq y x.val)

include hy

theorem extendAt_scalar_lower_on_ball_of_gradientBoundBefore {Cgrad : ℝ≥0} {qcan A : ℝ}
    (hgrad : G.GradientBoundBefore Cgrad qcan s) (hq : 0 < qcan) (hA : 0 ≤ A)
    (hqR : qcan < G.flow.scalar τ x.val / (4 * (1 + Cgrad * A) ^ 2)) :
    ∀ z ∈ riemannianBallOf ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
        ((H.extendAt hend G hG hat hτs).toHistory.activeStage
          (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) y
        (A / Real.sqrt (G.flow.scalar τ x.val)),
      (4 * (1 + Cgrad * A) ^ 2)⁻¹ * G.flow.scalar τ x.val ≤
        metricScalarAt ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
          ((H.extendAt hend G hG hat hτs).toHistory.activeStage
            (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) z := by
  refine (H.extendAt_stageAt_iff hend G hG hat hτs (fun _ g yh => ∀ z ∈ riemannianBallOf g yh
      (A / Real.sqrt (G.flow.scalar τ x.val)),
      (4 * (1 + Cgrad * A) ^ 2)⁻¹ * G.flow.scalar τ x.val ≤ metricScalarAt g z)
    x.val y hy).mpr ?_
  intro z hz
  rw [inv_mul_eq_div]
  exact OrientedThreeStage.IncomingSlab.quarter_scalar_le_on_closedBall_of_gradientBoundBefore
    hgrad ⟨hat, hτs⟩ hq hA x.val hqR z
    (show riemannianEDistOf (G.flow.base.metric τ) x.val z < _ from hz).le

theorem extendAt_scalar_upper_on_ball (L : G.TerminalLimitMetric) {r Q A : ℝ} (hr : 0 < r)
    (hQ : 1 ≤ Q)
    (hL : ∀ w : G.terminalRegularOpen,
      riemannianEDistOf L.metric x w < ENNReal.ofReal (2 * r) →
      metricScalarAt L.metric w ≤ Q * metricScalarAt L.metric x)
    (hsub : riemannianBallOf (G.flow.base.metric τ) x.val (16 * r / 17) ⊆
      Subtype.val '' riemannianClosedBallOf L.metric x r)
    (hclose : ∀ w ∈ riemannianClosedBallOf L.metric x r,
      |metricScalarAt (G.flow.base.metric τ) w.val - metricScalarAt L.metric w| <
        metricScalarAt L.metric x)
    (hrad : A / Real.sqrt (G.flow.scalar τ x.val) ≤ 16 * r / 17)
    (hlow : metricScalarAt L.metric x / 2 ≤ G.flow.scalar τ x.val) :
    ∀ z ∈ riemannianBallOf ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
        ((H.extendAt hend G hG hat hτs).toHistory.activeStage
          (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) y
        (A / Real.sqrt (G.flow.scalar τ x.val)),
      metricScalarAt ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
          ((H.extendAt hend G hG hat hτs).toHistory.activeStage
            (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) z ≤
        2 * (Q + 1) * G.flow.scalar τ x.val := by
  refine (H.extendAt_stageAt_iff hend G hG hat hτs (fun _ g yh => ∀ z ∈ riemannianBallOf g yh
      (A / Real.sqrt (G.flow.scalar τ x.val)),
      metricScalarAt g z ≤ 2 * (Q + 1) * G.flow.scalar τ x.val) x.val y hy).mpr ?_
  intro z hz
  have hb := L.scalar_le_on_slice_ball_of_image_closedBall x hr hL hsub hclose z
    (riemannianBallOf_mono _ _ hrad hz)
  change G.flow.scalar τ z ≤ _
  calc G.flow.scalar τ z ≤ Q * metricScalarAt L.metric x + metricScalarAt L.metric x := hb
    _ = (Q + 1) * metricScalarAt L.metric x := by ring
    _ ≤ (Q + 1) * (2 * G.flow.scalar τ x.val) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = 2 * (Q + 1) * G.flow.scalar τ x.val := by ring

theorem extendAt_neck_alternative_on_ball (L : G.TerminalLimitMetric) {r A c ε C1 C2 : ℝ}
    (hsub : riemannianBallOf (G.flow.base.metric τ) x.val (16 * r / 17) ⊆
      Subtype.val '' riemannianClosedBallOf L.metric x r)
    (hwit : ∀ w ∈ riemannianClosedBallOf L.metric x r,
      ∀ W : SpatialCanonicalWitness (G.flow.base.metric τ) ε C1 C2 w.val,
        W.capTubeHasNeckChart ε →
          ∃ neck : SpatialLocalNeck (G.flow.base.metric τ) ε w.val W.domain.carrier,
            W.alternative = SpatialCanonicalAlternative.neck neck)
    (hrad : A / Real.sqrt (G.flow.scalar τ x.val) ≤ 16 * r / 17) :
    ∀ z ∈ riemannianBallOf ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
        ((H.extendAt hend G hG hat hτs).toHistory.activeStage
          (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) y
        (A / Real.sqrt (G.flow.scalar τ x.val)),
      c * G.flow.scalar τ x.val ≤
        metricScalarAt ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
          ((H.extendAt hend G hG hat hτs).toHistory.activeStage
            (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) z →
      ∀ W : SpatialCanonicalWitness ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
          ((H.extendAt hend G hG hat hτs).toHistory.activeStage
            (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) ε C1 C2 z,
        W.capTubeHasNeckChart ε → ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk := by
  refine (H.extendAt_stageAt_iff hend G hG hat hτs (fun _ g yh => ∀ z ∈ riemannianBallOf g yh
      (A / Real.sqrt (G.flow.scalar τ x.val)),
      c * G.flow.scalar τ x.val ≤ metricScalarAt g z →
      ∀ W : SpatialCanonicalWitness g ε C1 C2 z, W.capTubeHasNeckChart ε →
        ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) x.val y hy).mpr ?_
  intro z hz _ W hW
  obtain ⟨w, hw, rfl⟩ := hsub (riemannianBallOf_mono _ _ hrad hz)
  obtain ⟨neck, hneck⟩ := hwit w hw W hW
  exact ⟨neck, hneck⟩

theorem extendAt_exists_separating_sets {R : ℝ}
    (S V W : Set (H.stage (Fin.last H.eventCount)).Carrier) (hV : IsOpen V) (hW : IsOpen W)
    (hVW : Disjoint V W)
    (hS : ∀ z ∈ S, riemannianEDistOf (G.flow.base.metric τ) x.val z ≤
      ENNReal.ofReal (7 / Real.sqrt R)) :
    ∃ S' V' W' : Set ((H.extendAt hend G hG hat hτs).toHistory.stageAt
        (H.extendAtTime hend G hG hat hτs)).Carrier,
      IsOpen V' ∧ IsOpen W' ∧ Disjoint V' W' ∧
      (∀ z ∈ S', riemannianEDistOf ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
          ((H.extendAt hend G hG hat hτs).toHistory.activeStage
            (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) y z ≤
        ENNReal.ofReal (7 / Real.sqrt R)) ∧
      ∀ A : ℝ,
        (riemannianClosedBallOf (G.flow.base.metric τ) x.val (3 * A / Real.sqrt R) \ S ⊆
            V ∪ W ∧
          ∃ p ∈ V, ∃ q ∈ W,
            ENNReal.ofReal (A / Real.sqrt R) ≤ riemannianEDistOf (G.flow.base.metric τ) x.val p ∧
            riemannianEDistOf (G.flow.base.metric τ) x.val p <
              ENNReal.ofReal (3 * A / Real.sqrt R) ∧
            ENNReal.ofReal (A / Real.sqrt R) ≤ riemannianEDistOf (G.flow.base.metric τ) x.val q ∧
            riemannianEDistOf (G.flow.base.metric τ) x.val q <
              ENNReal.ofReal (3 * A / Real.sqrt R)) →
        riemannianClosedBallOf ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
            ((H.extendAt hend G hG hat hτs).toHistory.activeStage
              (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) y
            (3 * A / Real.sqrt R) \ S' ⊆ V' ∪ W' ∧
        ∃ p ∈ V', ∃ q ∈ W',
          ENNReal.ofReal (A / Real.sqrt R) ≤
            riemannianEDistOf ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
              ((H.extendAt hend G hG hat hτs).toHistory.activeStage
                (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) y p ∧
          riemannianEDistOf ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
              ((H.extendAt hend G hG hat hτs).toHistory.activeStage
                (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) y p <
            ENNReal.ofReal (3 * A / Real.sqrt R) ∧
          ENNReal.ofReal (A / Real.sqrt R) ≤
            riemannianEDistOf ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
              ((H.extendAt hend G hG hat hτs).toHistory.activeStage
                (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) y q ∧
          riemannianEDistOf ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
              ((H.extendAt hend G hG hat hτs).toHistory.activeStage
                (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) y q <
            ENNReal.ofReal (3 * A / Real.sqrt R) :=
  (H.extendAt_stageAt_iff hend G hG hat hτs (fun K g yh => ∃ S' V' W' : Set K.Carrier,
      IsOpen V' ∧ IsOpen W' ∧ Disjoint V' W' ∧
      (∀ z ∈ S', riemannianEDistOf g yh z ≤ ENNReal.ofReal (7 / Real.sqrt R)) ∧
      ∀ A : ℝ,
        (riemannianClosedBallOf (G.flow.base.metric τ) x.val (3 * A / Real.sqrt R) \ S ⊆
            V ∪ W ∧
          ∃ p ∈ V, ∃ q ∈ W,
            ENNReal.ofReal (A / Real.sqrt R) ≤ riemannianEDistOf (G.flow.base.metric τ) x.val p ∧
            riemannianEDistOf (G.flow.base.metric τ) x.val p <
              ENNReal.ofReal (3 * A / Real.sqrt R) ∧
            ENNReal.ofReal (A / Real.sqrt R) ≤ riemannianEDistOf (G.flow.base.metric τ) x.val q ∧
            riemannianEDistOf (G.flow.base.metric τ) x.val q <
              ENNReal.ofReal (3 * A / Real.sqrt R)) →
        riemannianClosedBallOf g yh (3 * A / Real.sqrt R) \ S' ⊆ V' ∪ W' ∧
        ∃ p ∈ V', ∃ q ∈ W',
          ENNReal.ofReal (A / Real.sqrt R) ≤ riemannianEDistOf g yh p ∧
          riemannianEDistOf g yh p < ENNReal.ofReal (3 * A / Real.sqrt R) ∧
          ENNReal.ofReal (A / Real.sqrt R) ≤ riemannianEDistOf g yh q ∧
          riemannianEDistOf g yh q < ENNReal.ofReal (3 * A / Real.sqrt R))
    x.val y hy).mpr ⟨S, V, W, hV, hW, hVW, hS, fun _ h => h⟩

theorem extendAt_not_nonempty_spatialNeck {eps : ℝ}
    (h : ¬ Nonempty (SpatialNeck (G.flow.base.metric τ) eps x.val)) :
    ¬ Nonempty (SpatialNeck ((H.extendAt hend G hG hat hτs).toHistory.stageMetric
        ((H.extendAt hend G hG hat hτs).toHistory.activeStage
          (H.extendAtTime hend G hG hat hτs)) (H.extendAtTime hend G hG hat hτs)) eps y) :=
  (H.extendAt_stageAt_iff hend G hG hat hτs
    (fun _ g yh => ¬ Nonempty (SpatialNeck g eps yh)) x.val y hy).mpr h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
