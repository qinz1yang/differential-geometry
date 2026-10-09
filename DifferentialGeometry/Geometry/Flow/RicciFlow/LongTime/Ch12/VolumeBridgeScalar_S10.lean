import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime
universe u
namespace GC.LongTime.Ch12

theorem lower_transport_S10 {A B : OrientedThreeStage.{u}} (hAB : A = B) {mA : A.Metric}
    {mB : B.Metric} (hm : HEq mA mB) {r : ℝ}
    (h : ∀ x : A.Carrier, r ≤ metricScalarAt mA x) : ∀ x : B.Carrier, r ≤ metricScalarAt mB x := by
  subst hAB
  cases eq_of_heq hm
  exact h

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- The profile scalar lower bound (stated on `postMetric`) transfers to every smooth interval of
any observed history `observe b`. -/
theorem postMetric_lower_on_observe_S10 (O : ObservationTower P g) (B : ℝ → ℝ)
    (hlow : ∀ t, 0 ≤ t → ∀ x : (postStage O t).Carrier, B t ≤ metricScalarAt (postMetric O t) x)
    (b : ℝ) (hb : 0 ≤ b) (t : Icc (0 : ℝ) b) :
    ∀ x : ((O.observe b hb).stage ((O.observe b hb).activeStage ⟨t.1, t.2.1, t.2.2⟩)).Carrier,
      B t.1 ≤ metricScalarAt ((O.observe b hb).stageMetric
        ((O.observe b hb).activeStage ⟨t.1, t.2.1, t.2.2⟩) t.1) x := by
  have ht0 : 0 ≤ t.1 := t.2.1
  have hmax : max t.1 0 = t.1 := max_eq_left ht0
  have hobs : O.observe (max t.1 0) (le_max_right t.1 0) = O.observe t.1 ht0 := by
    have hsub : (⟨max t.1 0, le_max_right t.1 0⟩ : {t : ℝ // 0 ≤ t}) = ⟨t.1, ht0⟩ :=
      Subtype.ext hmax
    exact congrArg (fun t : {t : ℝ // 0 ≤ t} => O.observe t.val t.property) hsub
  have hstage : postStage O t.1 = (O.observe t.1 ht0).stage (Fin.last (O.observe t.1 ht0).eventCount) := by
    unfold postStage
    rw [hobs]
  have hmetric : HEq (postMetric O t.1)
      ((O.observe t.1 ht0).stageMetric (Fin.last (O.observe t.1 ht0).eventCount) t.1) := by
    have hm : ∀ {H H' : ObservedHistory}, H = H' → ∀ τ : ℝ,
        HEq (H.stageMetric (Fin.last H.eventCount) τ) (H'.stageMetric (Fin.last H'.eventCount) τ) := by
      intro H H' h τ
      cases h
      rfl
    exact (heq_of_eq (congrArg
      (fun τ => (O.observe (max t.1 0) (le_max_right t.1 0)).stageMetric
        (Fin.last (O.observe (max t.1 0) (le_max_right t.1 0)).eventCount) τ) hmax)).trans
      (hm hobs t.1)
  have h1 := lower_transport_S10 hstage hmetric (hlow t.1 ht0)
  -- identify with the observation at `b`
  let t' : Icc (0 : ℝ) t.1 := ⟨t.1, ht0, le_rfl⟩
  have hst := O.observe_slice_stage t.1 b ht0 hb t.2.2 t'
  have hme := O.observe_slice_metric t.1 b ht0 hb t.2.2 t'
  have hact : (O.observe t.1 ht0).activeStage t' = Fin.last (O.observe t.1 ht0).eventCount :=
    (O.observe t.1 ht0).activeStage_at_horizon
  have hst' : (O.observe t.1 ht0).stage (Fin.last (O.observe t.1 ht0).eventCount) =
      (O.observe b hb).stage ((O.observe b hb).activeStage ⟨t.1, t.2.1, t.2.2⟩) := by
    rw [← hact]
    exact hst
  have hme' : HEq ((O.observe t.1 ht0).stageMetric (Fin.last (O.observe t.1 ht0).eventCount) t.1)
      ((O.observe b hb).stageMetric ((O.observe b hb).activeStage ⟨t.1, t.2.1, t.2.2⟩) t.1) := by
    rw [← hact]
    exact hme
  exact lower_transport_S10 hst' hme' h1

end GC.LongTime.Ch12
