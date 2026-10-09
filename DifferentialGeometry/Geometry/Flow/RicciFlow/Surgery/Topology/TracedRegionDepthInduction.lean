import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionDepthStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature (metricScalarAt)
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

theorem scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball
    (H : RetainedCoreHistory.{u})
    {Ctime : ℝ≥0} {qcan R Q T ρ : ℝ} {u t : Icc (0 : ℝ) H.toHistory.horizon}
    (hR : 0 < R) (hQ : 0 < Q) (hstep : 2 * Ctime * Q * T ≤ 1) (hu : (u : ℝ) = t - T / R)
    (hut : u ≤ t)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hqcan : qcan ≤ Q * R) (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hball : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ρ,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ Q * R) :
    ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ρ,
      ∀ (w : Icc (0 : ℝ) H.toHistory.horizon) (_ : u ≤ w) (hwt : w ≤ t)
        (B : BackwardPointTrace H.toHistory (H.toHistory.activeStage w)
          (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hwt) x)
        (v : Icc (0 : ℝ) H.toHistory.horizon) (hwv : w ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hwv)
            (H.toHistory.activeStage_mono hvt)) ≤ 2 * (Q * R) := by
  have htime : Ctime * (Q * R) * ((t : ℝ) - u) ≤ 1 / 2 := by
    have heq : (Ctime : ℝ) * (Q * R) * ((t : ℝ) - u) = (2 * Ctime * Q * T) / 2 := by
      rw [hu]
      field_simp
      ring
    rw [heq]
    linarith
  refine H.scalar_le_two_mul_along_backward_traces_of_depth_step le_rfl hslabs hcurrent hfinal
    (mul_pos hQ hR) hqcan htime _ ?_
  intro x hx w htw hwt B v hwv hvt
  obtain rfl : w = t := le_antisymm hwt htw
  obtain rfl : v = w := le_antisymm hvt hwv
  rw [show B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hwv)
      (H.toHistory.activeStage_mono hvt) = x from B.endpoint_eq]
  exact hball x hx

private theorem scalar_le_on_ball_extendHorizon_of_final_slab
    (H : RetainedCoreHistory.{u}) {t : ℝ} (hT : H.horizon ≤ t)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (y : (H.stage (Fin.last H.eventCount)).Carrier) {ρ M : ℝ}
    (hball : ∀ z ∈ riemannianBallOf (S.flow.base.metric t) y ρ, S.flow.scalar t z ≤ M)
    (tt : Icc (0 : ℝ) (H.extendHorizon t hT S hS).toHistory.horizon) (htt : (tt : ℝ) = t)
    (k : Fin (H.eventCount + 1)) (hk : k = Fin.last H.eventCount)
    (y' : ((H.extendHorizon t hT S hS).toHistory.stage k).Carrier) (hy : HEq y' y) :
    ∀ x ∈ riemannianBallOf ((H.extendHorizon t hT S hS).toHistory.stageMetric k tt) y' ρ,
      metricScalarAt ((H.extendHorizon t hT S hS).toHistory.stageMetric k tt) x ≤ M := by
  subst hk
  obtain rfl : y' = y := eq_of_heq hy
  rw [H.stageMetric_extendHorizon_last hT S hS S.lt, htt]
  exact hball

theorem exists_scalar_le_along_backward_traces_of_final_slab_window
    (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) :
    ∃ εcone : ℝ, 0 < εcone ∧ ∀ ε : ℝ, ε ≤ εcone → ∀ A : ℝ, 0 < A →
      ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {t : ℝ}
        (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
        (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        1 ≤ q → Λ * q < S.flow.scalar t y →
        H.time (Fin.last H.eventCount) ≤ t - Λ / S.flow.scalar t y →
        (∀ x, q < S.flow.scalar t x →
          ∃ W : Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness
              (S.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
        (S.restrictIncoming le_rfl S.lt le_rfl).DerivativeBoundBefore Ctime q t →
        (S.restrictIncoming le_rfl S.lt le_rfl).GradientBoundBefore Cgrad q t →
        H.EventSlabsPinched phi →
        Perelman.PhiAlmostNonnegative (S.restrictIncoming le_rfl S.lt le_rfl).flow
          (Ico (H.time (Fin.last H.eventCount)) t) phi →
        H.TerminalNoncollapsedBefore hend (S.restrictIncoming le_rfl S.lt le_rfl) hS κ ρ t →
        Λ ≤ ρ * Real.sqrt (S.flow.scalar t y) →
      ∀ (hT : H.horizon ≤ t) (tt : Icc (0 : ℝ) (H.extendHorizon t hT S hS).toHistory.horizon),
        (tt : ℝ) = t →
      ∀ y' : ((H.extendHorizon t hT S hS).toHistory.stage
          ((H.extendHorizon t hT S hS).toHistory.activeStage tt)).Carrier, HEq y' y →
      ∀ (T : ℝ), 0 < T → 2 * Ctime * Q * T ≤ 1 →
      ∀ uu : Icc (0 : ℝ) (H.extendHorizon t hT S hS).toHistory.horizon,
        (uu : ℝ) = t - T / S.flow.scalar t y →
      ∀ x ∈ riemannianBallOf ((H.extendHorizon t hT S hS).toHistory.stageMetric
          ((H.extendHorizon t hT S hS).toHistory.activeStage tt) tt) y'
          (A / Real.sqrt (S.flow.scalar t y)),
        ∀ (w : Icc (0 : ℝ) (H.extendHorizon t hT S hS).toHistory.horizon) (_ : uu ≤ w)
          (hwt : w ≤ tt)
          (B : BackwardPointTrace (H.extendHorizon t hT S hS).toHistory
            ((H.extendHorizon t hT S hS).toHistory.activeStage w)
            ((H.extendHorizon t hT S hS).toHistory.activeStage tt)
            ((H.extendHorizon t hT S hS).toHistory.activeStage_mono hwt) x)
          (v : Icc (0 : ℝ) (H.extendHorizon t hT S hS).toHistory.horizon) (hwv : w ≤ v)
          (hvt : v ≤ tt),
          metricScalarAt ((H.extendHorizon t hT S hS).toHistory.stageMetric
              ((H.extendHorizon t hT S hS).toHistory.activeStage v) v)
            (B.point ((H.extendHorizon t hT S hS).toHistory.activeStage v)
              ((H.extendHorizon t hT S hS).toHistory.activeStage_mono hwv)
              ((H.extendHorizon t hT S hS).toHistory.activeStage_mono hvt)) ≤
            2 * (Q * S.flow.scalar t y) := by
  obtain ⟨εcone, hεcone, hbound⟩ :=
    exists_scalar_bound_at_distance_of_final_slab_window.{u} κ C1 C2 hκ Ctime Cgrad hphi
  refine ⟨εcone, hεcone, fun ε hε A hA => ?_⟩
  obtain ⟨Q, Λ, hQ1, hΛ1, hQ⟩ := hbound ε hε A hA
  refine ⟨Q, Λ, hQ1, hΛ1, ?_⟩
  intro H hend t S hS y q ρ hq1 hΛq hwin hW hderiv hfinal hgrad hpinch hpinchF hnc hρ hT tt
    htt y' hy T hT0 hstep uu huu
  have hball := hQ H hend S hS y q ρ hq1 hΛq hwin hW hderiv hfinal hgrad hpinch hpinchF hnc hρ
  have hqR : q ≤ S.flow.scalar t y := by nlinarith
  have hR : 0 < S.flow.scalar t y := by linarith
  have hlast : (H.extendHorizon t hT S hS).toHistory.activeStage tt = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last hT S hS tt (by rw [htt]; exact S.lt.le)
  have hut : uu ≤ tt := by
    change (uu : ℝ) ≤ tt
    rw [huu, htt]
    linarith [div_pos hT0 hR]
  refine (H.extendHorizon t hT S hS).scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball
    (qcan := q) hR (by linarith) hstep (by rw [huu, htt]) hut ?_ ?_ ?_
    (hqR.trans (le_mul_of_one_le_left hR.le hQ1)) y'
    (H.scalar_le_on_ball_extendHorizon_of_final_slab hT S hS y hball tt htt _ hlast y' hy)
  · rw [hlast]
    exact H.eventSlabsDerivative_extendHorizon hderiv hT S hS
  · intro j hj
    rw [hlast] at hj
    exact absurd hj (Fin.castSucc_lt_last j).ne
  · intro h _
    rw [htt]
    exact hfinal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
