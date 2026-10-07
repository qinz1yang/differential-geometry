import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveBall

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology
namespace GC.GeneralFlow
universe u

open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport

/-- The native own-threshold reserve ball at the original point of the same flow
observation, with all physical inputs and the reserve radius unchanged. -/
theorem PreparedSpatialChain.isParabolicallyRmControlledBall_observation_at_reserve_of_scalar_le
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower)
    (j : ℕ) {εcut Dcut : ℝ} {mcut : ℕ}
    (W : PreparedSpatialStepRetention (S.state j) (S.state (j + 1))
      (S.accuracy j) (1 / ((j : ℝ) + 2)) εcut Dcut mcut)
    (hshift : (S.state (j + 1)).shift =
      (S.state j).history.time (Fin.last (S.state j).history.eventCount))
    (hoffset : (S.state (j + 1)).offset = (S.state j).history.eventCount)
    (U : ℝ) (hU : 0 ≤ U)
    (T : Icc (0 : ℝ) (F.observation.observe U hU).horizon)
    (τ : Icc (0 : ℝ) W.oldNative.horizon)
    (hclock : (T : ℝ) = (τ : ℝ) + (S.state j).shift)
    (htop : (τ : ℝ) < W.oldNative.horizon)
    (hcan : ∀ i b, ((W.oldNativeRecords i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((W.oldNativeRecords i).static b).neck.scale / 2 ≤
      metricScalarAt ((W.oldNativeRecords i).static b).witness.metric
        (((W.oldNativeRecords i).static b).witness.cap z))
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : W.oldNative.EventSlabsPinched phi)
    (hlast : W.oldNative.toHistory.activeStage τ = Fin.last W.oldNative.eventCount →
      ∃ h : W.oldNative.time (Fin.last W.oldNative.eventCount) < W.oldNative.horizon,
        Perelman.PhiAlmostNonnegative (W.oldNative.finalSlab h).flow
          (Icc (W.oldNative.time (Fin.last W.oldNative.eventCount)) W.oldNative.horizon) phi)
    (x : ((F.observation.observe U hU).stageAt T).Carrier)
    (hRle : metricScalarAt
      ((F.observation.observe U hU).stageMetric
        ((F.observation.observe U hU).activeStage T) T) x ≤ (S.state j).prepared.Qall)
    (hback : ((S.state j).radius / 100) ^ 2 ≤ (τ : ℝ))
    (hgradScale : (C.Cgrad : ℝ) * ((S.state j).radius / 100) *
      Real.sqrt (S.state j).prepared.Qall ≤ 1 / 4)
    (htimeScale : C.Ctime * (4 * (S.state j).prepared.Qall) *
      ((S.state j).radius / 100) ^ 2 ≤ 1 / 2)
    (hpinchScale : ((S.state j).radius / 100) ^ 4 *
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * (S.state j).prepared.Qall)) ^ 2 ≤ 1)
    (hlarge : ∀ i : Fin W.oldNative.eventCount,
      W.oldNative.time i.succ ∈ Ioc ((τ : ℝ) - ((S.state j).radius / 100) ^ 2) (τ : ℝ) →
      ∀ b : (W.oldNative.toHistory.event i).RetainedBoundaryIndex,
        16 * (S.state j).prepared.Qall < ((W.oldNativeRecords i).static b).neck.scale) :
    (F.observation.observe U hU).isParabolicallyRmControlledBall T x ((S.state j).radius / 100) := by
  obtain ⟨hstage, hmetric, hball⟩ := S.native_query_transport_to_observation
    F hTower j W hshift hoffset U hU T τ hclock
  let y := overlapCastPoint hstage x
  have hpoint : HEq x y := (overlapCastPoint_heq hstage x).symm
  have hscalar := overlap_scalar_eq hstage hmetric hpoint
  have hRleNative : metricScalarAt
      (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage τ) τ) y ≤
        (S.state j).prepared.Qall := by
    rw [← hscalar]
    exact hRle
  exact hball x y hpoint ((S.state j).radius / 100)
    (W.isParabolicallyRmControlledBall_at_reserve_of_scalar_le
      hcan hscale hphi hpinch τ htop hlast y hRleNative
      hback hgradScale htimeScale hpinchScale hlarge)

end GC.GeneralFlow
