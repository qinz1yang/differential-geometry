import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingPullback
import DifferentialGeometry.Geometry.Curvature.OperatorScaling

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

private theorem pinching_localPullMetric
    {M N : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric ThreeModel N) (f : M → N)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) (Phi : ℝ → ℝ)
    (hpinch : ∀ x : N, curvatureOperatorLowerBoundAt g x
      (metricAlgebraicCurvatureTensorAt g x) (Phi (metricScalarAt g x))) :
    ∀ x : M, curvatureOperatorLowerBoundAt (localPullMetric g f hf) x
      (metricAlgebraicCurvatureTensorAt (localPullMetric g f hf) x)
      (Phi (metricScalarAt (localPullMetric g f hf) x)) := by
  intro x
  rw [metricScalarAt_localPull, curvatureOperatorLowerBoundAt_localPullMetric_iff]
  exact hpinch (f x)

private theorem pinching_restrictOpen
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : TopologicalSpace.Opens M)
    (Phi : ℝ → ℝ)
    (hpinch : ∀ x : M, curvatureOperatorLowerBoundAt g x
      (metricAlgebraicCurvatureTensorAt g x) (Phi (metricScalarAt g x))) :
    ∀ x : U, curvatureOperatorLowerBoundAt (g.restrictOpen U) x
      (metricAlgebraicCurvatureTensorAt (g.restrictOpen U) x)
      (Phi (metricScalarAt (g.restrictOpen U) x)) := by
  rw [← DifferentialGeometry.localPullMetric_subtype_val]
  exact pinching_localPullMetric g Subtype.val _ Phi hpinch

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
  (K : Set G.terminalRegularOpen)
  (gflow : ℝ → SmoothRiemannianMetric ThreeModel
    (H.backwardSurvivorIncomingFootprint first last hle G K))
  (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
    ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
        (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K))
  (hlast : ∀ t ∈ Icc (H.time last) s,
    gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
      (H.backwardSurvivorIncomingFootprint first last hle G K))
  {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
  (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
    Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
  (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi)

include hslabs hlast hPhi hpinch hpinchFinal in
theorem curvatureOperatorLowerBoundAt_backwardSurvivorIncomingFootprint
    {t : ℝ} (ht : t ∈ Icc (H.time first) s) :
    ∀ x : H.backwardSurvivorIncomingFootprint first last hle G K,
      curvatureOperatorLowerBoundAt (gflow t) x (metricAlgebraicCurvatureTensorAt (gflow t) x)
        (Phi (metricScalarAt (gflow t) x)) := by
  by_cases hlasttime : H.time last ≤ t
  · rw [hlast t ⟨hlasttime, ht.2⟩]
    apply pinching_restrictOpen
    unfold backwardSurvivorIncomingMetric
    apply pinching_localPullMetric
    exact L.extendedMetric_curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative
      hPhi hpinchFinal ⟨hlasttime, ht.2⟩
  · have hti : t < H.time last := lt_of_not_ge hlasttime
    let tH : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg first).trans ht.1, hti.le.trans (H.time_le_horizon_at last)⟩
    let k := H.activeStage tH
    have hk : k < last := by
      apply H.time_strictMono.lt_iff_lt.mp
      exact (H.activeStage_time_le tH).trans_lt hti
    have hkfirst : first ≤ k := H.le_activeStage tH first ht.1
    let j : Fin H.eventCount := ⟨k.val, by have := last.isLt; change k.val < H.eventCount; omega⟩
    have hf : first ≤ j.castSucc := hkfirst
    have hl : j.succ ≤ last := hk
    have htj : t ∈ Icc (H.time j.castSucc) (H.time j.succ) := by
      refine ⟨H.activeStage_time_le tH, ?_⟩
      exact (H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)).le
    rw [hslabs j hf hl t htj]
    apply pinching_restrictOpen
    apply pinching_restrictOpen
    unfold backwardSurvivorSlabMetric
    apply pinching_localPullMetric
    exact (H.event j).terminal.extendedMetric_curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative
      hPhi (hpinch j hf hl) htj

private local instance :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let _ : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first last hle).isOpen)
  let _ : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

include hslabs hlast hPhi hpinch hpinchFinal in
theorem phiAlmostNonnegative_parabolic_backwardSurvivorIncomingFootprint_localPullback
    {E J M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace J] {I : ModelWithCorners ℝ E J} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace J M] [IsManifold I ∞ M] [T2Space M]
    {Q θ : ℝ} (hQ : 0 < Q) (hstart : H.time first ≤ s - θ / Q)
    (f : M → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hf : IsLocalDiffeomorph I ThreeModel ∞ f)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hmetric : ∀ v ∈ Icc (-θ) 0,
      S.base.metric v = localPullMetric (scaleMetric Q hQ (gflow (s + v / Q))) f hf) :
    Perelman.PhiAlmostNonnegative S (Icc (-θ) 0) (Perelman.rescalePinchingFunction Q Phi) := by
  let U : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K) D :=
    { base.metric := fun v => scaleMetric Q hQ (gflow (s + v / Q)) }
  have hU : Perelman.PhiAlmostNonnegative U (Icc (-θ) 0)
      (Perelman.rescalePinchingFunction Q Phi) := by
    intro v hv x
    have hlo : -(θ / Q) ≤ v / Q := by
      simpa only [neg_div] using div_le_div_of_nonneg_right hv.1 hQ.le
    have hhi : v / Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv.2 hQ.le
    have ht : s + v / Q ∈ Icc (H.time first) s := by constructor <;> linarith
    have hp := H.curvatureOperatorLowerBoundAt_backwardSurvivorIncomingFootprint
      first last hle G L K gflow hslabs hlast hPhi hpinch hpinchFinal ht x
    change curvatureOperatorLowerBoundAt (scaleMetric Q hQ (gflow (s + v / Q))) x
      (metricAlgebraicCurvatureTensorAt (scaleMetric Q hQ (gflow (s + v / Q))) x)
      (Perelman.rescalePinchingFunction Q Phi
        (metricScalarAt (scaleMetric Q hQ (gflow (s + v / Q))) x))
    rw [curvatureOperatorLowerBoundAt_scaleMetric_iff, metricScalarAt_scaleMetric,
      Perelman.rescalePinchingFunction]
    simpa only [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul] using hp
  have hp := hU.localPullback f hf
  intro v hv x
  change curvatureOperatorLowerBoundAt (S.base.metric v) x
    (metricAlgebraicCurvatureTensorAt (S.base.metric v) x)
    (Perelman.rescalePinchingFunction Q Phi (metricScalarAt (S.base.metric v) x))
  rw [hmetric v hv]
  exact hp v hv x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
