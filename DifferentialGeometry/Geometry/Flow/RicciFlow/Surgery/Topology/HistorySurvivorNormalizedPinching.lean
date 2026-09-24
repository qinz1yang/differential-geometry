import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorPinching
import DifferentialGeometry.Geometry.Curvature.OperatorScaling

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

private local instance (K : Set (H.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorFootprintInterior first i hle K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorTerminalFace first i hle).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K).isOpen)

theorem phiAlmostNonnegative_parabolic_backwardSurvivorFootprint
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (G : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
            (H.backwardSurvivorFootprintInterior first i hle K))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    {Q θ : ℝ} (hQ : 0 < Q)
    (hstart : H.time first ≤ H.time i.succ - θ / Q)
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorFootprintInterior first i hle K) D)
    (hmetric : ∀ s ∈ Icc (-θ) 0,
      S.base.metric s = scaleMetric Q hQ (G (H.time i.succ + s / Q))) :
    Perelman.PhiAlmostNonnegative S (Icc (-θ) 0) (Perelman.rescalePinchingFunction Q Phi) := by
  intro s hs x
  have hlo : -(θ / Q) ≤ s / Q := by
    simpa only [neg_div] using div_le_div_of_nonneg_right hs.1 hQ.le
  have hhi : s / Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le
  have ht : H.time i.succ + s / Q ∈ Icc (H.time first) (H.time i.succ) := by
    constructor <;> linarith
  have hp := H.curvatureOperatorLowerBoundAt_backwardSurvivorFootprint first i hle K G
    hslabs hlast hPhi hpinch ht x
  change curvatureOperatorLowerBoundAt (S.base.metric s) x
    (metricAlgebraicCurvatureTensorAt (S.base.metric s) x)
    (Perelman.rescalePinchingFunction Q Phi (metricScalarAt (S.base.metric s) x))
  rw [hmetric s hs, curvatureOperatorLowerBoundAt_scaleMetric_iff,
    metricScalarAt_scaleMetric, Perelman.rescalePinchingFunction]
  simpa only [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul] using hp

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set DifferentialGeometry.Geometry.Curvature
universe u
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace F] {I : ModelWithCorners ℝ E F} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace F M] [IsManifold I ∞ M] [T2Space M]
  (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

theorem phiAlmostNonnegative_parabolic_backwardSurvivorFootprint_localPullback
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (G : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
            (H.backwardSurvivorFootprintInterior first i hle K))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    {Q θ : ℝ} (hQ : 0 < Q)
    (hstart : H.time first ≤ H.time i.succ - θ / Q)
    (f : M → H.backwardSurvivorFootprintInterior first i hle K)
    (hf : IsLocalDiffeomorph I ThreeModel ∞ f)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hmetric : ∀ s ∈ Icc (-θ) 0,
      S.base.metric s = localPullMetric
        (scaleMetric Q hQ (G (H.time i.succ + s / Q))) f hf) :
    Perelman.PhiAlmostNonnegative S (Icc (-θ) 0) (Perelman.rescalePinchingFunction Q Phi) := by
  let U : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorFootprintInterior first i hle K) D :=
    { base.metric := fun s => scaleMetric Q hQ (G (H.time i.succ + s / Q)) }
  have hp := (H.phiAlmostNonnegative_parabolic_backwardSurvivorFootprint first i hle K G
    hslabs hlast hPhi hpinch hQ hstart U (fun _ _ => rfl)).localPullback f hf
  intro s hs x
  change curvatureOperatorLowerBoundAt (S.base.metric s) x
    (metricAlgebraicCurvatureTensorAt (S.base.metric s) x)
    (Perelman.rescalePinchingFunction Q Phi (metricScalarAt (S.base.metric s) x))
  rw [hmetric s hs]
  exact hp s hs x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
