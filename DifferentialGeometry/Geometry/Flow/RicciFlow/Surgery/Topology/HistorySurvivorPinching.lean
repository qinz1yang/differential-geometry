import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFootprint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalPinching

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
variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

theorem curvatureOperatorLowerBoundAt_backwardSurvivorFootprint
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
    {t : ℝ} (ht : t ∈ Icc (H.time first) (H.time i.succ)) :
    ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
      curvatureOperatorLowerBoundAt (G t) x (metricAlgebraicCurvatureTensorAt (G t) x)
        (Phi (metricScalarAt (G t) x)) := by
  by_cases hlasttime : H.time i.castSucc ≤ t
  · rw [hlast t ⟨hlasttime, ht.2⟩]
    apply pinching_restrictOpen
    unfold backwardSurvivorTerminalFaceMetric
    apply pinching_localPullMetric
    exact (H.event i).terminal.extendedMetric_curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative
      hPhi (hpinch i hle le_rfl) ⟨hlasttime, ht.2⟩
  · have hti : t < H.time i.castSucc := lt_of_not_ge hlasttime
    let tH : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg first).trans ht.1, ht.2.trans (H.time_le_horizon_at i.succ)⟩
    let k := H.activeStage tH
    have hk : k < i.castSucc := by
      apply H.time_strictMono.lt_iff_lt.mp
      exact (H.activeStage_time_le tH).trans_lt hti
    have hkfirst : first ≤ k := H.le_activeStage tH first ht.1
    let j : Fin H.eventCount := ⟨k.val, by
      have := i.isLt
      change k.val < H.eventCount
      omega⟩
    have hf : first ≤ j.castSucc := hkfirst
    have hl : j.succ ≤ i.castSucc := by
      change k.val + 1 ≤ i.val
      have hki : k.val < i.val := hk
      omega
    have htj : t ∈ Icc (H.time j.castSucc) (H.time j.succ) := by
      refine ⟨H.activeStage_time_le tH, ?_⟩
      exact (H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)).le
    rw [hslabs j hf hl t htj]
    apply pinching_restrictOpen
    apply pinching_restrictOpen
    unfold backwardSurvivorSlabMetric
    apply pinching_localPullMetric
    exact (H.event j).terminal.extendedMetric_curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative
      hPhi (hpinch j hf hk.le) htj

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
