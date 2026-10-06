import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Pinching_CX12
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84GlueV2_O12

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Curvature.DimensionThree
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Discharge the pinching input of the v2 glue from the given profile.
The statement is the O12 addendum's `hpinchS`, with no additional input. -/
theorem slice_pinching_input_CX12
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ s : RegularSlice F.observation, ∀ v : Icc (0 : ℝ) s.history.horizon, v ≤ sliceTop_S8 s →
        ∀ x, curvatureOperatorLowerBoundAt (s.history.stageMetric (s.history.activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt (s.history.stageMetric (s.history.activeStage v) v) x)
          (Phi (metricScalarAt (s.history.stageMetric (s.history.activeStage v) v) x)) := by
  obtain ⟨Phi, hPhi, hbound⟩ :=
    Perelman.exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion
      Hp.pinchingShift_pos
  refine ⟨Phi, hPhi, fun s v _ x => ?_⟩
  let gm := s.history.stageMetric (s.history.activeStage v) v
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt gm x hdim
  have hreg := (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion gm
    (Hp.pinchingShift + v) x).mp (slice_history_fixedHI_CX12 Hp s v x)
  have hb := hbound (Hp.pinchingShift + v) (le_add_of_nonneg_right v.2.1) _ _ hreg
  have hp := hPhi.pos (metricScalarAt gm x)
  rw [leastCurvatureOperatorEigenvalueAt_eq_sectionalMin gm x basis horth] at hb
  exact (curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le gm basis horth).mpr (by linarith)

/-- Restrict an actual traced family in starting time, radius and backward
depth, while increasing its curvature bound. The center is the restriction
of the same trace, so no new center compatibility hypothesis is needed. -/
theorem traced_family_mono_CX12 {H : ObservedHistory.{u}}
    {a b top : Icc (0 : ℝ) H.horizon} {hat : a ≤ top}
    {x : (H.stageAt top).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
      (H.activeStage_mono hat) x)
    {ρ τ K ρ' τ' K' : ℝ}
    (hfamily : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
      H.isTracedRegion v (X.point (H.activeStage v) (H.activeStage_mono hav)
        (H.activeStage_mono hvt)) ρ τ K)
    (hab : a ≤ b) (hbt : b ≤ top) (hρ' : 0 < ρ') (hρ : ρ' ≤ ρ)
    (hτ' : 0 < τ') (hτ : τ' ≤ τ) (hK : 0 ≤ K) (hKK' : K ≤ K') :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hbv : b ≤ v) (hvt : v ≤ top),
      H.isTracedRegion v
        ((X.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt)).point
          (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt)) ρ' τ' K' := by
  intro v hbv hvt
  exact (hfamily v (hab.trans hbv) hvt).mono hρ' hρ hτ' hτ hK hKK'

/-- The point trace supplied by a traced ball is independent of how the
ball was obtained; this gives the needed compatibility at a restart seam. -/
theorem traced_region_center_trace_CX12 {H : ObservedHistory.{u}}
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {ρ τ K : ℝ}
    (h : H.isTracedRegion t p ρ τ K) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
      (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) p),
      (a : ℝ) = t - τ ∧ X.isRmBoundedBy (hat := hat) K := by
  obtain ⟨hρ, _, a, hat, ha, htrace⟩ := h
  obtain ⟨X, hX⟩ := htrace p (mem_ball_self_O12 _ p hρ)
  exact ⟨a, hat, X, ha, hX⟩

end GC.LongTime.Ch12
