import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Base_O34
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Metric.Distance.Basic

/-!
# CH12-O34 G3: restart sub-balls (S2 of KL Lemma 86.2, halved centres, R4 D-R4-5 (2))

A ball `B(z, θ r)` with centre `z ∈ B(x, r / 2)` and `θ ≤ 1 / 2` lies in `B(x, r)`, so the
sectional lower bound (with the larger bound `-((θ r) ^ 2)⁻¹`) and the Euclidean-subball volume
premise of the parent pass to it.  This is the "same time" part of the Child conditions of the
STEP clause of `[FROZEN v4] CH12-O34`.
-/
set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Restart sub-balls: `z ∈ B(x, r/2)`, `0 < θ ≤ 1/2` ⇒ the parent's sec/vol premises hold on
`B(z, θ r)` at radius `θ r`. -/
theorem child_ball_O34 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (s : RegularSlice F.observation)
    (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (x z : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) {r θ ε : ℝ}
    (hr : 0 < r) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hz : z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) x (r / 2))
    (hsec : (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) x (r),
      SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) q (-((r) ^ 2)⁻¹)))
    (hvol : (∀ w ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) x (r),
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
        ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤ ballVolume ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) w ρ)) :
    (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) z (θ * r),
      SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) q (-((θ * r) ^ 2)⁻¹)) ∧
    (∀ w ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) z (θ * r),
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ θ * r →
        ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤ ballVolume ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) w ρ) := by
  have hin : ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) z (θ * r), q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) x r := by
    intro q hq
    have hz' : riemannianEDistOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) x z < ENNReal.ofReal (r / 2) := hz
    have hq' : riemannianEDistOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) z q < ENNReal.ofReal (θ * r) := hq
    have h1 := riemannianEDistOf_triangle ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) x z q
    have h2 : ENNReal.ofReal (r / 2) + ENNReal.ofReal (θ * r) ≤ ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    change riemannianEDistOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) x q < ENNReal.ofReal r
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le (ENNReal.add_lt_add hz' hq') h2)
  have hθr : θ * r ≤ r := mul_le_of_le_one_left hr.le (by linarith)
  have hsq : (θ * r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hθr 2
  refine ⟨fun q hq => (hsec q (hin q hq)).mono (neg_le_neg (inv_anti₀ (by positivity) hsq)),
    fun w hw ρ hρ hρr => hvol w (hin w hw) ρ hρ (le_trans hρr hθr)⟩

end GC.LongTime.Ch12
