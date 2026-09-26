import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ParabolicBallOfCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaModelCurvatureWindow

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def NormalizedSequence.TerminalSliceNoncollapsed {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (kappa' : ℝ) : Prop :=
  0 < kappa' ∧ ∀ᶠ i in atTop, ∀ time : (X.interval i).FlowTime, (time : ℝ) = 0 →
    ∀ B : FlowMetricBall (X.term i).S time, B.radius ≤ 1 → B.IsSpatiallyRmControlled →
      B.IsKappaNoncollapsed kappa'

theorem exists_terminalSliceNoncollapsed {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
      ∃ kappa' : ℝ, 0 < kappa' ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ,
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, X.TerminalSliceNoncollapsed kappa' := by
  obtain ⟨epsStar, hepsStar, hcyl⟩ :=
    exists_isParabolicallyRmControlled_of_isSpatiallyRmControlled_at_base
      (KappaSolutions.ancientKappa_modelCurvatureBoundNearBase.{u, 0, 0} (I := I3)
        (by simp [ThreeSpace]) hkappa)
  refine ⟨epsStar, hepsStar, fun Phi hPhi => ?_⟩
  obtain ⟨lam, hlam, hlam1, hshrink⟩ := hcyl Phi hPhi
  have hK : 0 < modelNoncollapseFactor * kappa := mul_pos modelNoncollapseFactor_pos hkappa
  have hK' : 0 < modelNoncollapseFactor * kappa * lam ^ 3 := mul_pos hK (pow_pos hlam 3)
  refine ⟨modelNoncollapseFactor * kappa * lam ^ 3, hK', ?_⟩
  intro eps heps hle sigma X
  have hsigma : 0 < sigma := pos_of_mul_pos_right (X.noncollapse 0).1 (Real.sqrt_nonneg _)
  refine ⟨hK', ?_⟩
  have hscale : ∀ᶠ i in atTop, 1 ≤ Real.sqrt (X.scale i) * sigma :=
    ((Real.tendsto_sqrt_atTop.comp X.scale_tendsto).atTop_mul_const hsigma).eventually_ge_atTop 1
  filter_upwards [hshrink eps heps hle sigma hsigma X, hscale] with i hi hsi
  intro time htime B hr hB
  have hBr := B.radius_pos
  have hsmall : (B.shrink lam hlam).radius ≤ Real.sqrt (X.scale i) * sigma := by
    change lam * B.radius ≤ _
    nlinarith
  have hB' := hi time htime B hr hB (B.shrink lam hlam) rfl le_rfl
  obtain ⟨-, hvol⟩ := (X.noncollapse i).2 time (B.shrink lam hlam) hsmall hB'
  have hnest := FlowMetricBall.volume_mono (FlowMetricBall.shrink_nested B hlam hlam1)
  refine ⟨hK', le_trans (le_of_eq ?_) (hvol.trans hnest)⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  change ENNReal.ofReal (modelNoncollapseFactor * kappa * lam ^ 3) *
      ENNReal.ofReal B.radius ^ Module.finrank ℝ ThreeSpace =
    ENNReal.ofReal (modelNoncollapseFactor * kappa) *
      ENNReal.ofReal (lam * B.radius) ^ Module.finrank ℝ ThreeSpace
  rw [hdim, ← ENNReal.ofReal_pow hBr.le, ← ENNReal.ofReal_pow (mul_pos hlam hBr).le,
    ← ENNReal.ofReal_mul hK'.le, ← ENNReal.ofReal_mul hK.le]
  congr 1
  ring

theorem NormalizedSequence.TerminalSliceNoncollapsed.eventually_metricNoncollapsed
    {eps kappa sigma kappa' : ℝ} {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : X.TerminalSliceNoncollapsed kappa') :
    ∀ᶠ i in atTop, MetricNoncollapsed ((X.term i).atTime 0) kappa' (Ioc 0 1) := by
  filter_upwards [h.2] with i hi
  intro y r hr hrpos hcurv
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  let B : FlowMetricBall (X.term i).S ⟨0, hzero⟩ := ⟨y, r, hrpos⟩
  have hB : B.IsSpatiallyRmControlled := hcurv
  have hvol := (hi ⟨0, hzero⟩ rfl B hr.2 hB).2
  rw [ENNReal.ofReal_mul' (pow_nonneg hrpos.le 3), ENNReal.ofReal_pow hrpos.le]
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  simp only [hdim, B, FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
    volumeMeasureOn_eq_metric, SolutionOn.family_metric, PointedFlowData.atTime,
    riemannianBallOf] at hvol ⊢
  with_unfolding_all exact hvol

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
