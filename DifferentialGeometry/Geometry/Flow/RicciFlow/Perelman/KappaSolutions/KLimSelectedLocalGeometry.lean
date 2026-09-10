import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimCurvatureBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance klimSelectedLocalTopology : TopologicalSpace F.M := F.topology
local instance klimSelectedLocalCharted : ChartedSpace H F.M := F.charted
local instance klimSelectedLocalSmooth : IsManifold I ∞ F.M := F.smooth
local instance klimSelectedLocalC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance klimSelectedLocalT2 : T2Space F.M := F.t2
local instance klimSelectedLocalSigma : SigmaCompactSpace F.M := F.sigmaCompact

variable {kappa : ℝ}

theorem terminalCurvatureNormalizedFlowSeq_klim_three_rmNormSq_bound
    (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    {s : ℝ} (hs : s ≤ 0) (z : F.M)
    (hz : (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
      z (x i)).toReal < r * Real.sqrt (F.S.scalar 0 (x i))) :
    ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).rmNormSq (I := I) s z ≤ 48 := by
  have h := terminalCurvatureNormalizedFlowSeq_three_rmNormSq_bound_mul
    F hK hdim x hQ i r 4 hlocal hs z hz
  norm_num at h ⊢
  exact h

theorem terminalCurvatureNormalizedFlowSeq_klim_three_smallBall_volume
    (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (y : F.M) (rho : ℝ) (hrho : 0 < rho) (hrhoQuarter : rho ≤ 1 / 4)
    (hdomain : riemannianBallOf (I := I)
        (scaleMetric (F.S.scalar 0 (x i)) (hQ i) (F.S.base.metric 0)) y rho ⊆
      {z : F.M | (riemannianEDistOf (I := I)
        (scaleMetric (F.S.scalar 0 (x i)) (hQ i) (F.S.base.metric 0)) z (x i)).toReal <
          r * Real.sqrt (F.S.scalar 0 (x i))}) :
    ENNReal.ofReal kappa * ENNReal.ofReal rho ^ 3 ≤
      riemannianVolumeMeasure (I := I) (M := F.M)
        (scaleMetric (F.S.scalar 0 (x i)) (hQ i) (F.S.base.metric 0))
        (riemannianBallOf (I := I)
          (scaleMetric (F.S.scalar 0 (x i)) (hQ i) (F.S.base.metric 0)) y rho) := by
  let S : SolutionOn (I := I) (M := F.M) ancientTimeInterval :=
    ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S
  let g0 : SmoothRiemannianMetric I F.M :=
    scaleMetric (F.S.scalar 0 (x i)) (hQ i) (F.S.base.metric 0)
  have hmetric : S.base.metric 0 = g0 :=
    terminalCurvatureNormalizedFlowSeq_metric F hK x hQ i
  let time : ancientTimeInterval.FlowTime := ⟨0, by simp⟩
  let B : FlowMetricBall S time := ⟨y, rho, hrho⟩
  have hset : B.set = riemannianBallOf (I := I) g0 y rho := by
    change {z : F.M | riemannianEDistOf (I := I) (S.base.metric 0) y z <
      ENNReal.ofReal rho} = _
    rw [hmetric]
    rfl
  have hcontrol : B.IsSpatiallyRmControlled := by
    intro z hz
    have hzball : z ∈ riemannianBallOf (I := I) g0 y rho := by
      rw [← hset]
      exact hz
    have hzdomain := hdomain hzball
    have hzterminal : (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
        z (x i)).toReal < r * Real.sqrt (F.S.scalar 0 (x i)) := by
      rw [terminalCurvatureNormalizedFlowSeq_metric]
      exact hzdomain
    have hRm := terminalCurvatureNormalizedFlowSeq_klim_three_rmNormSq_bound
      F hK hdim x hQ i r hlocal (s := 0) le_rfl z hzterminal
    have hpow : rho ^ 4 ≤ (1 / 4 : ℝ) ^ 4 :=
      pow_le_pow_left₀ hrho.le hrhoQuarter 4
    have hmul := mul_le_mul_of_nonneg_left hRm (pow_nonneg hrho.le 4)
    change rho ^ 4 *
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).rmNormSq (I := I) 0 z ≤ 1
    nlinarith
  have hvolume := (terminalCurvatureNormalizedFlowSeq_noncollapsed
    F hK x hQ i time B hcontrol).2
  change ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
    riemannianVolumeMeasure (I := I) (M := F.M) (S.base.metric 0) B.set at hvolume
  rw [hdim, hmetric, hset] at hvolume
  exact hvolume

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
