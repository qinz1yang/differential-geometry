import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSourceCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_scalar_le_mul_scalar_of_modelCurvatureBound {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar D : ℝ, 0 < epsStar ∧ 0 < D ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ i : ℕ, ∀ t ∈ Set.Icc (-(X.depth i)) 0, ∀ x : (X.term i).M,
              2 ≤ (X.term i).S.scalar t x → ∀ y : (X.term i).M,
                riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) x y ≤
                  ENNReal.ofReal (1 / Real.sqrt ((X.term i).S.scalar t x)) →
                (X.term i).S.scalar t y ≤ D * (X.term i).S.scalar t x := by
  obtain ⟨K, hK, hmodel⟩ := hmod
  have hD : 0 < (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * sourceCurvatureBound 3 K := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    exact mul_pos (by rw [h3]; norm_num) (sourceCurvatureBound_pos 3 hK)
  refine ⟨1 / 4, (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * sourceCurvatureBound 3 K,
    by norm_num, hD, ?_⟩
  intro eps heps heps4 sigma hsigma Phi hPhi X i t ht x hx y hy
  obtain ⟨W, -⟩ := X.higher_good i t ht x hx
  have hQ : 0 < (X.term i).S.scalar t x := lt_of_lt_of_le (by norm_num) hx
  have hmodel' : ∀ s ∈ Set.Icc (-(4 : ℝ)) 0, ∀ z ∈ riemannianClosedBallOf (I := I3)
      (W.model.S.base.metric 0) W.model.basepoint 2,
      W.model.rmNormSq (I := I3) s z ≤ K ^ 2 := by
    intro s hs z hz
    exact hmodel W.model W.model_ancient W.model_scalar_base s hs z
      (riemannianClosedBallOf_mono (W.model.S.base.metric 0) W.model.basepoint
        (by norm_num : (2 : ℝ) ≤ 3) hz)
  obtain ⟨-, hbound⟩ := W.unitBall_compact_curvature_bound heps4 hK hmodel' (a := 0) (by norm_num)
  have hres : rescaledMetric (X.term i).S t ((X.term i).S.scalar t x) W.scalar_pos 0 =
      scaleMetric ((X.term i).S.scalar t x) W.scalar_pos ((X.term i).S.base.metric t) := by
    simp only [rescaledMetric, parabolicTime, zero_div, add_zero]
  have hy' : y ∈ riemannianClosedBallOf (I := I3)
      (rescaledMetric (X.term i).S t ((X.term i).S.scalar t x) W.scalar_pos 0) x 1 := by
    have hone : (1 : ℝ) = Real.sqrt ((X.term i).S.scalar t x) *
        (1 / Real.sqrt ((X.term i).S.scalar t x)) := by
      rw [mul_one_div, div_self (ne_of_gt (Real.sqrt_pos.mpr hQ))]
    rw [hres, hone, riemannianClosedBallOf_scaleMetric]
    exact hy
  have hbound' := hbound 0 (by norm_num) y hy'
  have hsq : Real.sqrt (normSq0S (I := I3)
      (rescaledMetric (X.term i).S t ((X.term i).S.scalar t x) W.scalar_pos 0) y 4
      (metricRm04At (I := I3)
        (rescaledMetric (X.term i).S t ((X.term i).S.scalar t x) W.scalar_pos 0) y)) ≤
      sourceCurvatureBound 3 K := by
    refine (Real.sqrt_le_sqrt hbound').trans_eq ?_
    exact Real.sqrt_sq (sourceCurvatureBound_pos 3 hK).le
  have hscal := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm (I := I3)
    (rescaledMetric (X.term i).S t ((X.term i).S.scalar t x) W.scalar_pos 0) y
  have hdim : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
  rw [hdim] at hscal
  have hscalarAt : metricScalarAt (I := I3)
      (rescaledMetric (X.term i).S t ((X.term i).S.scalar t x) W.scalar_pos 0) y =
      ((X.term i).S.scalar t x)⁻¹ * (X.term i).S.scalar t y := by
    rw [hres, metricScalarAt_scaleMetric]
    simp only [SolutionOn.scalar, SolutionFamily.scalar]
  rw [hscalarAt] at hscal
  have hkey : ((X.term i).S.scalar t x)⁻¹ * (X.term i).S.scalar t y ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * sourceCurvatureBound 3 K :=
    le_trans (le_abs_self _)
      (le_trans hscal (mul_le_mul_of_nonneg_left hsq (by positivity)))
  have hmul := mul_le_mul_of_nonneg_left hkey hQ.le
  rw [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul] at hmul
  calc (X.term i).S.scalar t y
      ≤ (X.term i).S.scalar t x *
          ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * sourceCurvatureBound 3 K) := hmul
    _ = ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * sourceCurvatureBound 3 K) *
          (X.term i).S.scalar t x := by ring


theorem exists_curvDerivNormSq_le_of_modelCurvatureBound {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar D : ℝ, 0 < epsStar ∧ 0 < D ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ i : ℕ, ∀ t ∈ Set.Icc (-(X.depth i)) 0, ∀ x : (X.term i).M,
              2 ≤ (X.term i).S.scalar t x → ∀ y : (X.term i).M,
                riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) x y ≤
                  ENNReal.ofReal (1 / Real.sqrt ((X.term i).S.scalar t x)) →
                curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤
                  (2 * (2 * Real.sqrt 3) *
                    (D * (X.term i).S.scalar t x / 4 +
                      rescalePinchingFunction (X.scale i) Phi
                        (D * (X.term i).S.scalar t x) +
                      rescalePinchingFunction (X.scale i) Phi 0)) ^ 2 := by
  obtain ⟨e, D, he, hD, hcmp⟩ :=
    exists_scalar_le_mul_scalar_of_modelCurvatureBound (kappa := kappa) hmod
  refine ⟨e, D, he, hD, ?_⟩
  intro eps heps heps4 sigma hsigma Phi hPhi X i t ht x hx y hy
  have hQ : 0 < (X.term i).S.scalar t x := lt_of_lt_of_le (by norm_num) hx
  have hP : 0 < D * (X.term i).S.scalar t x / 4 := by positivity
  have hquarter : 4 * (D * (X.term i).S.scalar t x / 4) = D * (X.term i).S.scalar t x := by
    ring
  have hub : (X.term i).S.scalar t y ≤ 4 * (D * (X.term i).S.scalar t x / 4) := by
    rw [hquarter]
    exact hcmp eps heps heps4 sigma hsigma Phi hPhi X i t ht x hx y hy
  have hbridge : RmNormBoundOn (X.term i).S (2 * Real.sqrt 3) := fun t w basis horth a ha =>
    sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le (X.term i).S t w basis horth ha
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hmem : t ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [ht.1, X.depth_pos i], ht.2⟩
  have hrm := sqrt_rmNormSq_le_of_scalar_le (I := I3) (by positivity) hbridge
    (hPhi.rescale (X.scale_pos i)) (X.pinching i) hdim hmem y hP hub
  rw [hquarter] at hrm
  have hcurv : FlowMetricBall.rmNormSq (X.term i).S t y =
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y := rfl
  rw [hcurv] at hrm
  exact (Real.sqrt_le_iff.mp hrm).2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
