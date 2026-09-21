import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Coefficients
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0MultiplicationInclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.FiniteProduct
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients

noncomputable section
open Set
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

abbrev GraphCircleHs (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (ι : Type*) (σ : ℝ) := PiLp 2 (fun _ : ι => TensorHs g 0 0 σ)

private def vectorCoordinateMultiplication
    {ι A X : Type*} [Fintype ι] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : A →L[ℝ] X →L[ℝ] X) :
    A →L[ℝ] PiLp 2 (fun _ : ι => X) →L[ℝ] PiLp 2 (fun _ : ι => X) :=
  LinearMap.mkContinuous
    { toFun := fun x => ContinuousLinearMap.piLpMap 2 (fun _ : ι => m x)
      map_add' := by
        intro x y
        ext v i
        simp only [ContinuousLinearMap.piLpMap_apply, map_add, add_apply, PiLp.add_apply]
      map_smul' := by
        intro c x
        ext v i
        simp only [ContinuousLinearMap.piLpMap_apply, map_smul, smul_apply, PiLp.smul_apply,
          RingHom.id_apply] }
    ‖m‖ (fun x => (ContinuousLinearMap.norm_piLpMap_le
      (fun _ : ι => m x) (norm_nonneg (m x)) (fun _ => le_rfl)).trans (m.le_opNorm x))

private def vectorHsCongr
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {σ τ : ℝ} (h : σ = τ) : GraphCircleHs g ι σ →L[ℝ] GraphCircleHs g ι τ :=
by
  let _ : Fintype ι := inferInstance
  exact ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsCongrL g 0 0 h)

noncomputable def graphDiffusionCoefficientContinuous
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (v : GraphCircleHs g (Fin n) 1) : C(AddCircle (1 : ℝ), ℝ) :=
  ⟨fun x => graphDiffusionCoefficient
      (WithLp.toLp 2 (fun i : Fin n =>
        DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous g (v i) x)) - 1, by
    have hv : Continuous (fun x : AddCircle (1 : ℝ) =>
        fun i : Fin n => DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous g (v i) x) :=
      continuous_pi (fun i => (DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous g (v i)).continuous)
    have hvlp : Continuous (fun x : AddCircle (1 : ℝ) =>
        WithLp.toLp 2 (fun i : Fin n => DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous g (v i) x)) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp hv
    exact (contDiff_graphDiffusionCoefficient (E := EuclideanSpace ℝ (Fin n))).continuous.comp hvlp |>.sub
      continuous_const⟩

def graphCurveShorteningN
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (reaction : ℝ → GraphCircleHs g (Fin n) 2 → GraphCircleHs g (Fin n) 1 → GraphCircleHs g (Fin n) 0)
    {R : ℝ} (t : ℝ)
    (u : {u : GraphCircleHs g (Fin n) 2 |
      ‖(ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (r := 0) (s := 0) (show (1 : ℝ) ≤ 2 by norm_num))) u‖ ≤ R}) :
    GraphCircleHs g (Fin n) 0 :=
  let u12 := vectorHsCongr g (ι := Fin n) (by norm_num : (2 : ℝ) = ((1 : ℕ) : ℝ) + 1) u.1
  let d1raw := AddCircle.parameterDerivativeHsPi g 1 u12
  let d1 := vectorHsCongr g (ι := Fin n) (by norm_num : ((1 : ℕ) : ℝ) = 1) d1raw
  let u02 := vectorHsCongr g (ι := Fin n) (by norm_num : (2 : ℝ) = ((0 : ℕ) : ℝ) + 2) u.1
  let qraw := AddCircle.parameterSecondDerivativeHsPi g 0 u02
  let q := vectorHsCongr g (ι := Fin n) (by norm_num : ((0 : ℕ) : ℝ) = 0) qraw
  vectorCoordinateMultiplication (ι := Fin n)
      (DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul g)
      (graphDiffusionCoefficientContinuous g d1) q + reaction t u.1 d1

theorem graphCurveShorteningN_zero
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (reaction : ℝ → GraphCircleHs g (Fin n) 2 → GraphCircleHs g (Fin n) 1 → GraphCircleHs g (Fin n) 0)
    {R : ℝ} (hR : 0 ≤ R) (t : ℝ) (hreaction : reaction t 0 = 0) :
    ‖graphCurveShorteningN g reaction (R := R) t
      ⟨0, by simpa using hR⟩‖ ≤ 0 := by
  have hd1 : vectorHsCongr g (ι := Fin n) (by norm_num : ((1 : ℕ) : ℝ) = 1)
      (AddCircle.parameterDerivativeHsPi g 1
        (vectorHsCongr g (ι := Fin n) (by norm_num : (2 : ℝ) = ((1 : ℕ) : ℝ) + 1)
          (0 : GraphCircleHs g (Fin n) 2))) = 0 := by simp [vectorHsCongr]
  have hq : vectorHsCongr g (ι := Fin n) (by norm_num : ((0 : ℕ) : ℝ) = 0)
      (AddCircle.parameterSecondDerivativeHsPi g 0
        (vectorHsCongr g (ι := Fin n) (by norm_num : (2 : ℝ) = ((0 : ℕ) : ℝ) + 2)
          (0 : GraphCircleHs g (Fin n) 2))) = 0 := by simp [vectorHsCongr]
  rw [graphCurveShorteningN, hd1, hq, map_zero, zero_add, hreaction]
  exact norm_zero.le

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
