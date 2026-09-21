import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.TimeInterval
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
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
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
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

abbrev GraphState
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (R : ℝ) :=
  {u : GraphCircleHs g (Fin n) 2 |
    ‖(ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (r := 0) (s := 0) (show (1 : ℝ) ≤ 2 by norm_num))) u‖ ≤ R}

theorem graphDiffusionCoefficientContinuous_continuous
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    Continuous (graphDiffusionCoefficientContinuous g :
      GraphCircleHs g (Fin n) 1 → C(AddCircle (1 : ℝ), ℝ)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hpi : Continuous (fun p : GraphCircleHs g (Fin n) 1 × AddCircle (1 : ℝ) =>
      fun i : Fin n => DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous g
        (p.1 i) p.2) := by
    apply continuous_pi
    intro i
    have hi : Continuous (fun p : GraphCircleHs g (Fin n) 1 × AddCircle (1 : ℝ) => p.1 i) :=
      (PiLp.continuous_apply 2 (fun _ : Fin n => TensorHs g 0 0 1) i).comp continuous_fst
    have hc : Continuous (fun p : GraphCircleHs g (Fin n) 1 × AddCircle (1 : ℝ) =>
        DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous g (p.1 i)) :=
      (DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous g).continuous.comp hi
    exact continuous_eval.comp (hc.prodMk continuous_snd)
  have hto : Continuous (fun p : GraphCircleHs g (Fin n) 1 × AddCircle (1 : ℝ) =>
      WithLp.toLp 2 (fun i : Fin n => DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous g
        (p.1 i) p.2)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp hpi
  change Continuous (fun p : GraphCircleHs g (Fin n) 1 × AddCircle (1 : ℝ) =>
      graphDiffusionCoefficient (WithLp.toLp 2 (fun i : Fin n =>
        DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous g (p.1 i) p.2)) - 1)
  exact (contDiff_graphDiffusionCoefficient (E := EuclideanSpace ℝ (Fin n))).continuous.comp hto |>.sub
    continuous_const

theorem graphCurveShorteningN_continuous
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (reaction : ℝ → GraphCircleHs g (Fin n) 2 → GraphCircleHs g (Fin n) 1 → GraphCircleHs g (Fin n) 0)
    {R τ : ℝ}
    (hreaction : Continuous (fun p : ℝ × GraphCircleHs g (Fin n) 2 × GraphCircleHs g (Fin n) 1 =>
      reaction p.1 p.2.1 p.2.2)) :
    Continuous (fun p : Icc (0 : ℝ) τ × GraphState (n := n) g R =>
      graphCurveShorteningN g reaction p.1 p.2) := by
  let d1CLM : GraphCircleHs g (Fin n) 2 →L[ℝ] GraphCircleHs g (Fin n) 1 :=
    (vectorHsCongr g (ι := Fin n) (by norm_num : ((1 : ℕ) : ℝ) = 1)).comp
      ((AddCircle.parameterDerivativeHsPi g 1).comp
        (vectorHsCongr g (ι := Fin n) (by norm_num : (2 : ℝ) = ((1 : ℕ) : ℝ) + 1)))
  let qCLM : GraphCircleHs g (Fin n) 2 →L[ℝ] GraphCircleHs g (Fin n) 0 :=
    (vectorHsCongr g (ι := Fin n) (by norm_num : ((0 : ℕ) : ℝ) = 0)).comp
      ((AddCircle.parameterSecondDerivativeHsPi g 0).comp
        (vectorHsCongr g (ι := Fin n) (by norm_num : (2 : ℝ) = ((0 : ℕ) : ℝ) + 2)))
  let mulCLM := vectorCoordinateMultiplication (ι := Fin n)
      (DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul g)
  let P := Icc (0 : ℝ) τ × GraphState (n := n) g R
  let d1 : P → GraphCircleHs g (Fin n) 1 := fun p => d1CLM p.2.1
  let q : P → GraphCircleHs g (Fin n) 0 := fun p => qCLM p.2.1
  have hd1 : Continuous d1 := d1CLM.continuous.comp
    (continuous_subtype_val.comp continuous_snd)
  have hq : Continuous q := qCLM.continuous.comp
    (continuous_subtype_val.comp continuous_snd)
  have hcoef : Continuous (fun p : P => graphDiffusionCoefficientContinuous g (d1 p)) :=
    graphDiffusionCoefficientContinuous_continuous g |>.comp hd1
  have hmul : Continuous (fun p : P => mulCLM (graphDiffusionCoefficientContinuous g (d1 p)) (q p)) := by
    exact (mulCLM.continuous.comp hcoef).clm_apply hq
  have hmap : Continuous (fun p : P => ((p.1 : ℝ), ((p.2 : GraphCircleHs g (Fin n) 2), d1 p)) :
      P → ℝ × (GraphCircleHs g (Fin n) 2 × GraphCircleHs g (Fin n) 1)) := by
    exact (continuous_subtype_val.comp continuous_fst).prodMk ((continuous_subtype_val.comp continuous_snd).prodMk hd1)
  have hreactionP : Continuous (fun p : P => reaction (p.1 : ℝ) (p.2 : GraphCircleHs g (Fin n) 2) (d1 p)) := by
    have hh := hreaction.comp hmap
    convert hh using 1; rfl
  change Continuous (fun p : P => _)
  unfold graphCurveShorteningN
  convert hmul.add hreactionP using 1; rfl

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

theorem graphCurveShorteningN_timeNemyMeas
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (reaction : ℝ → GraphCircleHs g (Fin n) 2 → GraphCircleHs g (Fin n) 1 → GraphCircleHs g (Fin n) 0)
    {R τ : ℝ} (hR : 0 ≤ R)
    (hreaction : Continuous (fun p : ℝ × GraphCircleHs g (Fin n) 2 × GraphCircleHs g (Fin n) 1 =>
      reaction p.1 p.2.1 p.2.2)) :
    TimeNemyMeas
      (show (0 : GraphCircleHs g (Fin n) 2) ∈ GraphState (n := n) g R by
        simpa [GraphState] using hR)
      (fun t u => graphCurveShorteningN g reaction t u) τ := by
  apply timeNemy_of_contOn_Icc
  exact graphCurveShorteningN_continuous g reaction hreaction

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
