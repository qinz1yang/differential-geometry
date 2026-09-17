import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcing
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0MultiplicationInclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0SmoothMultiplier
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacian
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleIteratedMultiplication
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleIteratedDifferentiation

noncomputable section

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem parameterDerivativeParabolicForcing_eq_principal_add_drift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a₂ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (b : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (f₀ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))
    (v : TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) :
    let a := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) a₂
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    let q : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianPrincipalCoefficient g, (laplacianPrincipalCoefficient g).2.continuous⟩
    let d : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianDriftCoefficient g, (laplacianDriftCoefficient g).2.continuous⟩
    parameterDerivativeParabolicForcing g a b f₀ v =
      scalarH0ContinuousMul g (C a - q) (Z (parameterSecondDerivativeHs g 0 v)) +
        scalarH0ContinuousMul g (C (parameterDerivativeHs g 1 a₂) - d)
          (Z (parameterDerivativeHs g 0 (J v))) +
        parameterDerivativeParabolicForcing g a b f₀ 0 := by
  intro a C Z J q d
  let D := (parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)))
  let R := (parameterDerivativeHs g 1).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2))
  let J₁₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
  have ha : Z (D a) = J₁₀ (parameterDerivativeHs g 1 a₂) := by
    simp only [D, a, ContinuousLinearMap.comp_apply]
    rw [← tensorHsInclusion_trans_apply,
      parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1)]
    exact (tensorHsInclusion_trans_apply _ _ _).symm
  have hv : J₁₀ (R v) = Z (parameterDerivativeHs g 0 (J v)) := by
    have h := parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1)
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2) v)
    rw [← tensorHsInclusion_trans_apply] at h
    change _ = Z (parameterDerivativeHs g 0 (J v))
    rw [h]
    exact tensorHsInclusion_trans_apply _ _ _
  have hcross : scalarH0ContinuousMul g (C (R v)) (Z (D a)) =
      scalarH0ContinuousMul g (C (parameterDerivativeHs g 1 a₂))
        (Z (parameterDerivativeHs g 0 (J v))) := by
    rw [ha, scalarH0ContinuousMul_scalarH1ToContinuous_comm, hv]
  have hL : Z (tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ) v) =
      scalarH0ContinuousMul g q (Z (parameterSecondDerivativeHs g 0 v)) +
        scalarH0ContinuousMul g d (Z (parameterDerivativeHs g 0 (J v))) := by
    rw [tensorScaleLaplacian_eq_principal_add_drift]
    simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]
    rw [tensorHsInclusion_appHs_scalarCc_zero, tensorHsInclusion_appHs_scalarCc_zero]
  have hf : parameterDerivativeParabolicForcing g a b f₀ v =
      scalarH0ContinuousMul g (C a) (Z (parameterSecondDerivativeHs g 0 v)) +
        scalarH0ContinuousMul g (C (R v)) (Z (D a)) -
          Z (tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ) v) +
        parameterDerivativeParabolicForcing g a b f₀ 0 := by
    simp only [parameterDerivativeParabolicForcing, map_zero, zero_apply,
      add_zero, zero_add, sub_zero, C, Z, R, D]
  rw [hf, hcross, hL]
  simp only [map_sub, sub_apply]
  abel


section
open DifferentialGeometry.Integral.L2

theorem parameterSecondDerivative_parabolic_equation
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ u : TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2))
    (a b f : TensorHs g 0 0 ((2 : ℕ) : ℝ)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let D := (parameterDerivativeHs g 1).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)))
    let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))
    let Z₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let Q := Z₀.comp ((parameterSecondDerivativeHs g 0).comp N)
    let Q₂ := parameterSecondDerivativeHs g 2
    let L₂ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
    let L₀ := Z₀.comp
      ((tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ)).comp N)
    let m := scalarH0ContinuousMul g
    let q : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianPrincipalCoefficient g, (laplacianPrincipalCoefficient g).2.continuous⟩
    let d : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianDriftCoefficient g, (laplacianDriftCoefficient g).2.continuous⟩
    L₂ u + f = scalarHsMul g 2 (by norm_num) a (Q₂ (f₀ + u)) + b →
      Q f + (Q.comp L₂ - L₀.comp Q₂) u =
        m (C (J a) - q) (Q (Q₂ u)) +
          m ((2 : ℝ) • C (D a) - d) (Z (D (Q₂ u))) +
          (m (C (J (Q₂ (f₀ + u)))) (Q a) +
            m (C (J a)) (Q (Q₂ f₀)) +
            (2 : ℝ) • m (C (D a)) (Z (D (Q₂ f₀))) + Q b) := by
  intro J Z C D N Z₀ Q Q₂ L₂ L₀ m q d heq
  have h := congrArg Q heq
  rw [map_add, map_add] at h
  have hmul := parameterSecondDerivativeHs_scalarHsMul g a (Q₂ (f₀ + u))
  change Q (scalarHsMul g 2 (by norm_num) a (Q₂ (f₀ + u))) =
    m (C (J a)) (Q (Q₂ (f₀ + u))) +
      (2 : ℝ) • m (C (D a)) (Z (D (Q₂ (f₀ + u)))) +
      m (C (J (Q₂ (f₀ + u)))) (Q a) at hmul
  rw [hmul] at h
  simp only [map_add, smul_add] at h
  have hv (v : TensorHs g 0 0 ((2 : ℕ) : ℝ)) :
      Z₀ (parameterDerivativeHs g 0 (tensorHsInclusion
        (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2) (N v))) =
          Z (D v) := by
    have h := parameterDerivativeHs_tensorHsInclusion g (by decide : 0 ≤ 1)
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)) v)
    have hh := congrArg Z₀ h
    simpa only [N, Z₀, Z, D, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply] using hh
  have hL : L₀ (Q₂ u) = m q (Q (Q₂ u)) + m d (Z (D (Q₂ u))) := by
    change Z₀ (tensorScaleLaplacian (g := g) (r := 0) (s := 0)
      ((0 : ℕ) : ℝ) (N (Q₂ u))) = _
    rw [tensorScaleLaplacian_eq_principal_add_drift]
    simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]
    rw [tensorHsInclusion_appHs_scalarCc_zero,
      tensorHsInclusion_appHs_scalarCc_zero, hv]
    rfl
  calc
    _ = Q (L₂ u) + Q f - L₀ (Q₂ u) := by
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      abel
    _ = _ := by
      rw [h, hL]
      simp only [map_add, add_apply, map_sub, sub_apply, map_smul, smul_apply]
      module

end

end AddCircle

open MeasureTheory Filter Set
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TimeSobolev MaximalRegularity
open DifferentialGeometry.Analysis.Spectral
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem parameterSecondDerivativeDuhamelForcing_ae_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((2 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a : ℝ → TensorHs g 0 0 ((2 : ℕ) : ℝ))
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((2 : ℕ) : ℝ))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let D := (AddCircle.parameterDerivativeHs g 1).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)))
    let Z₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) + 2)
    let Q := Z₀.comp ((AddCircle.parameterSecondDerivativeHs g 0).comp N)
    let Q₂ := AddCircle.parameterSecondDerivativeHs g 2
    let L₂ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
    let m := scalarH0ContinuousMul g
    let q : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨AddCircle.laplacianPrincipalCoefficient g,
        (AddCircle.laplacianPrincipalCoefficient g).2.continuous⟩
    let d : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨AddCircle.laplacianDriftCoefficient g,
        (AddCircle.laplacianDriftCoefficient g).2.continuous⟩
    let U := maximalRegularityDuhamelVectorField hT 0 F
    let G := parameterSecondDerivativeDuhamelForcing g 0 hT F
    let V := maximalRegularityDuhamelVectorField hT 0 G
    (∀ᵐ t ∂timeMeasure T, ∀ i, L₂ (U t i) + F t i =
      scalarHsMul g 2 (by norm_num) (a t) (Q₂ (f₀ i + U t i)) + b t i) →
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      Z₀ (G t i) = m (C (J (a t)) - q) (Q (B (V t i))) +
        m ((2 : ℝ) • C (D (a t)) - d) (Z (D (B (V t i)))) +
        (m (C (J (Q₂ (f₀ i + U t i)))) (Q (a t)) +
          m (C (J (a t))) (Q (Q₂ (f₀ i))) +
          (2 : ℝ) • m (C (D (a t))) (Z (D (Q₂ (f₀ i)))) + Q (b t i)) := by
  intro J Z C D Z₀ N B Q Q₂ L₂ m q d U G V heq
  let Dv := (AddCircle.parameterSecondDerivativeHsPi (ι := ι) g 0).comp
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => N))
  let Dh := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => N)).comp
    (AddCircle.parameterSecondDerivativeHsPi (ι := ι) g 2)
  let Lh := ContinuousLinearMap.piLpMap 2 (fun _ : ι => L₂)
  let Ll := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ))
  let L₀ := Z₀.comp ((tensorScaleLaplacian (g := g) (r := 0) (s := 0)
    ((0 : ℕ) : ℝ)).comp N)
  let K := Dv.comp Lh - Ll.comp Dh
  have hG : G = Dv.compLpL 2 (timeMeasure T) F + K.compLpL 2 (timeMeasure T) U := by
    rfl
  have hGa : ∀ᵐ t ∂timeMeasure T, G t = Dv (F t) + K (U t) := by
    filter_upwards [Lp.coeFn_add (Dv.compLpL 2 (timeMeasure T) F)
      (K.compLpL 2 (timeMeasure T) U), Dv.coeFn_compLpL F, K.coeFn_compLpL U]
      with t hadd hD hK
    rw [hG, hadd]
    change Dv.compLpL 2 (timeMeasure T) F t + K.compLpL 2 (timeMeasure T) U t = _
    rw [hD, hK]
  have hfield := (parameterSecondDerivative_duhamel_vector_eq g 0 hT F).1
  have hQa : ∀ᵐ t ∂timeMeasure T, Dh (U t) = V t := by
    change Dh.compLpL 2 (timeMeasure T) U = V at hfield
    have hh := Dh.coeFn_compLpL U
    rw [hfield] at hh
    exact hh.symm
  filter_upwards [heq, hGa, hQa] with t ht hgt hvt
  intro i
  have hi : Q₂ (U t i) = B (V t i) := by
    have h := congrArg B (congrArg (fun z => z i) hvt)
    simpa only [Dh, B, N, Q₂, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.piLpMap_apply, AddCircle.parameterSecondDerivativeHsPi_apply,
      ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply] using h
  have hGi : Z₀ (G t i) = Q (F t i) + (Q.comp L₂ - L₀.comp Q₂) (U t i) := by
    rw [hgt]
    simp only [Dv, K, Dh, Lh, Ll, L₀, Q, Q₂, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.piLpMap_apply, AddCircle.parameterSecondDerivativeHsPi_apply,
      sub_apply, PiLp.add_apply, PiLp.sub_apply, map_add, map_sub]
  rw [hGi, ← hi]
  exact AddCircle.parameterSecondDerivative_parabolic_equation g
    (f₀ i) (U t i) (a t) (b t i) (F t i) (ht i)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

noncomputable section
open scoped Manifold ContDiff
namespace AddCircle
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem tensorScaleLaplacian_h0_formula
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (v : TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) :
    let E₀ : TensorHs g 0 0 ((0 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 0 :=
      tensorHsInclusion (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let J₀ : TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2) →L[ℝ]
        TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1) :=
      tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    E₀ (tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ) v) =
      scalarH0ContinuousMul g
        ⟨laplacianPrincipalCoefficient g, (laplacianPrincipalCoefficient g).2.continuous⟩
        (E₀ (parameterSecondDerivativeHs g 0 v)) +
      scalarH0ContinuousMul g
        ⟨laplacianDriftCoefficient g, (laplacianDriftCoefficient g).2.continuous⟩
        (E₀ (parameterDerivativeHs g 0 (J₀ v))) := by
  intro E₀ J₀
  rw [tensorScaleLaplacian_eq_principal_add_drift g 0]
  change E₀ (appHs g 0 0 0
    (DifferentialGeometry.Analysis.Sobolev.scalarCc g (laplacianPrincipalCoefficient g))
    (parameterSecondDerivativeHs g 0 v) +
      appHs g 0 0 0 (DifferentialGeometry.Analysis.Sobolev.scalarCc g (laplacianDriftCoefficient g))
        (parameterDerivativeHs g 0 (J₀ v))) = _
  rw [map_add]
  exact congrArg₂ (· + ·)
    (tensorHsInclusion_appHs_scalarCc_zero g (laplacianPrincipalCoefficient g)
      (parameterSecondDerivativeHs g 0 v))
    (tensorHsInclusion_appHs_scalarCc_zero g (laplacianDriftCoefficient g)
      (parameterDerivativeHs g 0 (J₀ v)))

private theorem iteratedParameterDerivative_secondDerivative_normalized
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (w : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)) :
    let E₀ : TensorHs g 0 0 (((0 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let N : TensorHs g 0 0 (((2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))
    let D : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      E₀.comp ((iteratedParameterDerivativeHs g 0 (k + 2)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((0 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))))
    let Dh : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (((2 : ℕ) : ℝ)) :=
      (iteratedParameterDerivativeHs g 2 (k + 2)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((2 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2))
    let Qh : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)) :=
      parameterSecondDerivativeHs g (k + 2)
    let Q₀ : TensorHs g 0 0 (((2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      E₀.comp ((parameterSecondDerivativeHs g 0).comp N)
    D (Qh w) = Q₀ (Dh w) := by
  intro E₀ N D Dh Qh Q₀
  have hh := iteratedParameterDerivativeHs_parameterSecondDerivativeHs g 0 (k + 2)
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((0 + (k + 2) : ℕ) : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ) + 2) w)
  rw [parameterSecondDerivativeHs_tensorHsInclusion g
    (by omega : 0 + (k + 2) ≤ k + 2)] at hh
  have h := congrArg E₀ hh
  simpa only [E₀, N, D, Dh, Qh, Q₀, Nat.zero_add, ContinuousLinearMap.comp_apply,
    tensorHsInclusion_refl_apply, ← tensorHsInclusion_trans_apply] using h

private theorem iteratedParameterDerivative_firstDerivative_normalized
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (w : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)) :
    let E₀ : TensorHs g 0 0 (((0 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let N : TensorHs g 0 0 (((2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))
    let Dh : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (((2 : ℕ) : ℝ)) :=
      (iteratedParameterDerivativeHs g 2 (k + 2)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((2 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2))
    let Qh : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)) :=
      parameterSecondDerivativeHs g (k + 2)
    let W₁ : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (((1 : ℕ) : ℝ)) :=
      (iteratedParameterDerivativeHs g 1 (k + 1)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith : ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let Z : TensorHs g 0 0 (((1 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let J₀ : TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    let D₀ : TensorHs g 0 0 (((2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      E₀.comp ((parameterDerivativeHs g 0).comp (J₀.comp N))
    Z (W₁ (Qh w)) = D₀ (Dh w) := by
  intro E₀ N Dh Qh W₁ Z J₀ D₀
  let v : TensorHs g 0 0 ((1 + (k + 3) : ℕ) : ℝ) :=
    tensorHsInclusion (by push_cast; linarith :
      ((1 + (k + 3) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2) w
  let r : TensorHs g 0 0 ((0 + (k + 3) : ℕ) : ℝ) :=
    tensorHsInclusion (by push_cast; linarith :
      ((0 + (k + 3) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2) w
  let w₂ : TensorHs g 0 0 ((2 + (k + 2) : ℕ) : ℝ) :=
    tensorHsInclusion (by push_cast; linarith :
      ((2 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2) w
  have hleft : W₁ (Qh w) = iteratedParameterDerivativeHs g 1 (k + 3) v := by
    have hc := iteratedParameterDerivativeHs_parameterSecondDerivativeHs g 1 (k + 1)
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((1 + (k + 1) : ℕ) : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ) + 2) w)
    rw [parameterSecondDerivativeHs_tensorHsInclusion g
      (by omega : 1 + (k + 1) ≤ k + 2)] at hc
    have hs := parameterSecondDerivativeHs_iteratedParameterDerivativeHs g 1 (k + 1) v
    simp only [v, ← tensorHsInclusion_trans_apply] at hc hs
    simpa only [W₁, Qh, v, ContinuousLinearMap.comp_apply] using hc.trans hs
  have hproject : Z (iteratedParameterDerivativeHs g 1 (k + 3) v) =
      E₀ (iteratedParameterDerivativeHs g 0 (k + 3) r) := by
    have hi := iteratedParameterDerivativeHs_tensorHsInclusion g
      (by omega : 0 ≤ 1) (k + 3) v
    have h := congrArg E₀ hi.symm
    simpa only [E₀, Z, v, r, ← tensorHsInclusion_trans_apply] using h
  have hright : D₀ (Dh w) = E₀ (iteratedParameterDerivativeHs g 0 (k + 3) r) := by
    have hi := iteratedParameterDerivativeHs_tensorHsInclusion g
      (by omega : 1 ≤ 2) (k + 2) w₂
    have hi' := congrArg
      (fun z : TensorHs g 0 0 ((1 : ℕ) : ℝ) =>
        E₀ (parameterDerivativeHs g 0
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)) z))) hi
    have hd := congrArg E₀ (parameterDerivativeHs_iteratedParameterDerivativeHs g 0
      (k + 2) r)
    simp only [w₂, r, ← tensorHsInclusion_trans_apply] at hi' hd
    simpa only [D₀, J₀, N, Dh, r, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply] using hi'.symm.trans hd
  exact (congrArg Z hleft).trans (hproject.trans hright.symm)

theorem iteratedParameterDerivative_parabolic_equation
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f₀ u : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))
    (a : TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
    (b f : TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)) :
    let E₀ : TensorHs g 0 0 (((0 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let N : TensorHs g 0 0 (((2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))
    let D : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      E₀.comp ((iteratedParameterDerivativeHs g 0 (k + 2)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((0 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))))
    let Dh : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (((2 : ℕ) : ℝ)) :=
      (iteratedParameterDerivativeHs g 2 (k + 2)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((2 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2))
    let Qh : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)) :=
      parameterSecondDerivativeHs g (k + 2)
    let Q₀ : TensorHs g 0 0 (((2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      E₀.comp ((parameterSecondDerivativeHs g 0).comp N)
    let Lh : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)) :=
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ)
    let L₀ : TensorHs g 0 0 (((2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) := E₀.comp
      ((tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ)).comp N)
    let J : TensorHs g 0 0 (((k + 3 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
          ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A : TensorHs g 0 0 (((k + 3 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (((1 : ℕ) : ℝ)) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
          ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A₁ : TensorHs g 0 0 (((k + 3 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (((1 : ℕ) : ℝ)) :=
      (iteratedParameterDerivativeHs g 1 1).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
            ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
    let W₁ : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (((1 : ℕ) : ℝ)) :=
      (iteratedParameterDerivativeHs g 1 (k + 1)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith : ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let Ra : TensorHs g 0 0 (((k + 3 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (((1 + k + 2 : ℕ) : ℝ)) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((1 + k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let Rw : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (((1 + k : ℕ) : ℝ)) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 + k ≤ k + 2 by omega) :
          ((1 + k : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    let Z : TensorHs g 0 0 (((1 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let J₀ : TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    let D₀ : TensorHs g 0 0 (((2 : ℕ) : ℝ)) →L[ℝ] TensorHs g 0 0 (0) :=
      E₀.comp ((parameterDerivativeHs g 0).comp (J₀.comp N))
    let C : TensorHs g 0 0 (((1 : ℕ) : ℝ)) →L[ℝ] C(AddCircle (1 : ℝ), ℝ) :=
      (scalarH1ToContinuous g).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let m : C(AddCircle (1 : ℝ), ℝ) →L[ℝ] TensorHs g 0 0 (0) →L[ℝ] TensorHs g 0 0 (0) :=
      scalarH0ContinuousMul g
    let q : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianPrincipalCoefficient g, (laplacianPrincipalCoefficient g).2.continuous⟩
    let d : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianDriftCoefficient g, (laplacianDriftCoefficient g).2.continuous⟩
    Lh u + f = scalarHsMul g (k + 2) (by simp) (J a) (Qh (f₀ + u)) + b →
      D f + (D.comp Lh - L₀.comp Dh) u =
        m (C (A a) - q) (Q₀ (Dh u)) +
          m (((k + 2 : ℕ) : ℝ) • C (A₁ a) - d) (D₀ (Dh u)) +
          (Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
              (Ra a) (Rw (Qh (f₀ + u)))) +
            m (C (A a)) (D (Qh f₀)) +
              ((k + 2 : ℕ) : ℝ) • m (C (A₁ a)) (Z (W₁ (Qh f₀))) + D b) := by
  intro E₀ N D Dh Qh Q₀ Lh L₀ J A A₁ W₁ Ra Rw Z J₀ D₀ C m q d heq
  have hL (v : TensorHs g 0 0 ((2 : ℕ) : ℝ)) :
      L₀ v = m q (Q₀ v) + m d (D₀ v) := by
    simpa only [L₀, Q₀, D₀, m, q, d, ContinuousLinearMap.comp_apply] using
      tensorScaleLaplacian_h0_formula g (N v)
  have h := congrArg D heq
  rw [map_add, map_add] at h
  have hmul := iteratedParameterDerivativeHs_scalarHsMul_zero g k a (Qh (f₀ + u))
  change D (scalarHsMul g (k + 2) (by simp) (J a) (Qh (f₀ + u))) =
    Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
      (Ra a) (Rw (Qh (f₀ + u)))) +
      m (C (A a)) (D (Qh (f₀ + u))) +
        ((k + 2 : ℕ) : ℝ) • m (C (A₁ a)) (Z (W₁ (Qh (f₀ + u)))) at hmul
  rw [hmul] at h
  have hQ (w : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)) :
      D (Qh w) = Q₀ (Dh w) :=
    iteratedParameterDerivative_secondDerivative_normalized g k w
  have hD (w : TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)) :
      Z (W₁ (Qh w)) = D₀ (Dh w) :=
    iteratedParameterDerivative_firstDerivative_normalized g k w
  calc
    _ = D (Lh u) + D f - L₀ (Dh u) := by
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      abel
    _ = _ := by
      rw [h, hL]
      simp only [map_add, smul_add, hQ, hD, map_sub, sub_apply, map_smul, smul_apply]
      abel

end AddCircle
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TimeSobolev MaximalRegularity
open DifferentialGeometry.Analysis.Spectral
open AddCircle (iteratedParameterDerivativeHs parameterSecondDerivativeHs parameterDerivativeHs
  iteratedParameterDerivativeMulRemainderHs laplacianPrincipalCoefficient laplacianDriftCoefficient)
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem compLpL_add_ae_eq
    {α X Y Z : Type*} [MeasurableSpace α]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (μ : Measure α) (D : X →L[ℝ] Z) (K : Y →L[ℝ] Z)
    (F : Lp X 2 μ) (U : Lp Y 2 μ) :
    ∀ᵐ t ∂μ, (D.compLpL 2 μ F + K.compLpL 2 μ U) t = D (F t) + K (U t) := by
  filter_upwards [Lp.coeFn_add (D.compLpL 2 μ F) (K.compLpL 2 μ U),
    D.coeFn_compLpL F, K.coeFn_compLpL U] with t hadd hD hK
  exact hadd.trans (congrArg₂ (· + ·) hD hK)

private theorem compLpL_ae_eq_of_eq
    {α X Y : Type*} [MeasurableSpace α]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (μ : Measure α) (D : X →L[ℝ] Y) (U : Lp X 2 μ) (V : Lp Y 2 μ)
    (h : D.compLpL 2 μ U = V) :
    ∀ᵐ t ∂μ, D (U t) = V t := by
  filter_upwards [D.coeFn_compLpL U] with t ht
  exact ht.symm.trans (congrArg (fun z : Lp Y 2 μ => z t) h)

theorem iteratedParameterDerivativeDuhamelForcing_ae_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)))
    (a : ℝ → TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))) :
    let E₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) + 2)
    let D := E₀.comp ((iteratedParameterDerivativeHs g 0 (k + 2)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((0 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))))
    let Qh := parameterSecondDerivativeHs g (k + 2)
    let Q₀ := E₀.comp ((parameterSecondDerivativeHs g 0).comp N)
    let Lh := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ)
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
        ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A₁ := (iteratedParameterDerivativeHs g 1 1).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
          ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
    let W₁ := (iteratedParameterDerivativeHs g 1 (k + 1)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let Ra := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let Rw := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + k ≤ k + 2 by omega) :
        ((1 + k : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let J₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    let D₀ := E₀.comp ((parameterDerivativeHs g 0).comp (J₀.comp N))
    let C := (scalarH1ToContinuous g).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let m := scalarH0ContinuousMul g
    let q : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianPrincipalCoefficient g, (laplacianPrincipalCoefficient g).2.continuous⟩
    let d : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianDriftCoefficient g, (laplacianDriftCoefficient g).2.continuous⟩
    let U := maximalRegularityDuhamelVectorField hT 0 F
    let G := iteratedParameterDerivativeDuhamelForcing g 0 (k + 2) hT F
    let V := maximalRegularityDuhamelVectorField hT 0 G
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      Lh (U t i) + F t i = scalarHsMul g (k + 2) (by simp)
        (J (a t)) (Qh (f₀ i + U t i)) + b t i) →
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      E₀ (G t i) = m (C (A (a t)) - q) (Q₀ (B (V t i))) +
        m (((k + 2 : ℕ) : ℝ) • C (A₁ (a t)) - d) (D₀ (B (V t i))) +
        (Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
            (Ra (a t)) (Rw (Qh (f₀ i + U t i)))) +
          m (C (A (a t))) (D (Qh (f₀ i))) +
            ((k + 2 : ℕ) : ℝ) • m (C (A₁ (a t))) (Z (W₁ (Qh (f₀ i)))) + D (b t i)) := by
  intro E₀ N B D Qh Q₀ Lh J A A₁ W₁ Ra Rw Z J₀ D₀ C m q d U G V heq
  let Dh := (iteratedParameterDerivativeHs g 2 (k + 2)).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((2 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2))
  let L₀ := E₀.comp
    ((tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ)).comp N)
  let Ds : TensorHs g 0 0 ((k + 2 : ℕ) : ℝ) →L[ℝ]
      TensorHs g 0 0 ((0 : ℕ) : ℝ) :=
    (iteratedParameterDerivativeHs g 0 (k + 2)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((0 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
  let Dv : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ)))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ))) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => Ds)
  let Dhv : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => N.comp Dh)
  let Lhv : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ))) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => Lh)
  let Llv : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ))) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ))
  let K : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ))) :=
    Dv.comp Lhv - Llv.comp Dhv
  have hG : G = Dv.compLpL 2 (timeMeasure T) F + K.compLpL 2 (timeMeasure T) U := by
    rfl
  have hGa : ∀ᵐ t ∂timeMeasure T, G t = Dv (F t) + K (U t) := by
    simpa only [← hG] using compLpL_add_ae_eq (timeMeasure T) Dv K F U
  have hfield := (iteratedParameterDerivative_duhamel_vector_eq g 0 (k + 2) hT F).1
  change Dhv.compLpL 2 (timeMeasure T) U = V at hfield
  have hVa : ∀ᵐ t ∂timeMeasure T, Dhv (U t) = V t :=
    compLpL_ae_eq_of_eq (timeMeasure T) Dhv U V hfield
  filter_upwards [heq, hGa, hVa] with t ht hgt hvt
  intro i
  have hi : Dh (U t i) = B (V t i) := by
    have h := congrArg B (congrArg (fun z => z i) hvt)
    simpa only [Dhv, B, N, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.piLpMap_apply, ← tensorHsInclusion_trans_apply,
      tensorHsInclusion_refl_apply] using h
  have hGi : E₀ (G t i) = D (F t i) + (D.comp Lh - L₀.comp Dh) (U t i) := by
    rw [hgt]
    change E₀ (Ds (F t i) +
      (Ds (Lh (U t i)) - tensorScaleLaplacian (g := g) (r := 0) (s := 0)
        ((0 : ℕ) : ℝ) (N (Dh (U t i))))) =
      E₀ (Ds (F t i)) + (E₀ (Ds (Lh (U t i))) -
        E₀ (tensorScaleLaplacian (g := g) (r := 0) (s := 0)
          ((0 : ℕ) : ℝ) (N (Dh (U t i)))))
    rw [map_add, map_sub]
  have hs := AddCircle.iteratedParameterDerivative_parabolic_equation g k
    (f₀ i) (U t i) (a t) (b t i) (F t i) (ht i)
  let R := Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
      (Ra (a t)) (Rw (Qh (f₀ i + U t i)))) +
    m (C (A (a t))) (D (Qh (f₀ i))) +
      ((k + 2 : ℕ) : ℝ) • m (C (A₁ (a t))) (Z (W₁ (Qh (f₀ i)))) + D (b t i)
  exact hGi.trans (hs.trans (congrArg
    (fun z : TensorHs g 0 0 ((2 : ℕ) : ℝ) =>
      m (C (A (a t)) - q) (Q₀ z) +
        m (((k + 2 : ℕ) : ℝ) • C (A₁ (a t)) - d) (D₀ z) + R) hi))

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
