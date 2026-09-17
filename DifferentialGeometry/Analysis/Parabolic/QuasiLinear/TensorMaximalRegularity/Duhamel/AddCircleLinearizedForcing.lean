import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcing
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0MultiplicationInclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0SmoothMultiplier
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacian

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
