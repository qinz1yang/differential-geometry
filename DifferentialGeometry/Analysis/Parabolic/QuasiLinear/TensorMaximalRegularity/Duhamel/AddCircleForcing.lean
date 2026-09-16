import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleMultiplication
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivativeComposition
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleDifferentiation

noncomputable section

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

def parameterDerivativeParabolicForcing
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a b : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (f₀ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))
    (v : TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) : TensorHs g 0 0 0 :=
    let D := (parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)))
    let Dh := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))).comp
        ((parameterDerivativeHs g 2).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Q₁ := parameterSecondDerivativeHs g 1
    let Q₀ := parameterSecondDerivativeHs g 0
    let R := (parameterDerivativeHs g 1).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2))
    let L₀ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ)
    scalarH0ContinuousMul g (C a) (Z (Q₀ v)) +
      scalarH0ContinuousMul g (C (R v)) (Z (D a)) - Z (L₀ v) +
      (scalarH0ContinuousMul g (C a) (Z (Q₀ (Dh f₀))) +
        scalarH0ContinuousMul g (C (Q₁ f₀)) (Z (D a)) + Z (D b))

theorem parameterDerivative_parabolic_equation
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))
    (a b f : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    let D := (parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)))
    let Dh := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))).comp
        ((parameterDerivativeHs g 2).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Q₁ := parameterSecondDerivativeHs g 1
    let Q₀ := parameterSecondDerivativeHs g 0
    let R := (parameterDerivativeHs g 1).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2))
    let L₁ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
    let L₀ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ)
    L₁ u + f = scalarHsMul g 1 (by norm_num) a (Q₁ (f₀ + u)) + b →
      Z (D f + (D.comp L₁ - L₀.comp Dh) u) =
        scalarH0ContinuousMul g (C a) (Z (Q₀ (Dh u))) +
          scalarH0ContinuousMul g (C (R (Dh u))) (Z (D a)) - Z (L₀ (Dh u)) +
          (scalarH0ContinuousMul g (C a) (Z (Q₀ (Dh f₀))) +
            scalarH0ContinuousMul g (C (Q₁ f₀)) (Z (D a)) + Z (D b)) := by
  intro D Dh Z C Q₁ Q₀ R L₁ L₀ heq
  have hmul : Z (D (scalarHsMul g 1 (by norm_num) a (Q₁ (f₀ + u)))) =
      scalarH0ContinuousMul g (C a) (Z (D (Q₁ (f₀ + u)))) +
        scalarH0ContinuousMul g (C (Q₁ (f₀ + u))) (Z (D a)) :=
    parameterDerivativeHs_scalarHsMul g a (Q₁ (f₀ + u))
  have hcomm (v : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) :
      D (Q₁ v) = Q₀ (Dh v) :=
    parameterDerivativeHs_parameterSecondDerivativeHs g 0 v
  have hfirst : Q₁ u = R (Dh u) := by
    simp only [Q₁, R, Dh, parameterSecondDerivativeHs, ContinuousLinearMap.comp_apply]
    rw [← tensorHsInclusion_trans_apply]
  have h : Z (D (L₁ u)) + Z (D f) =
      Z (D (scalarHsMul g 1 (by norm_num) a (Q₁ (f₀ + u)))) + Z (D b) := by
    rw [← Z.map_add, ← D.map_add, heq, D.map_add, Z.map_add]
  rw [hmul, hcomm] at h
  simp only [map_add, add_apply] at h
  rw [hfirst] at h
  calc
    _ = Z (D (L₁ u)) + Z (D f) - Z (L₀ (Dh u)) := by
      simp only [sub_apply, ContinuousLinearMap.comp_apply, map_add, map_sub]
      abel
    _ = _ := by rw [h]; abel

end AddCircle


open MeasureTheory Filter Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TimeSobolev MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem compLpL_add_apply_ae
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {T : ℝ}
    (A : X →L[ℝ] Z) (B : Y →L[ℝ] Z) (F : timeL2 X T) (U : timeL2 Y T) :
    ∀ᵐ t ∂timeMeasure T,
      (A.compLpL 2 (timeMeasure T) F + B.compLpL 2 (timeMeasure T) U) t =
        A (F t) + B (U t) := by
  filter_upwards [Lp.coeFn_add (A.compLpL 2 (timeMeasure T) F)
    (B.compLpL 2 (timeMeasure T) U), A.coeFn_compLpL F, B.coeFn_compLpL U]
    with t ha hA hB
  rw [ha, Pi.add_apply, hA, hB]

private theorem parameterDerivativeDuhamelForcing_apply_ae
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T) :
    let D : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ)))) →L[ℝ] (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ)))) :=
      (AddCircle.parameterDerivativeHsPi (ι := ι) g n).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))))
    let Dh : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) →L[ℝ] (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) :=
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
      ((AddCircle.parameterDerivativeHsPi (ι := ι) g (n + 2)).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2))))
    let U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((n + 1 : ℕ) : ℝ)) hT 0 F
    let L₁ : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) →L[ℝ] (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ)))) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((n + 1 : ℕ) : ℝ))
    let L₀ : (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) →L[ℝ] (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ)))) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ))
    let G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T :=
      parameterDerivativeDuhamelForcing g n hT F
    ∀ᵐ t ∂timeMeasure T, G t =
      D (F t) + (D.comp L₁ - L₀.comp Dh) (U t) := by
  intro D Dh U L₁ L₀ G
  unfold G parameterDerivativeDuhamelForcing
  exact compLpL_add_apply_ae D (D.comp L₁ - L₀.comp Dh) F U

private theorem parameterDerivative_duhamel_vector_field_apply_ae
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T) :
    let Dh : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) →L[ℝ] (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) :=
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
      ((AddCircle.parameterDerivativeHsPi (ι := ι) g (n + 2)).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2))))
    let U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((n + 1 : ℕ) : ℝ)) hT 0 F
    let G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T :=
      parameterDerivativeDuhamelForcing g n hT F
    let V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
        (a := (n : ℝ)) hT 0 G
    ∀ᵐ t ∂timeMeasure T, Dh (U t) = V t := by
  intro Dh U G V
  have hV : Dh.compLpL 2 (timeMeasure T) U = V :=
    (parameterDerivative_duhamel_vector_eq g n hT F).1
  have h := Dh.coeFn_compLpL U
  rw [hV] at h
  exact h.symm

theorem parameterDerivativeDuhamelForcing_ae_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (a : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) :
    let Z : TensorHs g 0 0 ((0 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 0 :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let Q₁ := AddCircle.parameterSecondDerivativeHs g 1
    let L₁ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
    let U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 F
    let G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) T :=
      parameterDerivativeDuhamelForcing g 0 hT F
    let V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((0 : ℕ) : ℝ)) hT 0 G
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      L₁ (U t i) + F t i = scalarHsMul g 1 (by norm_num) (a t) (Q₁ (f₀ i + U t i)) + b t i) →
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      Z (G t i) = AddCircle.parameterDerivativeParabolicForcing g (a t) (b t i) (f₀ i) (V t i) := by
  intro Z Q₁ L₁ U G V heq
  let L₀ := tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ)
  let Dv : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) := (AddCircle.parameterDerivativeHsPi (ι := ι) g 0).comp
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ))))
  let Dhv : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ)))).comp
    ((AddCircle.parameterDerivativeHsPi g 2).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))))
  let L₁v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) := ContinuousLinearMap.piLpMap 2 (fun _ : ι => L₁)
  let L₀v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) := ContinuousLinearMap.piLpMap 2 (fun _ : ι => L₀)
  have hVa : ∀ᵐ t ∂timeMeasure T, Dhv (U t) = V t :=
    parameterDerivative_duhamel_vector_field_apply_ae g 0 hT F
  have hG : ∀ᵐ t ∂timeMeasure T,
      G t = Dv (F t) + (Dv.comp L₁v - L₀v.comp Dhv) (U t) :=
    parameterDerivativeDuhamelForcing_apply_ae g 0 hT F
  filter_upwards [heq, hG, hVa] with t ht hgt hvt
  intro i
  have hvti : Dhv (U t) i = V t i := congrArg (fun v => v i) hvt
  rw [hgt, ← hvti]
  exact AddCircle.parameterDerivative_parabolic_equation g (f₀ i) (U t i) (a t) (b t i)
    (F t i) (ht i)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
