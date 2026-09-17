import DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpOperators
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleMultiplicationInclusion
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedForcing

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι]

def parameterPrincipalOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
    ((ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι =>
        ((parameterSecondDerivativeHs g 1).precomp _).comp
          (scalarHsMul g 1 (by norm_num))))
      (a - ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g)))

def parameterDriftOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
    ((ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι =>
        ((parameterDerivativeHs g 1).precomp _).comp
          (scalarHsMul g 1 (by norm_num))))
      (parameterDerivativeHs g 1 a -
        ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g)))

def parameterPrincipalOperatorH0Pi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ)) :=
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    ((ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι =>
        (((Z.comp (parameterSecondDerivativeHs g 0)).precomp _).comp
          (scalarH0ContinuousMul g)).comp C))
      (a - ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g)))

def parameterDriftOperatorH0Pi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ)) :=
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    ((ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι =>
        (((Z.comp (parameterDerivativeHs g 0)).precomp _).comp
          (scalarH0ContinuousMul g)).comp C))
      (parameterDerivativeHs g 1 a -
        ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g)))

theorem tensorHsInclusion_parameterPrincipalOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) :
    (ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)))
      (parameterPrincipalOperatorHsPi g a v) =
    parameterPrincipalOperatorH0Pi g a
      ((ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2)) v) := by
  apply PiLp.ext
  intro i
  exact tensorHsInclusion_scalarHsMul_parameterSecondDerivativeHs g _ (v i)

theorem tensorHsInclusion_parameterDriftOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) :
    (ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)))
      (parameterDriftOperatorHsPi g a v) =
    parameterDriftOperatorH0Pi g a
      ((ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 1)) v) := by
  apply PiLp.ext
  intro i
  exact tensorHsInclusion_scalarHsMul_parameterDerivativeHs g _ (v i)

theorem memLp_parameterPrincipalOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} {a : Ω → TensorHs g 0 0 ((1 : ℕ) : ℝ)}
    (ha : MemLp a p μ) :
    MemLp (fun t => parameterPrincipalOperatorHsPi (ι := ι) g (a t)) p μ := by
  exact (ha.sub (memLp_const _)).continuousLinearMap_comp _

theorem memLp_parameterDriftOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} {a : Ω → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)}
    (ha : MemLp a p μ) :
    MemLp (fun t => parameterDriftOperatorHsPi (ι := ι) g (a t)) p μ := by
  exact ((ha.continuousLinearMap_comp (parameterDerivativeHs g 1)).sub
    (memLp_const _)).continuousLinearMap_comp _

theorem memLp_parameterPrincipalOperatorH0Pi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} {a : Ω → TensorHs g 0 0 ((1 : ℕ) : ℝ)}
    (ha : MemLp a p μ) :
    MemLp (fun t => parameterPrincipalOperatorH0Pi (ι := ι) g (a t)) p μ := by
  exact (ha.sub (memLp_const _)).continuousLinearMap_comp _

theorem memLp_parameterDriftOperatorH0Pi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} {a : Ω → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)}
    (ha : MemLp a p μ) :
    MemLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a t)) p μ := by
  exact ((ha.continuousLinearMap_comp (parameterDerivativeHs g 1)).sub
    (memLp_const _)).continuousLinearMap_comp _

theorem norm_parameterPrincipalOperatorHsPi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    ‖parameterPrincipalOperatorHsPi (ι := ι) g a‖ ≤
      ‖scalarHsMul g 1 (by norm_num)‖ *
        ‖a - ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))‖ *
          ‖parameterSecondDerivativeHs g 1‖ := by
  apply ContinuousLinearMap.norm_piLpMap_le _ (by positivity)
  intro i
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right ((scalarHsMul g 1 (by norm_num)).le_opNorm _)
      (norm_nonneg _))

theorem norm_parameterPrincipalOperatorH0Pi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    ‖parameterPrincipalOperatorH0Pi (ι := ι) g a‖ ≤
      ‖scalarH0ContinuousMul g‖ * (‖C‖ *
        ‖a - ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))‖) *
          ‖Z.comp (parameterSecondDerivativeHs g 0)‖ := by
  intro C Z
  apply ContinuousLinearMap.norm_piLpMap_le _ (by positivity)
  intro i
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact ((scalarH0ContinuousMul g).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (C.le_opNorm _) (norm_nonneg _))

theorem parameterDerivativeParabolicForcing_eq_operators
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a₂ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (b : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2))) :
    let a := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) a₂
    WithLp.toLp 2 (fun i => parameterDerivativeParabolicForcing g a (b i) (f₀ i) (v i)) =
      parameterPrincipalOperatorH0Pi g a v +
        parameterDriftOperatorH0Pi g a₂
          ((ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
            (g := g) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)) v) +
        WithLp.toLp 2 (fun i => parameterDerivativeParabolicForcing g a (b i) (f₀ i) 0) := by
  intro a
  let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  have hc (c : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯) :
      C (ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g c)) = ⟨c, c.2.continuous⟩ := by
    ext z
    simp only [C, ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs,
      scalarH1ToContinuous_apply_ccTensorToHs,
      DifferentialGeometry.Analysis.Sobolev.scalar0_scalarCc]
    rfl
  apply PiLp.ext
  intro i
  change parameterDerivativeParabolicForcing g a (b i) (f₀ i) (v i) =
    scalarH0ContinuousMul g (C (a - ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (laplacianPrincipalCoefficient g)))) _ +
    scalarH0ContinuousMul g (C (parameterDerivativeHs g 1 a₂ -
      ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g)))) _ +
    parameterDerivativeParabolicForcing g a (b i) (f₀ i) 0
  rw [C.map_sub, C.map_sub, hc, hc]
  exact parameterDerivativeParabolicForcing_eq_principal_add_drift g a₂ (b i) (f₀ i) (v i)

theorem parameterDriftOperatorH0Pi_smul_apply
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (c : ℝ)
    (a : TensorHs g 0 0 ((2 : ℕ) : ℝ))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((2 : ℕ) : ℝ))) :
    let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let D := (parameterDerivativeHs g 1).comp N
    let d : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianDriftCoefficient g, (laplacianDriftCoefficient g).2.continuous⟩
    parameterDriftOperatorH0Pi g (c • N a)
      ((ContinuousLinearMap.piLpMap 2 fun _ : ι => K) v) =
        WithLp.toLp 2 (fun i =>
          scalarH0ContinuousMul g (c • C (D a) - d) (Z (D (v i)))) := by
  intro N K Z C D d
  let Z₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let d₁ := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
  have hd : C d₁ = d := by
    ext x
    simp only [C, d₁, ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs,
      scalarH1ToContinuous_apply_ccTensorToHs,
      DifferentialGeometry.Analysis.Sobolev.scalar0_scalarCc]
    rfl
  have hder (w : TensorHs g 0 0 ((2 : ℕ) : ℝ)) :
      Z₀ (parameterDerivativeHs g 0 (K w)) = Z (D w) := by
    have h := congrArg Z₀
      (parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1) (N w))
    simpa only [Z₀, Z, D, K, N, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply] using h
  apply PiLp.ext
  intro i
  change scalarH0ContinuousMul g
    (C (parameterDerivativeHs g 1 (c • N a) - d₁))
      (Z₀ (parameterDerivativeHs g 0 (K (v i)))) = _
  rw [map_smul, C.map_sub, C.map_smul, hd, hder]
  rfl

end AddCircle
