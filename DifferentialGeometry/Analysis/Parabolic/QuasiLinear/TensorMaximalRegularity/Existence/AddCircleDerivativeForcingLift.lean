import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleLinearizedLift
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleBaselineDependence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleResidualContinuity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleSourceContinuity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LinearTimeDependentStability
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleIteratedDerivativeSource
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleSecondDerivativeSource
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedForcing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedOperators
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.HeatTraceLift
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.AddCircleIteratedDerivativeContinuity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcingContinuity

open private vectorTensorHsNormedSpace from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LinearTimeDependentStability

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open AddCircle

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def scalarH0ToNatZeroPi
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ)))

private theorem norm_scalarH0ToNatZeroPi_le_one
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ‖scalarH0ToNatZeroPi (ι := ι) g‖ ≤ 1 := by
  exact ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
    (fun _ => tensorHsInclusion_opNorm_le_one _)

private def normalizedPrincipalOperator
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
  (scalarH0ToNatZeroPi g).comp (parameterPrincipalOperatorH0Pi (ι := ι) g a)

private def normalizedDriftOperator
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
  (scalarH0ToNatZeroPi g).comp (parameterDriftOperatorH0Pi (ι := ι) g a)

private theorem memLp_normalizedPrincipalOperator
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    {a : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ)}
    (ha : MemLp a 2 (timeMeasure T)) :
    MemLp (fun t => normalizedPrincipalOperator (ι := ι) g (a t)) 2 (timeMeasure T) := by
  have hraw : MemLp (fun t => parameterPrincipalOperatorH0Pi (ι := ι) g (a t))
      2 (timeMeasure T) := memLp_parameterPrincipalOperatorH0Pi g ha
  let L :
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ))) →L[ℝ]
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) :=
    (scalarH0ToNatZeroPi (ι := ι) g).postcomp
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)))
  exact hraw.continuousLinearMap_comp L

private theorem memLp_normalizedDriftOperator
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    {a : ℝ → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)}
    (ha : MemLp a 2 (timeMeasure T)) :
    MemLp (fun t => normalizedDriftOperator (ι := ι) g (a t)) 2 (timeMeasure T) := by
  have hraw : MemLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a t))
      2 (timeMeasure T) := memLp_parameterDriftOperatorH0Pi g ha
  let L :
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1)) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ))) →L[ℝ]
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1)) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) :=
    (scalarH0ToNatZeroPi (ι := ι) g).postcomp
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1)))
  exact hraw.continuousLinearMap_comp L

private theorem norm_normalizedPrincipalOperator_le
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    ‖normalizedPrincipalOperator (ι := ι) g a‖ ≤
      ‖parameterPrincipalOperatorH0Pi (ι := ι) g a‖ := by
  calc
    ‖normalizedPrincipalOperator (ι := ι) g a‖ ≤
        ‖scalarH0ToNatZeroPi (ι := ι) g‖ *
          ‖parameterPrincipalOperatorH0Pi (ι := ι) g a‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖parameterPrincipalOperatorH0Pi (ι := ι) g a‖ :=
      mul_le_mul_of_nonneg_right (norm_scalarH0ToNatZeroPi_le_one g) (norm_nonneg _)
    _ = ‖parameterPrincipalOperatorH0Pi (ι := ι) g a‖ := one_mul _

private theorem tensorHsInclusion_parameterPrincipalOperatorHsPi_normalized
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))))
        (parameterPrincipalOperatorHsPi g a v) =
      normalizedPrincipalOperator g a
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2))) v) := by
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  have h := congrArg (fun w => w i)
    (tensorHsInclusion_parameterPrincipalOperatorHsPi g a v)
  simpa only [normalizedPrincipalOperator, scalarH0ToNatZeroPi,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply,
    ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply] using h

private theorem tensorHsInclusion_parameterDriftOperatorHsPi_normalized
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))))
        (parameterDriftOperatorHsPi g a v) =
      normalizedDriftOperator g a
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 1))) v) := by
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  have h := congrArg (fun w => w i)
    (tensorHsInclusion_parameterDriftOperatorHsPi g a v)
  simpa only [normalizedDriftOperator, scalarH0ToNatZeroPi,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply,
    ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply] using h

private theorem parameterPrincipalOperatorH0Pi_eq_continuous_mul
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (w : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)))
    (a₁ : TensorHs g 0 0 ((1 : ℕ) : ℝ)) (i : ι) :
    let Z₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let B₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) + 2)
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Q := Z₀.comp ((parameterSecondDerivativeHs g 0).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))))
    parameterPrincipalOperatorH0Pi g a₁ w i =
      scalarH0ContinuousMul g
        (C a₁ - ⟨laplacianPrincipalCoefficient g,
          (laplacianPrincipalCoefficient g).2.continuous⟩) (Q (B₂ (w i))) := by
  intro Z₀ B₂ C Q
  have hq : C (ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (laplacianPrincipalCoefficient g))) =
      ⟨laplacianPrincipalCoefficient g,
        (laplacianPrincipalCoefficient g).2.continuous⟩ := by
    ext x
    simp only [C, ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs,
      scalarH1ToContinuous_apply_ccTensorToHs,
      DifferentialGeometry.Analysis.Sobolev.scalar0_scalarCc]
    rfl
  change scalarH0ContinuousMul g
    (C (a₁ - ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (laplacianPrincipalCoefficient g))))
        (Z₀ (parameterSecondDerivativeHs g 0 (w i))) = _
  rw [C.map_sub, hq]
  simp only [Q, B₂, ContinuousLinearMap.comp_apply,
    ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]

private theorem parameterDriftOperatorH0Pi_smul_eq_continuous_mul
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (c : ℝ)
    (w : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)))
    (a₂ : TensorHs g 0 0 ((2 : ℕ) : ℝ)) (i : ι) :
    let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
    let K₁ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    let Zr := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let B₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) + 2)
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let D := (parameterDerivativeHs g 1).comp N
    parameterDriftOperatorH0Pi g (c • N a₂)
      ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁)) w) i =
        scalarH0ContinuousMul g
          (c • C (D a₂) - ⟨laplacianDriftCoefficient g,
            (laplacianDriftCoefficient g).2.continuous⟩) (Zr (D (B₂ (w i)))) := by
  intro N K₁ Zr B₂ C D
  let K₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
  have hKw : (ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₂))
      ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => B₂)) w) =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁)) w := by
    apply PiLp.ext
    intro j
    simp only [K₂, K₁, B₂, ContinuousLinearMap.piLpMap_apply,
      ← tensorHsInclusion_trans_apply]
  have hh := congrArg (fun z => z i) (parameterDriftOperatorH0Pi_smul_apply g
    c a₂ ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => B₂)) w))
  change parameterDriftOperatorH0Pi g (c • N a₂)
    ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₂))
      ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => B₂)) w)) i = _ at hh
  rw [hKw] at hh
  simpa only [N, B₂, C, D, Zr, ContinuousLinearMap.piLpMap_apply,
    ContinuousLinearMap.comp_apply] using hh

private theorem exists_normalized_parameterDerivative_forcing_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (c : ℝ)
    {T : ℝ} (hT : 0 < T)
    (a₂ : ℝ → TensorHs g 0 0 ((2 : ℕ) : ℝ))
    (ham : MemLp a₂ 2 (timeMeasure T)) (C2h C2l : ℝ≥0)
    (G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) T)
    (R : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
    let K₁ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorHsPi (ι := ι) g (J (a₂ t))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorH0Pi (ι := ι) g (J (a₂ t))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    (∀ᵐ t ∂timeMeasure T,
      G t = normalizedPrincipalOperator g (J (a₂ t)) (heatDuhamelVectorField hT 0 G t) +
        normalizedDriftOperator g (c • N (a₂ t))
          ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁))
            (heatDuhamelVectorField hT 0 G t)) + J₀.compLpL 2 (timeMeasure T) R t) →
    ∃ FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      G = J₀.compLpL 2 (timeMeasure T) FH := by
  intro J N K₁ Z J₀ hC2h hC2l hC2hlt hC2llt hfLeq
  let R₀ := J₀.compLpL 2 (timeMeasure T) R
  let A2h : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((((1 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
    fun t => parameterPrincipalOperatorHsPi (ι := ι) g (J (a₂ t))
  let A2l : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((((0 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
    fun t => normalizedPrincipalOperator (ι := ι) g (J (a₂ t))
  let A1h : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((((1 : ℕ) : ℝ) + 1))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
    fun t => parameterDriftOperatorHsPi (ι := ι) g (c • N (a₂ t))
  let A1l : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((((0 : ℕ) : ℝ) + 1))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
    fun t => normalizedDriftOperator (ι := ι) g (c • N (a₂ t))
  have hA2h : AEStronglyMeasurable A2h (timeMeasure T) :=
    (memLp_parameterPrincipalOperatorHsPi g (ham.continuousLinearMap_comp J)).aestronglyMeasurable
  have hA2l : AEStronglyMeasurable A2l (timeMeasure T) :=
    (memLp_normalizedPrincipalOperator g (ham.continuousLinearMap_comp J)).aestronglyMeasurable
  have hA1h : MemLp A1h 2 (timeMeasure T) :=
    memLp_parameterDriftOperatorHsPi g ((ham.continuousLinearMap_comp N).const_smul c)
  have hA1l : MemLp A1l 2 (timeMeasure T) :=
    memLp_normalizedDriftOperator g ((ham.continuousLinearMap_comp N).const_smul c)
  have hC2l' : ∀ᵐ t ∂timeMeasure T, ‖A2l t‖ ≤ C2l := by
    filter_upwards [hC2l] with t ht
    exact (norm_normalizedPrincipalOperator_le g (J (a₂ t))).trans ht
  have hc := tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  refine exists_heat_vector_forcing_lift_of_l2_coefficients
    (ι := ι) (E := ℝ) (H := ℝ) (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
    (g := g) (r := 0) (s := 0) (a := ((0 : ℕ) : ℝ)) (b := ((1 : ℕ) : ℝ))
    (by norm_num) hT hc 0 G A2h hA2h C2h hC2h A1h hA1h R
    A2l hA2l C2l hC2l' A1l hA1l R₀ ?_ ?_ rfl hfLeq hC2hlt hC2llt 0 ?_
  · exact Eventually.of_forall fun t x =>
      tensorHsInclusion_parameterPrincipalOperatorHsPi_normalized g (J (a₂ t)) x
  · exact Eventually.of_forall fun t x =>
      tensorHsInclusion_parameterDriftOperatorHsPi_normalized g (c • N (a₂ t)) x
  · exact (map_zero _).symm

private theorem exists_iteratedParameterDerivative_source_forcing_equation
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
    (hW : ContinuousOn W (Icc 0 T))
    (a : timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (bHigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)))
    :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let U := maximalRegularityDuhamelVectorField hT 0 F
    (∀ᵐ t ∂timeMeasure T, ∀ i, J (bHigh t i) = b t i) →
    (∀ᵐ t ∂timeMeasure T, ∀ i, W t i = K (U t i)) →
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U t i) +
        F t i = scalarHsMul g (k + 2) (by simp) (J (a t))
          (parameterSecondDerivativeHs g (k + 2) (P (f₀ i) + U t i)) + b t i) →
    let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
    let K₁ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let Qlow := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ))).comp
        ((parameterSecondDerivativeHs g (k + 1)).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ))))
    let G := iteratedParameterDerivativeDuhamelForcing g 0 (k + 2) hT F
    ∃ R : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      (∀ᵐ t ∂timeMeasure T, ∀ i,
        R t i = iteratedParameterDerivativeSourceHs g k (f₀ i) (a t) (bHigh t i)
          (Qlow (B (f₀ i) + W t i))) ∧
      ∀ᵐ t ∂timeMeasure T,
        G t = normalizedPrincipalOperator g (A (a t))
            (heatDuhamelVectorField hT 0 G t) +
          normalizedDriftOperator g (((k + 2 : ℕ) : ℝ) • N (a t))
            ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁))
              (heatDuhamelVectorField hT 0 G t)) +
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL 2 (timeMeasure T) R t := by
  intro J A P K Z U hb hWU heq Nout Kout Bout Qout Gout
  let H₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast (show 2 ≤ k + 3 by omega) :
      ((2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let a₂ : ℝ → TensorHs g 0 0 ((2 : ℕ) : ℝ) := fun t => H₂ (a t)
  let J₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
  let N₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
  let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
  let A₁ := (iteratedParameterDerivativeHs g 1 1).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
        ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let K₁ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
  let E₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let B₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
  let B₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((2 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) + 2)
  let E₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))
  let Zr := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
  let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
    (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Q := E₀.comp ((parameterSecondDerivativeHs g 0).comp E₂)
  let D := (parameterDerivativeHs g 1).comp N₂
  let D₀ := E₀.comp ((parameterDerivativeHs g 0).comp (K₁.comp E₂))
  have hEB (x : TensorHs g 0 0 (0 : ℝ)) : E₀ (B₀ x) = x := by
    simp only [E₀, B₀, ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
  have hEZ (x : TensorHs g 0 0 ((1 : ℕ) : ℝ)) : E₀ (Z x) = Zr x := by
    simp only [E₀, Z, Zr, ← tensorHsInclusion_trans_apply]
  have hJA (t : ℝ) : J₂ (a₂ t) = A (a t) := by
    simp only [J₂, a₂, H₂, A, ← tensorHsInclusion_trans_apply]
  have hNA (t : ℝ) : N₂ (a₂ t) = N (a t) := by
    simp only [N₂, a₂, H₂, N, ← tensorHsInclusion_trans_apply]
  have hfirst (x : TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) :
      A₁ x = parameterDerivativeHs g 1 (N x) := by
    simp only [A₁, N, iteratedParameterDerivativeHs, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ← tensorHsInclusion_trans_apply]
  have hDA (t : ℝ) : D (a₂ t) = A₁ (a t) := by
    simp only [D, ContinuousLinearMap.comp_apply, hNA, hfirst]
  have hD₀ (w : TensorHs g 0 0 ((2 : ℕ) : ℝ)) : D₀ w = Zr (D w) := by
    have hh := congrArg E₀
      (parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1) (N₂ w))
    simpa only [D₀, D, E₀, E₂, K₁, N₂, Zr, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply] using hh
  obtain ⟨R, hres⟩ := exists_timeL2_tensorHsInclusion_eq_iteratedParameterDerivativeSource
    g k f₀ a bHigh b W hW U hb hWU
  let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)
  let R₀ := J₀.compLpL 2 (timeMeasure T) R
  let G := iteratedParameterDerivativeDuhamelForcing g 0 (k + 2) hT F
  let V := maximalRegularityDuhamelVectorField hT 0 G
  let A2l : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
    fun t => normalizedPrincipalOperator g (J₂ (a₂ t))
  let A1l : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
    fun t => normalizedDriftOperator g (((k + 2 : ℕ) : ℝ) • N₂ (a₂ t))
  have hc := tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  have hlow := iteratedParameterDerivativeDuhamelForcing_ae_eq
    g k hT F ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => P)) f₀) a b heq
  have hheat : heatDuhamelVectorField hT 0 G = V := by
    simpa only [map_zero] using heatDuhamelVectorField_inclusion hT hc 0 G
  have hprincipal (w : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)))
      (a₁ : TensorHs g 0 0 ((1 : ℕ) : ℝ)) (i : ι) :
      parameterPrincipalOperatorH0Pi g a₁ w i =
        scalarH0ContinuousMul g
          (C a₁ - ⟨laplacianPrincipalCoefficient g,
            (laplacianPrincipalCoefficient g).2.continuous⟩) (Q (B₂ (w i))) :=
    parameterPrincipalOperatorH0Pi_eq_continuous_mul g w a₁ i
  have hdrift (w : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)))
      (t : ℝ) (i : ι) :
      parameterDriftOperatorH0Pi g (((k + 2 : ℕ) : ℝ) • N₂ (a₂ t))
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁)) w) i =
          scalarH0ContinuousMul g
            (((k + 2 : ℕ) : ℝ) • C (D (a₂ t)) - ⟨laplacianDriftCoefficient g,
              (laplacianDriftCoefficient g).2.continuous⟩) (Zr (D (B₂ (w i)))) :=
    parameterDriftOperatorH0Pi_smul_eq_continuous_mul g ((k + 2 : ℕ) : ℝ) w (a₂ t) i
  have hfLeq : ∀ᵐ t ∂timeMeasure T,
      G t = A2l t (heatDuhamelVectorField hT 0 G t) +
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁))
          (heatDuhamelVectorField hT 0 G t)) + R₀ t := by
    filter_upwards [hlow, hres, J₀.coeFn_compLpL R] with t hlt hrt hRt
    rw [hheat, hRt]
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    change E₀ (G t i) = E₀ (B₀ (parameterPrincipalOperatorH0Pi g (J₂ (a₂ t)) (V t) i) +
      B₀ (parameterDriftOperatorH0Pi g (((k + 2 : ℕ) : ℝ) • N₂ (a₂ t))
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁)) (V t)) i) + Z (R t i))
    rw [map_add, map_add, hEB, hEB, hEZ, hprincipal, hdrift, hJA, hDA, hrt i, ← hD₀]
    exact hlt i
  refine ⟨R, ?_, ?_⟩
  · exact iteratedParameterDerivativeSourceHs_ae_eq_of_projection
      g k f₀ a bHigh b W U R hb hWU hres
  · simpa only [A2l, A1l, hJA, hNA] using hfLeq

theorem exists_iteratedParameterDerivative_forcing_lift_of_principal_norm_lt_one
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
    (hW : ContinuousOn W (Icc 0 T))
    (a : timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (bHigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)))
    (C2h C2l : ℝ≥0) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let U := maximalRegularityDuhamelVectorField hT 0 F
    (∀ᵐ t ∂timeMeasure T, ∀ i, J (bHigh t i) = b t i) →
    (∀ᵐ t ∂timeMeasure T, ∀ i, W t i = K (U t i)) →
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U t i) +
        F t i = scalarHsMul g (k + 2) (by simp) (J (a t))
          (parameterSecondDerivativeHs g (k + 2) (P (f₀ i) + U t i)) + b t i) →
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorHsPi (ι := ι) g (A (a t))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorH0Pi (ι := ι) g (A (a t))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    ∃ FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      iteratedParameterDerivativeDuhamelForcing g 0 (k + 2) hT F =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL 2 (timeMeasure T) FH := by
  intro J A P K Z U hb hWU heq hC2h hC2l hC2hlt hC2llt
  obtain ⟨R, _, hfLeq⟩ := exists_iteratedParameterDerivative_source_forcing_equation
    g k hT F f₀ W hW a bHigh b hb hWU heq
  let H₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast (show 2 ≤ k + 3 by omega) :
      ((2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let a₂ : ℝ → TensorHs g 0 0 ((2 : ℕ) : ℝ) := fun t => H₂ (a t)
  let J₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
  let N₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
  let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
  have hJA (t : ℝ) : J₂ (a₂ t) = A (a t) := by
    simp only [J₂, a₂, H₂, A, ← tensorHsInclusion_trans_apply]
  have hNA (t : ℝ) : N₂ (a₂ t) = N (a t) := by
    simp only [N₂, a₂, H₂, N, ← tensorHsInclusion_trans_apply]
  have ham : MemLp a₂ 2 (timeMeasure T) := (Lp.memLp a).continuousLinearMap_comp H₂
  apply exists_normalized_parameterDerivative_forcing_lift g ((k + 2 : ℕ) : ℝ) hT
    a₂ ham C2h C2l (iteratedParameterDerivativeDuhamelForcing g 0 (k + 2) hT F) R
  · change ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (J₂ (a₂ t))‖ ≤ C2h
    simpa only [hJA] using hC2h
  · change ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := ι) g (J₂ (a₂ t))‖ ≤ C2l
    simpa only [hJA] using hC2l
  · exact hC2hlt
  · exact hC2llt
  · simpa only [a₂, H₂, ← tensorHsInclusion_trans_apply] using hfLeq

theorem exists_parameterSecondDerivative_forcing_lift_of_principal_norm_lt_one
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((2 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((3 : ℕ) : ℝ) + 2)))
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (hW : ContinuousOn W (Icc 0 T))
    (aHigh : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) T)
    (bHigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T)
    (a : ℝ → TensorHs g 0 0 ((2 : ℕ) : ℝ))
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((2 : ℕ) : ℝ)))
    (C2h C2l : ℝ≥0) :
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let U := maximalRegularityDuhamelVectorField hT 0 F
    (fun t => A (aHigh t)) =ᵐ[timeMeasure T] a →
    (∀ᵐ t ∂timeMeasure T, ∀ i, A (bHigh t i) = b t i) →
    (∀ᵐ t ∂timeMeasure T, ∀ i, W t i = K (U t i)) →
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((2 : ℕ) : ℝ) (U t i) + F t i =
        scalarHsMul g 2 (by norm_num) (a t)
          (parameterSecondDerivativeHs g 2 (P (f₀ i) + U t i)) + b t i) →
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorHsPi (ι := ι) g (J (a t))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorH0Pi (ι := ι) g (J (a t))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    ∃ FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      parameterSecondDerivativeDuhamelForcing g 0 hT F =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL 2 (timeMeasure T) FH := by
  intro A P K J Z U ha hb hWU heq hC2h hC2l hC2hlt hC2llt
  let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ) + 2)
  let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
  let K₁ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
  let Z₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let E₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
  let Zr := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
  let B₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((2 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) + 2)
  have hZE (x : TensorHs g 0 0 (0 : ℝ)) : Z₀ (E₀ x) = x := by
    simp only [Z₀, E₀, ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
  let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
    (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Q := Z₀.comp ((parameterSecondDerivativeHs g 0).comp (tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))))
  let D := (parameterDerivativeHs g 1).comp N
  let v := fun t => (parameterSecondDerivativeHsPi (ι := ι) g 1)
    ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => B)) f₀ + W t)
  have hv : ContinuousOn v (Icc 0 T) :=
    (parameterSecondDerivativeHsPi (ι := ι) g 1).continuous.comp_continuousOn
      (continuousOn_const.add hW)
  let R := parameterSecondDerivativeSourceTimeL2 g f₀ aHigh bHigh hv
  let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)
  let R₀ := J₀.compLpL 2 (timeMeasure T) R
  let G := parameterSecondDerivativeDuhamelForcing g 0 hT F
  let V := maximalRegularityDuhamelVectorField hT 0 G
  let A2l : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((((0 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
    fun t => normalizedPrincipalOperator (ι := ι) g (J (a t))
  let A1l : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((((0 : ℕ) : ℝ) + 1))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
    fun t => normalizedDriftOperator (ι := ι) g ((2 : ℝ) • N (a t))
  have ham : MemLp a 2 (timeMeasure T) :=
    ((Lp.memLp aHigh).continuousLinearMap_comp A).ae_eq ha
  have hc := tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  have hres := tensorHsInclusion_parameterSecondDerivativeSourceTimeL2_ae_eq
    g f₀ aHigh bHigh hv a b W U ha hb hWU
      (Eventually.of_forall (fun _ _ => rfl))
  have hlow := parameterSecondDerivativeDuhamelForcing_ae_eq
    g hT F ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => P)) f₀) a b heq
  have hheat : heatDuhamelVectorField hT 0 G = V := by
    simpa only [map_zero] using heatDuhamelVectorField_inclusion hT hc 0 G
  have hprincipal (w : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)))
      (a₁ : TensorHs g 0 0 ((1 : ℕ) : ℝ)) (i : ι) :
      parameterPrincipalOperatorH0Pi g a₁ w i =
        scalarH0ContinuousMul g
          (C a₁ - ⟨laplacianPrincipalCoefficient g,
            (laplacianPrincipalCoefficient g).2.continuous⟩) (Q (B₂ (w i))) :=
    parameterPrincipalOperatorH0Pi_eq_continuous_mul g w a₁ i
  have hdrift (w : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)))
      (t : ℝ) (i : ι) :
      parameterDriftOperatorH0Pi g ((2 : ℝ) • N (a t))
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁)) w) i =
          scalarH0ContinuousMul g
            ((2 : ℝ) • C (D (a t)) - ⟨laplacianDriftCoefficient g,
              (laplacianDriftCoefficient g).2.continuous⟩) (Zr (D (B₂ (w i)))) :=
    parameterDriftOperatorH0Pi_smul_eq_continuous_mul g (2 : ℝ) w (a t) i
  have hfLeq : ∀ᵐ t ∂timeMeasure T,
      G t = A2l t (heatDuhamelVectorField hT 0 G t) +
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁))
          (heatDuhamelVectorField hT 0 G t)) + R₀ t := by
    filter_upwards [hlow, hres, J₀.coeFn_compLpL R] with t hlt hrt hRt
    rw [hheat, hRt]
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    change Z₀ (G t i) = Z₀ (E₀ (parameterPrincipalOperatorH0Pi g (J (a t)) (V t) i) +
      E₀ (parameterDriftOperatorH0Pi g ((2 : ℝ) • N (a t))
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁)) (V t)) i) + Z (R t i))
    rw [map_add, map_add, hZE, hZE, hprincipal, hdrift]
    have hZR : Z₀ (Z (R t i)) = Zr (R t i) := by
      simp only [Z₀, Z, Zr, ← tensorHsInclusion_trans_apply]
    rw [hZR, hrt i]
    exact hlt i
  exact exists_normalized_parameterDerivative_forcing_lift g (2 : ℝ) hT a ham C2h C2l G R
    hC2h hC2l hC2hlt hC2llt hfLeq


section ResidualSource

attribute [local instance] vectorTensorHsNormedSpace

private abbrev circleResidualCore
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (q : ℝ) {T : ℝ} :=
  @heatVectorForcingResidualL ι (by infer_instance)
      ℝ Real.normedAddCommGroup (@InnerProductSpace.toNormedSpace ℝ ℝ Real.instRCLike
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup ℝ
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing ℝ
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing ℝ
              (@NormedCommRing.toSeminormedCommRing ℝ Real.normedCommRing))))
        (@RCLike.toInnerProductSpaceReal ℝ Real.instRCLike))
      (@FiniteDimensional.rclike_to_real ℝ Real.instRCLike) (by infer_instance)
      ℝ (@UniformSpace.toTopologicalSpace ℝ
        (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
      (𝓘(ℝ, ℝ)) (AddCircle (1 : ℝ))
      (@QuotientAddGroup.instTopologicalSpace ℝ
        (@UniformSpace.toTopologicalSpace ℝ
          (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
        Real.instAddGroup
        (@AddSubgroup.zmultiples ℝ
          Real.instAddGroup (1 : ℝ)))
      (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
      (by infer_instance) (by infer_instance) g 0 0 q T


private abbrev circleResidualInclusionCore
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T) :=
  @heatVectorForcingResidualL_eq_iff_tensorHsInclusion ι (by infer_instance)
      ℝ Real.normedAddCommGroup (@InnerProductSpace.toNormedSpace ℝ ℝ Real.instRCLike
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup ℝ
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing ℝ
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing ℝ
              (@NormedCommRing.toSeminormedCommRing ℝ Real.normedCommRing))))
        (@RCLike.toInnerProductSpaceReal ℝ Real.instRCLike))
      (@FiniteDimensional.rclike_to_real ℝ Real.instRCLike) (by infer_instance)
      ℝ (@UniformSpace.toTopologicalSpace ℝ
        (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
      (𝓘(ℝ, ℝ)) (AddCircle (1 : ℝ))
      (@QuotientAddGroup.instTopologicalSpace ℝ
        (@UniformSpace.toTopologicalSpace ℝ
          (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
        Real.instAddGroup
        (@AddSubgroup.zmultiples ℝ
          Real.instAddGroup (1 : ℝ)))
      (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
      (by infer_instance) (by infer_instance) g 0 0 ((0 : ℕ) : ℝ) T ((1 : ℕ) : ℝ)
      (by norm_num) hT
      (tensorResolventL2_isCompactOperator (I := 𝓘(ℝ, ℝ))
        (M := AddCircle (1 : ℝ)) g 0 0)


section ResidualInclusion

variable {ι : Type*} [Fintype ι]
variable (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
variable {T : ℝ} (hT : 0 < T)
variable (a : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
variable (b : ℝ → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
variable (ha : MemLp a 2 (timeMeasure T)) (hb : MemLp b 2 (timeMeasure T))
variable (Ch Cl : ℝ≥0)
variable (hCh : ∀ᵐ t ∂timeMeasure T,
  ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a t)‖ ≤ Ch)
variable (hCl : ∀ᵐ t ∂timeMeasure T,
  ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (a t)‖ ≤ Cl)

include hCl in
private theorem normalized_principal_bound :
    ∀ᵐ t ∂timeMeasure T, ‖normalizedPrincipalOperator (ι := ι) g (a t)‖ ≤ Cl := by
  filter_upwards [hCl] with t ht
  exact (norm_normalizedPrincipalOperator_le (ι := ι) g (a t)).trans ht

private abbrev circleResidualHigh :=
  circleResidualCore (ι := ι) g ((1 : ℕ) : ℝ) hT
    (fun t => AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a t))
    (AddCircle.memLp_parameterPrincipalOperatorHsPi (ι := ι) g ha).aestronglyMeasurable
    Ch hCh (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g (b t))
    (AddCircle.memLp_parameterDriftOperatorHsPi (ι := ι) g hb)

private abbrev circleResidualLow :=
  circleResidualCore (ι := ι) g ((0 : ℕ) : ℝ) hT
    (fun t => normalizedPrincipalOperator (ι := ι) g (a t))
    (memLp_normalizedPrincipalOperator (ι := ι) g ha).aestronglyMeasurable
    Cl (normalized_principal_bound g a Cl hCl)
    (fun t => normalizedDriftOperator (ι := ι) g (b t))
    (memLp_normalizedDriftOperator (ι := ι) g hb)

private abbrev circleResidualInclusionHigh :=
  circleResidualInclusionCore (ι := ι) g hT
    (fun t => AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a t))
    (AddCircle.memLp_parameterPrincipalOperatorHsPi (ι := ι) g ha).aestronglyMeasurable
    Ch hCh (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g (b t))
    (AddCircle.memLp_parameterDriftOperatorHsPi (ι := ι) g hb)

private abbrev circleResidualInclusionLow :=
  circleResidualInclusionHigh g hT a b ha hb Ch hCh
    (fun t => normalizedPrincipalOperator (ι := ι) g (a t))
    (memLp_normalizedPrincipalOperator (ι := ι) g ha).aestronglyMeasurable
    Cl (normalized_principal_bound g a Cl hCl)
    (fun t => normalizedDriftOperator (ι := ι) g (b t))
    (memLp_normalizedDriftOperator (ι := ι) g hb)

private abbrev circleResidualInclusionCompatibility :=
  circleResidualInclusionLow g hT a b ha hb Ch Cl hCh hCl
    (Eventually.of_forall fun t v =>
      tensorHsInclusion_parameterPrincipalOperatorHsPi_normalized g (a t) v)
    (Eventually.of_forall fun t v =>
      tensorHsInclusion_parameterDriftOperatorHsPi_normalized g (b t) v)

variable (FH R : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)

private abbrev circleResidualInclusionAt :=
  circleResidualInclusionCompatibility g hT a b ha hb Ch Cl hCh hCl FH R

private theorem parameterDerivative_forcing_residual_eq_iff_inclusion :
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let J := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL 2 (timeMeasure T)
    circleResidualHigh g hT a b ha hb Ch hCh FH = R ↔
      circleResidualLow g hT a b ha hb Cl hCl (J FH) = J R := by
  with_reducible exact circleResidualInclusionAt g hT a b ha hb Ch Cl hCh hCl FH R

end ResidualInclusion

private abbrev circleResidualHeatCore
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T) :=
  @heatVectorForcingResidualL_eq_iff_heat ι (by infer_instance)
      ℝ Real.normedAddCommGroup (@InnerProductSpace.toNormedSpace ℝ ℝ Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup ℝ Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal ℝ Real.instRCLike))
      (@FiniteDimensional.rclike_to_real ℝ Real.instRCLike) (by infer_instance)
      ℝ (@UniformSpace.toTopologicalSpace ℝ
        (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
      (𝓘(ℝ, ℝ)) (AddCircle (1 : ℝ))
      (@QuotientAddGroup.instTopologicalSpace ℝ
        (@UniformSpace.toTopologicalSpace ℝ
          (@PseudoMetricSpace.toUniformSpace ℝ (@SeminormedAddCommGroup.toPseudoMetricSpace ℝ
          (@NormedAddCommGroup.toSeminormedAddCommGroup ℝ Real.normedAddCommGroup))))
        (@AddCommGroup.toAddGroup ℝ Real.instAddCommGroup)
        (@AddSubgroup.zmultiples ℝ
          (@AddCommGroup.toAddGroup ℝ Real.instAddCommGroup) (1 : ℝ)))
      (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
      (by infer_instance) (by infer_instance) g 0 0 ((0 : ℕ) : ℝ) T hT
      (tensorResolventL2_isCompactOperator (I := 𝓘(ℝ, ℝ))
        (M := AddCircle (1 : ℝ)) g 0 0)


section ResidualHeat

variable {ι : Type*} [Fintype ι]
variable (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
variable {T : ℝ} (hT : 0 < T)
variable (a : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
variable (b : ℝ → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
variable (ha : MemLp a 2 (timeMeasure T)) (hb : MemLp b 2 (timeMeasure T))
variable (Cl : ℝ≥0)
variable (hCl : ∀ᵐ t ∂timeMeasure T,
  ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (a t)‖ ≤ Cl)

private abbrev normalizedPrincipalResidualHeatIff :=
  circleResidualHeatCore (ι := ι) g hT
    (fun t => normalizedPrincipalOperator (ι := ι) g (a t))
    (memLp_normalizedPrincipalOperator (ι := ι) g ha).aestronglyMeasurable
    Cl (normalized_principal_bound g a Cl hCl)

private abbrev normalizedResidualHeatIff :=
  normalizedPrincipalResidualHeatIff g hT a ha Cl hCl
    (fun t => normalizedDriftOperator (ι := ι) g (b t))
    (memLp_normalizedDriftOperator (ι := ι) g hb)

variable (G R : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) T)

private abbrev normalizedResidualHeatAt :=
  normalizedResidualHeatIff g hT a b ha hb Cl hCl G R

private abbrev normalizedResidualHeatBackward :=
  (normalizedResidualHeatAt g hT a b ha hb Cl hCl G R).mpr

variable (heq : ∀ᵐ t ∂timeMeasure T,
      G t = normalizedPrincipalOperator g (a t) (heatDuhamelVectorField hT 0 G t) +
        normalizedDriftOperator g (b t)
          ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)))
            (heatDuhamelVectorField hT 0 G t)) + R t)

private abbrev normalizedResidualHeatValue :=
  normalizedResidualHeatBackward g hT a b ha hb Cl hCl G R (by
    filter_upwards [heq] with t ht
    with_reducible exact ht)

include heq in
private theorem normalized_residual_eq_of_heat :
    circleResidualLow g hT a b ha hb Cl hCl G = R := by
  with_reducible exact normalizedResidualHeatValue g hT a b ha hb Cl hCl G R heq

end ResidualHeat

private theorem parameterDerivative_forcing_residual_eq_of_inclusion
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (a : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (b : ℝ → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (ha : MemLp a 2 (timeMeasure T)) (hb : MemLp b 2 (timeMeasure T))
    (C2h C2l : ℝ≥0)
    (G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) T)
    (FH R : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T) :
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)
    let K₁ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    ∀ (hC2h : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (a t)‖ ≤ C2h), (∀ᵐ t ∂timeMeasure T,
        ‖parameterPrincipalOperatorH0Pi (ι := ι) g (a t)‖ ≤ C2l) →
    G = J₀.compLpL 2 (timeMeasure T) FH →
    (∀ᵐ t ∂timeMeasure T,
      G t = normalizedPrincipalOperator g (a t) (heatDuhamelVectorField hT 0 G t) +
        normalizedDriftOperator g (b t)
          ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁))
            (heatDuhamelVectorField hT 0 G t)) + J₀.compLpL 2 (timeMeasure T) R t) →
    circleResidualHigh g hT a b ha hb C2h hC2h FH = R := by
  intro Z J₀ K₁ hC2h hC2l hlift hRlow
  have hlow := normalized_residual_eq_of_heat g hT a b ha hb C2l hC2l
    G (J₀.compLpL 2 (timeMeasure T) R) hRlow
  apply (parameterDerivative_forcing_residual_eq_iff_inclusion
    g hT a b ha hb C2h C2l hC2h hC2l FH R).mpr
  change circleResidualLow g hT a b ha hb C2l hC2l
    (J₀.compLpL 2 (timeMeasure T) FH) = J₀.compLpL 2 (timeMeasure T) R
  rw [← hlift]
  exact hlow

section

variable {ι : Type*} [Fintype ι]
variable (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
variable {T : ℝ} (hT : 0 < T)
variable (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))) T)
variable (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
variable (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
variable (hW : ContinuousOn W (Icc 0 T))
variable (a : timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
variable (bHigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
variable (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)))
variable (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
variable (C2h C2l : ℝ≥0)

include hW

theorem heatVectorForcingResidualL_iteratedParameterDerivative_lift_ae_eq :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let U := maximalRegularityDuhamelVectorField hT 0 F
    (∀ᵐ t ∂timeMeasure T, ∀ i, J (bHigh t i) = b t i) →
    (∀ᵐ t ∂timeMeasure T, ∀ i, W t i = K (U t i)) →
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U t i) +
        F t i = scalarHsMul g (k + 2) (by simp) (J (a t))
          (parameterSecondDerivativeHs g (k + 2) (P (f₀ i) + U t i)) + b t i) →
    ∀ (hC2h : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (A (a t))‖ ≤ C2h), (∀ᵐ t ∂timeMeasure T,
        ‖parameterPrincipalOperatorH0Pi (ι := ι) g (A (a t))‖ ≤ C2l) →
    iteratedParameterDerivativeDuhamelForcing g 0 (k + 2) hT F =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL 2 (timeMeasure T) FH →
    let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
    let aH := fun t => A (a t)
    let bH := fun t => ((k + 2 : ℕ) : ℝ) • N (a t)
    let haH := (Lp.memLp a).continuousLinearMap_comp A
    let hbH := ((Lp.memLp a).continuousLinearMap_comp N).const_smul ((k + 2 : ℕ) : ℝ)
    let R := circleResidualHigh g hT aH bH haH hbH C2h hC2h FH
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let Qlow := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ))).comp
        ((parameterSecondDerivativeHs g (k + 1)).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ))))
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      R t i = iteratedParameterDerivativeSourceHs g k (f₀ i) (a t) (bHigh t i)
        (Qlow (B (f₀ i) + W t i)) := by
  intro J A P K Z U hb hWU heq hC2h hC2l hlift N aH bH haH hbH Rtarget B Qlow
  obtain ⟨R, hRsource, hRlow⟩ := exists_iteratedParameterDerivative_source_forcing_equation
    g k hT F f₀ W hW a bHigh b hb hWU heq
  have hhigh := parameterDerivative_forcing_residual_eq_of_inclusion g hT
    aH bH haH hbH C2h C2l
    (iteratedParameterDerivativeDuhamelForcing g 0 (k + 2) hT F) FH R
    hC2h hC2l hlift hRlow
  change ∀ᵐ t ∂timeMeasure T, ∀ i,
    (circleResidualHigh g hT aH bH haH hbH C2h hC2h FH) t i = _
  rw [hhigh]
  exact hRsource

end

end ResidualSource

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal Topology
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open AddCircle
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
attribute [local instance] vectorTensorHsNormedSpace

private abbrev referenceForcingStabilityCore
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T) :=
  @tendsto_heat_vector_forcing_of_tendsto_residual ι (by infer_instance)
      ℝ Real.normedAddCommGroup (@InnerProductSpace.toNormedSpace ℝ ℝ Real.instRCLike
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup ℝ
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing ℝ
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing ℝ
              (@NormedCommRing.toSeminormedCommRing ℝ Real.normedCommRing))))
        (@RCLike.toInnerProductSpaceReal ℝ Real.instRCLike))
      (@FiniteDimensional.rclike_to_real ℝ Real.instRCLike) (by infer_instance)
      ℝ (@UniformSpace.toTopologicalSpace ℝ
        (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
      (𝓘(ℝ, ℝ)) (AddCircle (1 : ℝ))
      (@QuotientAddGroup.instTopologicalSpace ℝ
        (@UniformSpace.toTopologicalSpace ℝ
          (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
        Real.instAddGroup
        (@AddSubgroup.zmultiples ℝ
          Real.instAddGroup (1 : ℝ)))
      (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
      (by infer_instance) (by infer_instance) g 0 0 ((0 : ℕ) : ℝ) T ((1 : ℕ) : ℝ) X l
      (by norm_num) hT
      (tensorResolventL2_isCompactOperator (I := 𝓘(ℝ, ℝ))
        (M := AddCircle (1 : ℝ)) g 0 0)


section

variable
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (a : X → ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (b : X → ℝ → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (ha : ∀ x, MemLp (a x) 2 (timeMeasure T))
    (hb : ∀ x, MemLp (b x) 2 (timeMeasure T))
    (Ch Cl : X → ℝ≥0)
    (hCh : ∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (a x t)‖ ≤ Ch x)
    (hCl : ∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := ι) g (a x t)‖ ≤ Cl x)
    (hChlt : (Ch x₀ : ℝ) < 1) (hCllt : (Cl x₀ : ℝ) < 1)
    (FH : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)

private abbrev referenceStabilityHigh :=
  referenceForcingStabilityCore (l := l) (ι := ι) g hT
    (fun t => parameterPrincipalOperatorHsPi g (a x₀ t))
    (memLp_parameterPrincipalOperatorHsPi g (ha x₀)).aestronglyMeasurable
    (Ch x₀) (hCh x₀)
    (fun t => parameterDriftOperatorHsPi g (b x₀ t))
    (memLp_parameterDriftOperatorHsPi g (hb x₀))

private abbrev referenceStabilityLow :=
  referenceStabilityHigh (l := l) g hT x₀ a b ha hb Ch hCh
    (fun t => normalizedPrincipalOperator g (a x₀ t))
    (memLp_normalizedPrincipalOperator g (ha x₀)).aestronglyMeasurable
    (Cl x₀) (normalized_principal_bound g (a x₀) (Cl x₀) (hCl x₀))
    (fun t => normalizedDriftOperator g (b x₀ t))
    (memLp_normalizedDriftOperator g (hb x₀))

private abbrev referenceStabilityCompatibility :=
  referenceStabilityLow (l := l) g hT x₀ a b ha hb Ch Cl hCh hCl
    (Eventually.of_forall fun t v =>
      tensorHsInclusion_parameterPrincipalOperatorHsPi_normalized g (a x₀ t) v)
    (Eventually.of_forall fun t v =>
      tensorHsInclusion_parameterDriftOperatorHsPi_normalized g (b x₀ t) v)
    hChlt hCllt

private abbrev referenceStabilityFamily :=
  referenceStabilityCompatibility (l := l) g hT x₀ a b ha hb Ch Cl hCh hCl hChlt hCllt
    (fun x t => parameterPrincipalOperatorHsPi g (a x t))
    (fun x => (memLp_parameterPrincipalOperatorHsPi g (ha x)).aestronglyMeasurable)
    Ch hCh (fun x t => parameterDriftOperatorHsPi g (b x t))
    (fun x => memLp_parameterDriftOperatorHsPi g (hb x))
    (FH x₀) FH

include hCl hChlt hCllt in
private theorem reference_forcing_tendsto_of_residual :
    let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Q := fun x => circleResidualHigh (ι := ι) g hT (a x) (b x) (ha x) (hb x) (Ch x) (hCh x)
    Tendsto Q l (𝓝 (Q x₀)) →
    Tendsto (fun x => J₀.compLpL 2 (timeMeasure T) (FH x)) l
      (𝓝 (J₀.compLpL 2 (timeMeasure T) (FH x₀))) →
    Tendsto (fun x => Q x (FH x)) l (𝓝 (Q x₀ (FH x₀))) →
    Tendsto FH l (𝓝 (FH x₀)) := by
  intro J₀ Q hQ hF hR
  exact referenceStabilityFamily (l := l) g hT x₀ a b ha hb Ch Cl hCh hCl hChlt hCllt FH hQ hF hR

end

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal Topology
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TimeSobolev
open DifferentialGeometry.Analysis.Spectral
open AddCircle
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
attribute [local instance] vectorTensorHsNormedSpace

private abbrev referenceResidualCongrCore
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T) :=
  @heatVectorForcingResidualL_congr_ae ι (by infer_instance)
      ℝ Real.normedAddCommGroup (@InnerProductSpace.toNormedSpace ℝ ℝ Real.instRCLike
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup ℝ
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing ℝ
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing ℝ
              (@NormedCommRing.toSeminormedCommRing ℝ Real.normedCommRing))))
        (@RCLike.toInnerProductSpaceReal ℝ Real.instRCLike))
      (@FiniteDimensional.rclike_to_real ℝ Real.instRCLike) (by infer_instance)
      ℝ (@UniformSpace.toTopologicalSpace ℝ
        (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
      (𝓘(ℝ, ℝ)) (AddCircle (1 : ℝ))
      (@QuotientAddGroup.instTopologicalSpace ℝ
        (@UniformSpace.toTopologicalSpace ℝ
          (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
        Real.instAddGroup
        (@AddSubgroup.zmultiples ℝ
          Real.instAddGroup (1 : ℝ)))
      (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
      (by infer_instance) (by infer_instance) g 0 0 ((1 : ℕ) : ℝ) T hT


section ResidualCongruence

variable {ι : Type*} [Fintype ι]
variable (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
variable {T : ℝ} (hT : 0 < T)
variable (a₁ a₂ : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
variable (b₁ b₂ : ℝ → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
variable (ha₁ : MemLp a₁ 2 (timeMeasure T)) (ha₂ : MemLp a₂ 2 (timeMeasure T))
variable (hb₁ : MemLp b₁ 2 (timeMeasure T)) (hb₂ : MemLp b₂ 2 (timeMeasure T))
variable (C₁ C₂ : ℝ≥0)
variable (hC₁ : ∀ᵐ t ∂timeMeasure T,
  ‖parameterPrincipalOperatorHsPi (ι := ι) g (a₁ t)‖ ≤ C₁)
variable (hC₂ : ∀ᵐ t ∂timeMeasure T,
  ‖parameterPrincipalOperatorHsPi (ι := ι) g (a₂ t)‖ ≤ C₂)
variable (hae : a₁ =ᵐ[timeMeasure T] a₂) (hbe : b₁ =ᵐ[timeMeasure T] b₂)

private abbrev referenceResidualCongrPrincipal :=
  referenceResidualCongrCore (ι := ι) g hT
    (fun t => parameterPrincipalOperatorHsPi (ι := ι) g (a₁ t))
    (fun t => parameterPrincipalOperatorHsPi (ι := ι) g (a₂ t))
    (memLp_parameterPrincipalOperatorHsPi (ι := ι) g ha₁).aestronglyMeasurable
    (memLp_parameterPrincipalOperatorHsPi (ι := ι) g ha₂).aestronglyMeasurable
    C₁ C₂ hC₁ hC₂

private abbrev referenceResidualCongrDrift :=
  referenceResidualCongrPrincipal g hT a₁ a₂ ha₁ ha₂ C₁ C₂ hC₁ hC₂
    (fun t => parameterDriftOperatorHsPi (ι := ι) g (b₁ t))
    (fun t => parameterDriftOperatorHsPi (ι := ι) g (b₂ t))
    (memLp_parameterDriftOperatorHsPi (ι := ι) g hb₁)
    (memLp_parameterDriftOperatorHsPi (ι := ι) g hb₂)

private abbrev referenceResidualCongrValue :=
  referenceResidualCongrDrift g hT a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ C₁ C₂ hC₁ hC₂
    (hae.fun_comp (parameterPrincipalOperatorHsPi (ι := ι) g))
    (hbe.fun_comp (parameterDriftOperatorHsPi (ι := ι) g))

include hae hbe in
private theorem reference_residual_congr_ae :
    circleResidualHigh (ι := ι) g hT a₁ b₁ ha₁ hb₁ C₁ hC₁ =
      circleResidualHigh (ι := ι) g hT a₂ b₂ ha₂ hb₂ C₂ hC₂ := by
  exact referenceResidualCongrValue g hT a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ C₁ C₂ hC₁ hC₂ hae hbe

end ResidualCongruence


private theorem reference_residual_tendsto_of_coefficient_representatives
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (a : X → ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (b : X → ℝ → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (ha : ∀ x, MemLp (a x) 2 (timeMeasure T))
    (hb : ∀ x, MemLp (b x) 2 (timeMeasure T))
    (Ch : X → ℝ≥0)
    (hCh : ∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (a x t)‖ ≤ Ch x)
    (aTop : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (bLp : X → timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (haTop : ∀ x, aTop x =ᵐ[timeMeasure T] a x)
    (hbLp : ∀ x, bLp x =ᵐ[timeMeasure T] b x)
    (halim : Tendsto aTop l (𝓝 (aTop x₀)))
    (hblim : Tendsto bLp l (𝓝 (bLp x₀))) :
    Tendsto (fun x => circleResidualHigh (ι := ι) g hT
      (a x) (b x) (ha x) (hb x) (Ch x) (hCh x)) l
      (𝓝 (circleResidualHigh (ι := ι) g hT
        (a x₀) (b x₀) (ha x₀) (hb x₀) (Ch x₀) (hCh x₀))) := by
  have hbound (x : X) : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (aTop x t)‖ ≤ Ch x := by
    filter_upwards [haTop x, hCh x] with t ht hbound
    rw [ht]
    exact hbound
  have htend := tendsto_heatVectorForcingResidualL_parameterOperators
    (ι := ι) g hT aTop (aTop x₀) bLp (bLp x₀) halim hblim Ch (Ch x₀)
      hbound (hbound x₀)
  have haTop₂ (x : X) : MemLp (fun t => aTop x t) 2 (timeMeasure T) :=
    (Lp.memLp (aTop x)).mono_exponent (by simp)
  have heq (x : X) :
      circleResidualHigh (ι := ι) g hT (fun t => aTop x t) (fun t => bLp x t)
        (haTop₂ x) (Lp.memLp (bLp x)) (Ch x) (hbound x) =
      circleResidualHigh (ι := ι) g hT (a x) (b x) (ha x) (hb x) (Ch x) (hCh x) := by
    exact reference_residual_congr_ae g hT (fun t => aTop x t) (a x)
      (fun t => bLp x t) (b x) (haTop₂ x) (ha x) (Lp.memLp (bLp x)) (hb x)
      (Ch x) (Ch x) (hbound x) (hCh x) (haTop x) (hbLp x)
  change Tendsto (fun x => circleResidualHigh (ι := ι) g hT
    (fun t => aTop x t) (fun t => bLp x t) (haTop₂ x) (Lp.memLp (bLp x)) (Ch x) (hbound x)) l
    (𝓝 (circleResidualHigh (ι := ι) g hT (fun t => aTop x₀ t) (fun t => bLp x₀ t)
      (haTop₂ x₀) (Lp.memLp (bLp x₀)) (Ch x₀) (hbound x₀))) at htend
  simp only [heq] at htend
  exact htend

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal Topology
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open AddCircle
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
attribute [local instance] vectorTensorHsNormedSpace

section

variable {X ι : Type*} [Fintype ι] {l : Filter X}
variable (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
variable {T : ℝ} (hT : 0 < T) (x₀ : X)
variable (F : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))) T)
variable (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
variable (W : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
variable (hW : ∀ x, ContinuousOn (W x) (Icc 0 T))
variable (a : X → timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
variable (b : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
variable (FH : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
variable (aTop : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
variable (Ch Cl : X → ℝ≥0)

include hW

theorem tendsto_iteratedParameterDerivative_forcing_lift
    (hf : Tendsto f l (𝓝 (f x₀)))
    (ha : Tendsto a l (𝓝 (a x₀))) (hb : Tendsto b l (𝓝 (b x₀)))
    (hWlim : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (haToplim : Tendsto aTop l (𝓝 (aTop x₀))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let U := fun x => maximalRegularityDuhamelVectorField hT 0 (F x)
    let G := fun x => iteratedParameterDerivativeDuhamelForcing g 0 (k + 2) hT (F x)
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i, W x t i = K (U x t i)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U x t i) +
        F x t i = scalarHsMul g (k + 2) (by simp) (J (a x t))
          (parameterSecondDerivativeHs g (k + 2) (P (f x i) + U x t i)) + J (b x t i)) →
    (∀ x, aTop x =ᵐ[timeMeasure T] (fun t => A (a x t))) →
    ∀ (hCh : ∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (A (a x t))‖ ≤ Ch x),
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := ι) g (A (a x t))‖ ≤ Cl x) →
    (Ch x₀ : ℝ) < 1 → (Cl x₀ : ℝ) < 1 →
    (∀ x, G x = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL
      2 (timeMeasure T) (FH x)) →
    Tendsto G l (𝓝 (G x₀)) →
    Tendsto FH l (𝓝 (FH x₀)) := by
  intro J A P K Z U G hWU hPDE haTop hCh hCl hChlt hCllt hLift hG
  let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
  let aH := fun x t => A (a x t)
  let bH := fun x t => ((k + 2 : ℕ) : ℝ) • N (a x t)
  let haH := fun x => (Lp.memLp (a x)).continuousLinearMap_comp A
  let hbH := fun x => ((Lp.memLp (a x)).continuousLinearMap_comp N).const_smul ((k + 2 : ℕ) : ℝ)
  let Q := fun x => circleResidualHigh (ι := ι) g hT (aH x) (bH x)
    (haH x) (hbH x) (Ch x) (hCh x)
  let R := fun x => Q x (FH x)
  have hRsource (x : X) :=
    heatVectorForcingResidualL_iteratedParameterDerivative_lift_ae_eq
      g k hT (F x) (f x) (W x) (hW x) (a x) (b x)
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι => J) (b x t))
      (FH x) (Ch x) (Cl x) (Eventually.of_forall fun _ _ => rfl)
      (hWU x) (hPDE x) (hCh x) (hCl x) (hLift x)
  have hR : Tendsto R l (𝓝 (R x₀)) := by
    apply tendsto_timeL2_iteratedParameterDerivativeSourceHs_of_tendstoUniformlyOn
      g k T f (f x₀) a (a x₀) b (b x₀) W (W x₀) R (R x₀)
      hf ha hb hW (hW x₀) hWlim
    · exact hRsource
    · exact hRsource x₀
  let NL := (((k + 2 : ℕ) : ℝ) • N).compLpL 2 (timeMeasure T)
  let bLp := fun x => NL (a x)
  have hbLp (x : X) : bLp x =ᵐ[timeMeasure T] bH x := by
    exact (((k + 2 : ℕ) : ℝ) • N).coeFn_compLpL (a x)
  have hblim : Tendsto bLp l (𝓝 (bLp x₀)) :=
    (NL.continuous.tendsto (a x₀)).comp ha
  have hQ : Tendsto Q l (𝓝 (Q x₀)) :=
    reference_residual_tendsto_of_coefficient_representatives g hT x₀ aH bH
      haH hbH Ch hCh aTop bLp haTop hbLp haToplim hblim
  apply reference_forcing_tendsto_of_residual g hT x₀ aH bH haH hbH
    Ch Cl hCh hCl hChlt hCllt FH hQ
  · change Tendsto (fun x => (ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL
      2 (timeMeasure T) (FH x)) l
      (𝓝 ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL
        2 (timeMeasure T) (FH x₀)))
    simpa only [← hLift] using hG
  · exact hR

end

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

open private parameterDerivativeDuhamelForcing_affineHeatEquation affineHeatEquation timeH1ToH0 from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleLinearizedLift

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
attribute [local instance] vectorTensorHsNormedSpace

theorem heatVectorForcingResidualL_parameterDerivative_lift_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T)
    (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (C2h C2l : ℝ≥0) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)
    let U := maximalRegularityDuhamelVectorField hT 0 F
    let aH := fun t => J (a₂ t)
    let haH := (Lp.memLp a₂).continuousLinearMap_comp J
    ∀ (hC2h : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (aH t)‖ ≤ C2h),
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (aH t)‖ ≤ C2l) →
    parameterDerivativeDuhamelForcing g 0 hT F = J₀.compLpL 2 (timeMeasure T) FH →
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (U t i) + F t i =
        scalarHsMul g 1 (by norm_num) (aH t)
          (AddCircle.parameterSecondDerivativeHs g 1 (P (f₀ i) + U t i)) + J (b₂ t i)) →
    circleResidualHigh g hT aH (fun t => a₂ t) haH (Lp.memLp a₂) C2h hC2h FH =
      AddCircle.parameterDerivativeBaselineForcingLp g f₀ a₂ b₂ := by
  intro J P Z J₀ U aH haH hC2h hC2l hlift heq
  have hlow := parameterDerivativeDuhamelForcing_affineHeatEquation g hT F f₀ a₂ b₂ heq
  apply parameterDerivative_forcing_residual_eq_of_inclusion
    g hT aH (fun t => a₂ t) haH (Lp.memLp a₂) C2h C2l
    (parameterDerivativeDuhamelForcing g 0 hT F) FH
    (AddCircle.parameterDerivativeBaselineForcingLp g f₀ a₂ b₂) hC2h hC2l hlift
  unfold affineHeatEquation at hlow
  filter_upwards [hlow] with t ht
  unfold normalizedPrincipalOperator normalizedDriftOperator scalarH0ToNatZeroPi
  unfold timeH1ToH0 at ht
  with_reducible_and_instances exact ht

private theorem tendsto_parameterDerivativeDuhamelForcing
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T)
    (F₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T)
    (hF : Tendsto F l (𝓝 F₀)) :
    Tendsto (fun x => parameterDerivativeDuhamelForcing g n hT (F x)) l
      (𝓝 (parameterDerivativeDuhamelForcing g n hT F₀)) := by
  let S := maximalRegularityVectorFieldL (ι := ι) (g := g) (r := 0) (s := 0)
    ((n + 1 : ℕ) : ℝ) hT.le
  have hS : Tendsto (fun x => S (F x)) l (𝓝 (S F₀)) :=
    (S.continuous.tendsto F₀).comp hF
  have heq (f : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T) :
      S f = maximalRegularityDuhamelVectorField hT 0 f :=
    maximalRegularityVectorFieldL_eq_duhamel hT f
  have hU : Tendsto (fun x => maximalRegularityDuhamelVectorField hT 0 (F x)) l
      (𝓝 (maximalRegularityDuhamelVectorField hT 0 F₀)) := by
    simpa only [heq] using hS
  unfold parameterDerivativeDuhamelForcing
  dsimp only
  apply Filter.Tendsto.add
  · exact ((ContinuousLinearMap.continuous _).tendsto _).comp hF
  · exact ((ContinuousLinearMap.continuous _).tendsto _).comp hU

theorem tendsto_parameterDerivative_forcing_lift
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (F : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a : X → timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T)
    (FH : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (aTop : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (Ch Cl : X → ℝ≥0)
    (hF : Tendsto F l (𝓝 (F x₀)))
    (hf : Tendsto f l (𝓝 (f x₀)))
    (ha : Tendsto a l (𝓝 (a x₀)))
    (hb : Tendsto b l (𝓝 (b x₀)))
    (haToplim : Tendsto aTop l (𝓝 (aTop x₀))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let U := fun x => maximalRegularityDuhamelVectorField hT 0 (F x)
    let G := fun x => parameterDerivativeDuhamelForcing g 0 hT (F x)
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (U x t i) + F x t i =
        scalarHsMul g 1 (by norm_num) (J (a x t))
          (AddCircle.parameterSecondDerivativeHs g 1 (P (f x i) + U x t i)) + J (b x t i)) →
    (∀ x, aTop x =ᵐ[timeMeasure T] (fun t => J (a x t))) →
    ∀ (hCh : ∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (J (a x t))‖ ≤ Ch x),
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (J (a x t))‖ ≤ Cl x) →
    (Ch x₀ : ℝ) < 1 → (Cl x₀ : ℝ) < 1 →
    (∀ x, G x = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL
      2 (timeMeasure T) (FH x)) →
    Tendsto FH l (𝓝 (FH x₀)) := by
  intro J P Z U G hPDE haTop hCh hCl hChlt hCllt hLift
  let aH := fun x t => J (a x t)
  let bH := fun x t => a x t
  let haH := fun x => (Lp.memLp (a x)).continuousLinearMap_comp J
  let hbH := fun x => Lp.memLp (a x)
  let Q := fun x => circleResidualHigh (ι := ι) g hT (aH x) (bH x)
    (haH x) (hbH x) (Ch x) (hCh x)
  have hsource (x : X) : Q x (FH x) =
      AddCircle.parameterDerivativeBaselineForcingLp g (f x) (a x) (b x) := by
    exact heatVectorForcingResidualL_parameterDerivative_lift_eq
      g hT (F x) (f x) (a x) (b x) (FH x) (Ch x) (Cl x)
      (hCh x) (hCl x) (hLift x) (hPDE x)
  have hR : Tendsto (fun x => Q x (FH x)) l (𝓝 (Q x₀ (FH x₀))) := by
    simpa only [hsource] using
      AddCircle.tendsto_parameterDerivativeBaselineForcingLp g f (f x₀)
        a (a x₀) b (b x₀) hf ha hb
  have hQ : Tendsto Q l (𝓝 (Q x₀)) :=
    reference_residual_tendsto_of_coefficient_representatives g hT x₀ aH bH
      haH hbH Ch hCh aTop a haTop (fun _ => Filter.EventuallyEq.rfl) haToplim ha
  have hG : Tendsto G l (𝓝 (G x₀)) :=
    tendsto_parameterDerivativeDuhamelForcing g 0 hT F (F x₀) hF
  apply reference_forcing_tendsto_of_residual g hT x₀ aH bH haH hbH
    Ch Cl hCh hCl hChlt hCllt FH hQ
  · change Tendsto (fun x => (ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL
      2 (timeMeasure T) (FH x)) l
      (𝓝 ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL
        2 (timeMeasure T) (FH x₀)))
    simpa only [← hLift] using hG
  · exact hR

theorem exists_parameterDerivative_forcing_lift_of_principal_norm_lt_one
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T)
    (C2h C2l : ℝ≥0) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)
    let U := maximalRegularityDuhamelVectorField hT 0 F
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (J (a₂ t))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (J (a₂ t))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (U t i) + F t i =
        scalarHsMul g 1 (by norm_num) (J (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g 1 (P (f₀ i) + U t i)) + J (b₂ t i)) →
    ∃ FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      parameterDerivativeDuhamelForcing g 0 hT F = J₀.compLpL 2 (timeMeasure T) FH := by
  intro J P Z J₀ U hCh hCl hChlt hCllt hPDE
  have hlow := parameterDerivativeDuhamelForcing_affineHeatEquation g hT F f₀ a₂ b₂ hPDE
  let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  let J' := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
  let N' := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
  have hJN (v : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) : J' (N v) = J v := by
    apply TensorHs.ext
    rfl
  have hNN (v : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) : N' (N v) = v := by
    apply TensorHs.ext
    rfl
  refine exists_normalized_parameterDerivative_forcing_lift g 1 hT
    (fun t => N (a₂ t)) ((Lp.memLp a₂).continuousLinearMap_comp N) C2h C2l
    (parameterDerivativeDuhamelForcing g 0 hT F)
    (AddCircle.parameterDerivativeBaselineForcingLp g f₀ a₂ b₂) ?_ ?_ hChlt hCllt ?_
  · change ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (J' (N (a₂ t)))‖ ≤ C2h
    simpa only [hJN] using hCh
  · change ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (J' (N (a₂ t)))‖ ≤ C2l
    simpa only [hJN] using hCl
  · unfold affineHeatEquation at hlow
    filter_upwards [hlow] with t ht
    change _ = normalizedPrincipalOperator g (J' (N (a₂ t))) _ +
      normalizedDriftOperator g (1 • N' (N (a₂ t))) _ + _
    rw [hJN, hNN, one_smul]
    unfold normalizedPrincipalOperator normalizedDriftOperator scalarH0ToNatZeroPi
    unfold timeH1ToH0 at ht
    with_reducible_and_instances exact ht

section

open private tendsto_iteratedParameterDerivativeDuhamelForcing from
DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleIteratedDifferentiation

open AddCircle (parameterSecondDerivativeHs parameterPrincipalOperatorHsPi
  parameterPrincipalOperatorH0Pi)

private theorem exists_tendsto_iteratedParameterDerivative_forcing_lift
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (F : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))) T)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
    (W : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
    (hW : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (a : X → timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (b : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
    (aTop : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (Ch Cl : X → ℝ≥0)
    (hF : Tendsto F l (𝓝 (F x₀))) (hf : Tendsto f l (𝓝 (f x₀)))
    (ha : Tendsto a l (𝓝 (a x₀))) (hb : Tendsto b l (𝓝 (b x₀)))
    (hWlim : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (haToplim : Tendsto aTop l (𝓝 (aTop x₀))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let U := fun x => maximalRegularityDuhamelVectorField hT 0 (F x)
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i, W x t i = K (U x t i)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U x t i) +
        F x t i = scalarHsMul g (k + 2) (by simp) (J (a x t))
          (parameterSecondDerivativeHs g (k + 2) (P (f x i) + U x t i)) + J (b x t i)) →
    (∀ x, aTop x =ᵐ[timeMeasure T] (fun t => A (a x t))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (A (a x t))‖ ≤ Ch x) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := ι) g (A (a x t))‖ ≤ Cl x) →
    (∀ x, (Ch x : ℝ) < 1) → (∀ x, (Cl x : ℝ) < 1) →
    ∃ FH : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      (∀ x, iteratedParameterDerivativeDuhamelForcing g 0 (k + 2) hT (F x) =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => Z)).compLpL
          2 (timeMeasure T) (FH x)) ∧
      Tendsto FH l (𝓝 (FH x₀)) := by
  intro J A P K Z U hWU hPDE haTop hCh hCl hChlt hCllt
  classical
  have hex (x : X) := exists_iteratedParameterDerivative_forcing_lift_of_principal_norm_lt_one
    g k hT (F x) (f x) (W x) (hW x) (a x) (b x)
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι => J) (b x t))
    (Ch x) (Cl x) (Eventually.of_forall fun _ _ => rfl)
    (hWU x) (hPDE x) (hCh x) (hCl x) (hChlt x) (hCllt x)
  choose FH hFH using hex
  refine ⟨FH, hFH, ?_⟩
  apply tendsto_iteratedParameterDerivative_forcing_lift
    g k hT x₀ F f W hW a b FH aTop Ch Cl hf ha hb hWlim haToplim
    hWU hPDE haTop hCh hCl (hChlt x₀) (hCllt x₀) hFH
  exact tendsto_iteratedParameterDerivativeDuhamelForcing g 0 (k + 2) hT (F x₀) F hF

end

section

open private exists_tendsto_normalized_duhamel_successor_states from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.AddCircleIteratedDerivativeContinuity

open private exists_tendsto_forcing_with_representative from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcingContinuity

open _root_.AddCircle (parameterSecondDerivativeHs parameterPrincipalOperatorHsPi
  parameterPrincipalOperatorH0Pi)

private theorem exists_tendsto_duhamel_states_of_principal_norm_lt_one
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (F : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))) T)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
    (W : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
    (hW : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (a : X → timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (b : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
    (aTop : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (Ch Cl : X → ℝ≥0)
    (hF : Tendsto F l (𝓝 (F x₀))) (hf : Tendsto f l (𝓝 (f x₀)))
    (ha : Tendsto a l (𝓝 (a x₀))) (hb : Tendsto b l (𝓝 (b x₀)))
    (hWlim : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (haToplim : Tendsto aTop l (𝓝 (aTop x₀))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let U := fun x => maximalRegularityDuhamelVectorField hT 0 (F x)
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i, W x t i = K (U x t i)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U x t i) +
        F x t i = scalarHsMul g (k + 2) (by simp) (J (a x t))
          (parameterSecondDerivativeHs g (k + 2) (P (f x i) + U x t i)) + J (b x t i)) →
    (∀ x, aTop x =ᵐ[timeMeasure T] (fun t => A (a x t))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (A (a x t))‖ ≤ Ch x) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := ι) g (A (a x t))‖ ≤ Cl x) →
    (∀ x, (Ch x : ℝ) < 1) → (∀ x, (Cl x : ℝ) < 1) →
    ∃ (Vnext : X → timeL2
        (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))) T)
      (Wnext : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))),
      (∀ x, (ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))
        (F := fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)) 2 (fun _ : ι => P)).compLpL
        2 (timeMeasure T) (Vnext x) = U x) ∧
      (∀ x, ContinuousOn (Wnext x) (Icc 0 T)) ∧
      (∀ x t, t ∈ Icc 0 T →
        ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))
        (F := fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) 2 (fun _ : ι => K) (Wnext x t) = W x t) ∧
      (∀ x, Wnext x =ᵐ[timeMeasure T]
        fun t => ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))
        (F := fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)) 2 (fun _ : ι => P) (Vnext x t)) ∧
      Tendsto Vnext l (𝓝 (Vnext x₀)) ∧
      TendstoUniformlyOn Wnext (Wnext x₀) l (Icc 0 T) := by
  intro J A P K U hWU hPDE haTop hCh hCl hChlt hCllt
  obtain ⟨FH, hFH, hFHlim⟩ := exists_tendsto_iteratedParameterDerivative_forcing_lift
    g k hT x₀ F f W hW a b aTop Ch Cl hF hf ha hb hWlim haToplim
    hWU hPDE haTop hCh hCl hChlt hCllt
  exact exists_tendsto_normalized_duhamel_successor_states
    g k hT x₀ F FH W hW hF hFHlim hFH hWU

private def scalarSobolevPiInclusion
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a b : ℝ} (hab : a ≤ b) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 b) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 a) :=
  ContinuousLinearMap.piLpMap (𝕜 := ℝ)
    (E := fun _ : ι => TensorHs g 0 0 b)
    (F := fun _ : ι => TensorHs g 0 0 a)
    2 (fun _ : ι => tensorHsInclusion (g := g) (r := 0) (s := 0) hab)

variable
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (F : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))) T)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
    (W : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
    (hW : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (a : X → timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (b : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
    (aTop : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (Ch Cl : X → ℝ≥0)
    (hF : Tendsto F l (𝓝 (F x₀))) (hf : Tendsto f l (𝓝 (f x₀)))
    (ha : Tendsto a l (𝓝 (a x₀))) (hb : Tendsto b l (𝓝 (b x₀)))
    (hWlim : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (haToplim : Tendsto aTop l (𝓝 (aTop x₀)))

variable (hcoeffLift :
    ∀ Wnext : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)),
      (∀ x, ContinuousOn (Wnext x) (Icc 0 T)) →
      (∀ x t, t ∈ Icc 0 T →
        scalarSobolevPiInclusion (ι := ι) g
          (by simpa only [Nat.cast_add, Nat.cast_ofNat] using
            (Nat.cast_le.mpr (by omega : k + 3 ≤ (k + 2) + 2) :
              ((k + 3 : ℕ) : ℝ) ≤ (((k + 2) + 2 : ℕ) : ℝ))) (Wnext x t) = W x t) →
      TendstoUniformlyOn Wnext (Wnext x₀) l (Icc 0 T) →
      ∃ aTop : X → Lp (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) ∞ (timeMeasure T),
        (∀ x, aTop x =ᵐ[timeMeasure T] a x) ∧ Tendsto aTop l (𝓝 (aTop x₀)))

include hW hF hf ha hb hWlim haToplim hcoeffLift in
private theorem exists_tendsto_forcing_successor_of_coefficient_lift :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (Nat.cast_le.mpr (Nat.add_le_add_left (by decide : 2 ≤ 3) k) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (Nat.cast_le.mpr (by omega : 1 ≤ k + 3) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (add_le_add_left (Nat.cast_le.mpr
        (Nat.add_le_add_left (by decide : 2 ≤ 3) k) :
          ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)) 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by simpa only [Nat.cast_add, Nat.cast_ofNat] using
        (Nat.cast_le.mpr (by omega : k + 3 ≤ (k + 2) + 2) :
          ((k + 3 : ℕ) : ℝ) ≤ (((k + 2) + 2 : ℕ) : ℝ)))
    let U := fun x => maximalRegularityDuhamelVectorField hT 0 (F x)
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i, W x t i = K (U x t i)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U x t i) +
        F x t i = scalarHsMul g (k + 2) (by simp) (J (a x t))
          (parameterSecondDerivativeHs g (k + 2) (P (f x i) + U x t i)) + J (b x t i)) →
    (∀ x, aTop x =ᵐ[timeMeasure T] (fun t => A (a x t))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (A (a x t))‖ ≤ Ch x) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := ι) g (A (a x t))‖ ≤ Cl x) →
    (∀ x, (Ch x : ℝ) < 1) → (∀ x, (Cl x : ℝ) < 1) →
    ∃ (forceNext : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
      (Vnext : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))) T)
      (Wnext : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))),
      (∀ x, (scalarSobolevPiInclusion (ι := ι) g
        (Nat.cast_le.mpr (Nat.add_le_add_left (by decide : 2 ≤ 3) k) :
          ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))).compLpL
        2 (timeMeasure T) (forceNext x) = F x) ∧
      (∀ x, Vnext x = maximalRegularityDuhamelVectorField hT 0 (forceNext x)) ∧
      (∀ x, ContinuousOn (Wnext x) (Icc 0 T)) ∧
      (∀ x t, t ∈ Icc 0 T →
        scalarSobolevPiInclusion (ι := ι) g
          (by simpa only [Nat.cast_add, Nat.cast_ofNat] using
            (Nat.cast_le.mpr (by omega : k + 3 ≤ (k + 2) + 2) :
              ((k + 3 : ℕ) : ℝ) ≤ (((k + 2) + 2 : ℕ) : ℝ))) (Wnext x t) = W x t) ∧
      (∀ x, Wnext x =ᵐ[timeMeasure T]
        fun t => scalarSobolevPiInclusion (ι := ι) g
          (add_le_add_left (Nat.cast_le.mpr
            (Nat.add_le_add_left (by decide : 2 ≤ 3) k) :
              ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)) 2) (Vnext x t)) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 3 : ℕ) : ℝ) (Vnext x t i) +
          forceNext x t i = scalarHsMul g (k + 3) (by simp) (a x t)
            (parameterSecondDerivativeHs g (k + 3) (f x i + Vnext x t i)) + b x t i) ∧
      Tendsto forceNext l (𝓝 (forceNext x₀)) ∧
      Tendsto Vnext l (𝓝 (Vnext x₀)) ∧
      TendstoUniformlyOn Wnext (Wnext x₀) l (Icc 0 T) := by
  intro J A P K U hWU hPDE haTop hCh hCl hChlt hCllt
  obtain ⟨Vnext, Wnext, hs⟩ :=
    exists_tendsto_duhamel_states_of_principal_norm_lt_one
      (X := X) (ι := ι) (l := l) (T := T) g k hT x₀ F f W hW a b aTop Ch Cl hF hf ha hb hWlim haToplim
      hWU hPDE haTop hCh hCl hChlt hCllt
  obtain ⟨aHighTop, haHighTop, haHighToplim⟩ := hcoeffLift Wnext (hs.2.1) (hs.2.2.1) (hs.2.2.2.2.2)
  have hout := exists_tendsto_forcing_with_representative
    (X := X) (ι := ι) (l := l) (T := T) g k hT x₀ f Vnext F a aHighTop b W Wnext
    hs.2.1 hs.2.2.2.2.2 hf hs.2.2.2.2.1 haHighToplim hb haHighTop
    hs.1 hPDE hs.2.2.1 hs.2.2.2.1
  exact hout

end

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
