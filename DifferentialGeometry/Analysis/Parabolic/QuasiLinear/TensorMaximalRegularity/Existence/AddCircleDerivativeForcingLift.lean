import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleSecondDerivativeSource
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedForcing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedOperators
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.HeatTraceLift

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

private theorem parameterDriftOperatorH0Pi_two_smul_eq_continuous_mul
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
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
    parameterDriftOperatorH0Pi g ((2 : ℝ) • N a₂)
      ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁)) w) i =
        scalarH0ContinuousMul g
          ((2 : ℝ) • C (D a₂) - ⟨laplacianDriftCoefficient g,
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
    (2 : ℝ) a₂ ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => B₂)) w))
  change parameterDriftOperatorH0Pi g ((2 : ℝ) • N a₂)
    ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₂))
      ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => B₂)) w)) i = _ at hh
  rw [hKw] at hh
  simpa only [N, B₂, C, D, Zr, ContinuousLinearMap.piLpMap_apply,
    ContinuousLinearMap.comp_apply] using hh

private theorem exists_normalized_secondDerivative_forcing_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (a : ℝ → TensorHs g 0 0 ((2 : ℕ) : ℝ))
    (ham : MemLp a 2 (timeMeasure T)) (C2h C2l : ℝ≥0)
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
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorHsPi (ι := ι) g (J (a t))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorH0Pi (ι := ι) g (J (a t))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    (∀ᵐ t ∂timeMeasure T,
      G t = normalizedPrincipalOperator g (J (a t)) (heatDuhamelVectorField hT 0 G t) +
        normalizedDriftOperator g ((2 : ℝ) • N (a t))
          ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => K₁))
            (heatDuhamelVectorField hT 0 G t)) + J₀.compLpL 2 (timeMeasure T) R t) →
    ∃ FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      G = J₀.compLpL 2 (timeMeasure T) FH := by
  intro J N K₁ Z J₀ hC2h hC2l hC2hlt hC2llt hfLeq
  let R₀ := J₀.compLpL 2 (timeMeasure T) R
  let A2h : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((((1 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
    fun t => parameterPrincipalOperatorHsPi (ι := ι) g (J (a t))
  let A2l : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((((0 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
    fun t => normalizedPrincipalOperator (ι := ι) g (J (a t))
  let A1h : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((((1 : ℕ) : ℝ) + 1))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
    fun t => parameterDriftOperatorHsPi (ι := ι) g ((2 : ℝ) • N (a t))
  let A1l : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((((0 : ℕ) : ℝ) + 1))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
    fun t => normalizedDriftOperator (ι := ι) g ((2 : ℝ) • N (a t))
  have hA2h : AEStronglyMeasurable A2h (timeMeasure T) :=
    (memLp_parameterPrincipalOperatorHsPi g (ham.continuousLinearMap_comp J)).aestronglyMeasurable
  have hA2l : AEStronglyMeasurable A2l (timeMeasure T) :=
    (memLp_normalizedPrincipalOperator g (ham.continuousLinearMap_comp J)).aestronglyMeasurable
  have hA1h : MemLp A1h 2 (timeMeasure T) :=
    memLp_parameterDriftOperatorHsPi g ((ham.continuousLinearMap_comp N).const_smul (2 : ℝ))
  have hA1l : MemLp A1l 2 (timeMeasure T) :=
    memLp_normalizedDriftOperator g ((ham.continuousLinearMap_comp N).const_smul (2 : ℝ))
  have hC2l' : ∀ᵐ t ∂timeMeasure T, ‖A2l t‖ ≤ C2l := by
    filter_upwards [hC2l] with t ht
    exact (norm_normalizedPrincipalOperator_le g (J (a t))).trans ht
  have hc := tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  refine exists_heat_vector_forcing_lift_of_l2_coefficients
    (ι := ι) (E := ℝ) (H := ℝ) (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
    (g := g) (r := 0) (s := 0) (a := ((0 : ℕ) : ℝ)) (b := ((1 : ℕ) : ℝ))
    (by norm_num) hT hc 0 G A2h hA2h C2h hC2h A1h hA1h R
    A2l hA2l C2l hC2l' A1l hA1l R₀ ?_ ?_ rfl hfLeq hC2hlt hC2llt 0 ?_
  · exact Eventually.of_forall fun t x =>
      tensorHsInclusion_parameterPrincipalOperatorHsPi_normalized g (J (a t)) x
  · exact Eventually.of_forall fun t x =>
      tensorHsInclusion_parameterDriftOperatorHsPi_normalized g ((2 : ℝ) • N (a t)) x
  · exact (map_zero _).symm


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
    parameterDriftOperatorH0Pi_two_smul_eq_continuous_mul g w (a t) i
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
  exact exists_normalized_secondDerivative_forcing_lift g hT a ham C2h C2l G R
    hC2h hC2l hC2hlt hC2llt hfLeq

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
