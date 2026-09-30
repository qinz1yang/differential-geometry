import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientBounds

open private ScalarVectorTimeCoefficients.diffusion ScalarVectorTimeCoefficients.diffusionLipschitz ScalarVectorTimeCoefficients.diffusion_lipschitz ScalarVectorTimeCoefficients.radius ScalarVectorTimeCoefficients.radius_pos ScalarVectorTimeCoefficients.reaction ScalarVectorTimeCoefficients.reactionLipschitz ScalarVectorTimeCoefficients.reaction_lipschitz from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState

open private coordinateMultiplication CircleHsPi circleHsPiInclusion extendClosedBall extendClosedBall_apply circleHsPiCongr circleHsPiCongr_apply from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private firstJetCoordinates circleFirstJet ambientCoordinateCc ambientSobolev scalarH1ToContinuous_ambientSobolev scalarH1PiToContinuous_ambientSobolev ambientFirstJet PrecomposedCircleSolution precomposedCircleSolutionRadius precomposedCircleSolutionWithRadiusLe ScalarVectorTimeCoefficients ambientCoefficients initial_diffusion_coefficients precomposed_circle_solution_exists_with_radius_le ambientCoefficients_eval_of_eq_circleFirstJet from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private ambient_coefficients_h2_norm_le_of_small_state ambient_diffusion_sub_baseline_norm_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientBounds

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_coefficients_h2_norm_le_of_forcing_bound
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ δ ≤ 1 ∧
      ∃ A B : ℝ≥0, ∀ {ρ T : ℝ} (hT : 0 < T), T ≤ ρ → ρ ≤ δ →
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      ‖gforce‖ ≤ ρ / 4 →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))) ∧
        (fun t => P (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) ∧
        ‖b₂‖ ≤ B * (Real.sqrt T + (1 + T) * ρ / 4) := by
  intro C g₀ J K H P
  obtain ⟨δ, hδ, hδC, hδ1, A, B, hA, hB, hab⟩ :=
    ambient_coefficients_h2_norm_le_of_small_state c₀ g ht he hr hEU hleft β hG
  refine ⟨δ, hδ, hδC, hδ1, ⟨A, hA⟩, ⟨B, hB⟩, ?_⟩
  intro ρ T hT hTρ hρδ gforce field w hw hwu hbound hforce
  obtain ⟨a₂, b₂, ha₂, hb₂, hanorm, hbnorm⟩ :=
    hab T (hTρ.trans hρδ) field w hw hwu (fun t ht => (hbound t ht).trans hρδ)
  let S := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ 2)
  let SP := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => S)
  let aa := S.compLpL 2 (timeMeasure T) a₂
  let bb := SP.compLpL 2 (timeMeasure T) b₂
  have hSnorm : ‖S‖ ≤ 1 := tensorHsInclusion_opNorm_le_one _
  have hSPnorm : ‖SP‖ ≤ 1 :=
    ContinuousLinearMap.norm_piLpMap_le _ zero_le_one (fun _ => hSnorm)
  have han : ‖aa‖ ≤ ‖a₂‖ := by
    exact (S.norm_compLp_le a₂).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hSnorm (norm_nonneg a₂))
  have hbn : ‖bb‖ ≤ ‖b₂‖ := by
    exact (SP.norm_compLp_le b₂).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hSPnorm (norm_nonneg b₂))
  have hfield : ‖field‖ ≤ (1 + T) * ρ / 4 := by
    exact (norm_maximalRegularityDuhamelVectorField_zero_le hT gforce).trans
      (by simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left hforce (by linarith : 0 ≤ 1 + T))
  refine ⟨aa, bb, ?_, ?_, han.trans (hanorm.trans ?_), hbn.trans (hbnorm.trans ?_)⟩
  · filter_upwards [S.coeFn_compLpL a₂, ha₂] with t hta hta₂
    change H (aa t) = _
    rw [hta]
    exact (tensorHsInclusion_trans_apply _ _ _).symm.trans hta₂
  · filter_upwards [SP.coeFn_compLpL b₂, hb₂] with t htb htb₂
    change P (bb t) = _
    rw [htb, ← htb₂]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ 2) (b₂ t i)).symm
  · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hfield) hA
  · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hfield) hB

private theorem ambient_parameter_equation_of_h2_coefficients
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let f₄ := ambientSobolev c₀ (g 0) e he (((2 : ℕ) : ℝ) + 2)
    let K₄ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    ∀ (T : ℝ) (hT : 0 < T),
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))
      let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∀ b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
      (fun t => H (a₂ t)) =ᵐ[timeMeasure T] alpha →
      (fun t => P (b₂ t)) =ᵐ[timeMeasure T] reaction →
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) →
      ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) +
          gforce t i = scalarHsMul g₀ 1 (by norm_num) (H (a₂ t))
            (AddCircle.parameterSecondDerivativeHs g₀ 1 (K₄ (f₄ i) + field t i)) +
              H (b₂ t i) := by
  intro C g₀ f₀ f₄ K₄ H P J T hT gforce field w alpha reaction L Q m a₂ b₂ ha hb heq
  have hbase (i : Fin n) : K₄ (f₄ i) = f₀ i := by
    exact tensorHsInclusion_ccTensorToHs g₀ 0
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
      (ambientCoordinateCc c₀ (g 0) e he i)
  filter_upwards [heq, ha, hb] with t ht hat hbt
  intro i
  rw [hbase]
  rw [← hat, ← hbt] at ht
  exact congrArg (fun v : CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) => v i) ht

private theorem parameterDerivativeH0Pi_normalized_contraction
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (C₂ : ℝ≥0) :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let Z : CircleHsPi g₀ (Fin n) 0 →L[ℝ] CircleHsPi g₀ (Fin n) ((0 : ℕ) : ℝ) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ)))
    let A₂ : ℝ → CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi g₀ (Fin n) 0 :=
      fun t => AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (H (a₂ t))
    let A₁ : ℝ → CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 1) →L[ℝ]
        CircleHsPi g₀ (Fin n) 0 :=
      fun t => AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t)
    let hA₁ : MemLp A₁ 2 (timeMeasure T) := AddCircle.memLp_parameterDriftOperatorH0Pi (ι := Fin n) g₀ (Lp.memLp a₂)
    (∀ᵐ t ∂timeMeasure T,
      ‖A₂ t‖ ≤ C₂) →
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA₁.toLp A₁‖ < 1 →
    (∀ᵐ t ∂timeMeasure T,
      ‖Z.comp (A₂ t)‖ ≤ C₂) ∧
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (fun t => Z.comp (A₁ t)) 2 (timeMeasure T)).toReal < 1 := by
  intro H Z A₂ A₁ hA₁ hC hsmall
  have hZ : ‖Z‖ ≤ 1 :=
    ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
      (fun _ => tensorHsInclusion_opNorm_le_one _)
  have hpoint {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
      (L : X →L[ℝ] CircleHsPi g₀ (Fin n) 0) : ‖Z.comp L‖ ≤ ‖L‖ :=
    (ContinuousLinearMap.opNorm_comp_le Z L).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hZ (norm_nonneg L))
  have hn : (eLpNorm (fun t => Z.comp (A₁ t)) 2 (timeMeasure T)).toReal ≤
      (eLpNorm A₁ 2 (timeMeasure T)).toReal :=
    ENNReal.toReal_mono hA₁.eLpNorm_lt_top.ne
      (eLpNorm_mono
        (((ContinuousLinearMap.compL ℝ _ _ _) Z).continuous.comp_aestronglyMeasurable
          hA₁.aestronglyMeasurable)
        (fun t => hpoint (A₁ t)))
  refine ⟨?_, ?_⟩
  · filter_upwards [hC] with t ht
    exact (hpoint _).trans ht
  · rw [Lp.norm_toLp] at hsmall
    exact lt_of_le_of_lt
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg (1 + T)))) hsmall

private abbrev parameterPrincipalHigh
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) :=
  fun t => AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀
    (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))

private abbrev parameterNormalizeZero
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    CircleHsPi g₀ (Fin n) 0 →L[ℝ] CircleHsPi g₀ (Fin n) ((0 : ℕ) : ℝ) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ)))

private abbrev parameterPrincipalLow
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    ℝ → CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((0 : ℕ) : ℝ) :=
  fun t => (parameterNormalizeZero (n := n) g₀).comp
    (AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀
      (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)))

private abbrev parameterDriftHigh
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) :=
  fun t => AddCircle.parameterDriftOperatorHsPi (ι := Fin n) g₀ (a₂ t)

private abbrev parameterDriftLow
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    ℝ → CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((0 : ℕ) : ℝ) :=
  fun t => (parameterNormalizeZero (n := n) g₀).comp
    (AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t))

private abbrev parameterDerivativeLiftOfCoefficients
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (F : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (C₂h C₂l : ℝ≥0) :=
  exists_unique_parameterDerivativeDuhamelForcing_lift g₀ hT F f₄ a₂ b₂ C₂h C₂l

section

variable (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)

variable (F : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)

variable (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))

variable (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)

variable (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)

variable (C₂h C₂l : ℝ≥0)

variable (hC₂h : ∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h)

variable (hC₂l : ∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l)

variable (hsmallh : (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1)

variable (hsmalll : (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1)

private abbrev parameterDerivativeLiftWithHighBound :=
  parameterDerivativeLiftOfCoefficients
    g₀ hT F f₄ a₂ b₂ C₂h C₂l hC₂h hC₂l
      (by change _ + _ * ‖_‖ < (1 : ℝ); erw [Lp.norm_toLp]; exact hsmallh)

private abbrev parameterDerivativeLiftWithBounds :=
  parameterDerivativeLiftWithHighBound (g₀ := g₀) (hT := hT) (F := F) (f₄ := f₄)
    (a₂ := a₂) (b₂ := b₂) (C₂h := C₂h) (C₂l := C₂l) (hC₂h := hC₂h) (hC₂l := hC₂l)
    (hsmallh := hsmallh)
    (by change _ + _ * ‖_‖ < (1 : ℝ); erw [Lp.norm_toLp]; exact hsmalll)

include hC₂h hC₂l hsmallh hsmalll in
private theorem parameterDerivative_forcing_lift_of_contraction :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let K₄ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 F
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) + F t i =
        scalarHsMul g₀ 1 (by norm_num) (H (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g₀ 1 (K₄ (f₄ i) + field t i)) + H (b₂ t i)) →
    ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT F =
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := g₀) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
              2 (timeMeasure T) FH := by
  intro H K₄ field hweak
  obtain ⟨FH, hFH, _⟩ := parameterDerivativeLiftWithBounds
    (g₀ := g₀) (hT := hT) (F := F) (f₄ := f₄) (a₂ := a₂) (b₂ := b₂)
    (C₂h := C₂h) (C₂l := C₂l) (hC₂h := hC₂h) (hC₂l := hC₂l)
    (hsmallh := hsmallh) (hsmalll := hsmalll) hweak
  exact ⟨FH, hFH.2⟩

end


section

variable (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
variable (Cα A : ℝ≥0) {R : ℝ} (hR : 0 < R)

include hR in
private theorem exists_pos_parameterDerivative_high_contraction_radius :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (DifferentialGeometry.Analysis.Sobolev.scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
      0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ Cα * ρ) →
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      ∃ C₂h : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h) ∧
        (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1 := by
  intro H q
  obtain ⟨δ, hδ, hδR, hδ1, hh⟩ :=
    AddCircle.exists_pos_parameterDerivativeHsPi_contraction_radius (ι := Fin n) g₀ Cα A hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  obtain ⟨C₂h, hC₂h, hsmallh⟩ := hh hT hTρ hρδ a₂ hclose hnorm
  refine ⟨C₂h, hC₂h, ?_⟩
  simpa only [Lp.norm_toLp] using hsmallh

private def parameterDerivativeRawLowContraction
    {T : ℝ} (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) : Prop :=
  let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  let A₂ := fun t => AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (H (a₂ t))
  let A₁ := fun t => AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t)
  let hA₁ := AddCircle.memLp_parameterDriftOperatorH0Pi (ι := Fin n) g₀ (Lp.memLp a₂)
  ∃ C₂ : ℝ≥0, (∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ C₂) ∧
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA₁.toLp A₁‖ < 1

private def parameterDerivativeNormalizedLowContraction
    {T : ℝ} (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) : Prop :=
  ∃ C₂ : ℝ≥0,
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂) ∧
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1

private theorem parameterDerivative_normalizedLowContraction_of_raw
    {T : ℝ} (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (hraw : parameterDerivativeRawLowContraction (n := n) g₀ a₂) :
    parameterDerivativeNormalizedLowContraction (n := n) g₀ a₂ := by
  obtain ⟨C₂, hC₂, hsmall⟩ := hraw
  exact ⟨C₂, parameterDerivativeH0Pi_normalized_contraction g₀ a₂ C₂ hC₂ hsmall⟩

private def parameterDerivativeLowContractionRadiusStatement : Prop :=
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (DifferentialGeometry.Analysis.Sobolev.scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
      0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ Cα * ρ) →
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      ∃ C₂l : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l) ∧
        (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1

include hR in
private theorem exists_pos_parameterDerivative_low_contraction_radius :
    parameterDerivativeLowContractionRadiusStatement (n := n) g₀ Cα A (R := R) := by
  unfold parameterDerivativeLowContractionRadiusStatement
  intro H q
  obtain ⟨δ, hδ, hδR, hδ1, hl⟩ :=
    AddCircle.exists_pos_parameterDerivativeH0Pi_contraction_radius (ι := Fin n) g₀ Cα A hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  obtain ⟨C₂l, hC₂l, hsmalll⟩ := hl hT hTρ hρδ a₂ hclose hnorm
  exact parameterDerivative_normalizedLowContraction_of_raw g₀ a₂ ⟨C₂l, hC₂l, hsmalll⟩


private def parameterDerivativeContractionRadiusStatement : Prop :=
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (DifferentialGeometry.Analysis.Sobolev.scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
      0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ Cα * ρ) →
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      ∃ C₂h C₂l : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h) ∧
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l) ∧
        (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1 ∧
        (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1

include hR in
private theorem exists_pos_parameterDerivative_contraction_radius :
    parameterDerivativeContractionRadiusStatement (n := n) g₀ Cα A (R := R) := by
  unfold parameterDerivativeContractionRadiusStatement
  intro H q
  obtain ⟨δh, hδh, hδhR, hδh1, hh⟩ :=
    exists_pos_parameterDerivative_high_contraction_radius (n := n) g₀ Cα A hR
  obtain ⟨δl, hδl, _, _, hl⟩ :=
    exists_pos_parameterDerivative_low_contraction_radius (n := n) g₀ Cα A hR
  refine ⟨min δh δl, lt_min hδh hδl, (min_le_left _ _).trans hδhR,
    (min_le_left _ _).trans hδh1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  obtain ⟨C₂h, hC₂h, hsmallh⟩ :=
    hh (ρ := ρ) (T := T) hT hTρ (hρδ.trans (min_le_left _ _)) a₂ hclose hnorm
  obtain ⟨C₂l, hC₂l, hsmalll⟩ :=
    hl (ρ := ρ) (T := T) hT hTρ (hρδ.trans (min_le_right _ _)) a₂ hclose hnorm
  refine ⟨C₂h, C₂l, ?_, ?_, ?_, ?_⟩
  · exact hC₂h
  · exact hC₂l
  · exact hsmallh
  · exact hsmalll

end

section

variable (c₀ : SmoothImmersion (I := I) (M := M))

variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}

variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)

variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)

variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private def ambientH2Control :=
  Classical.indefiniteDescription _
    (ambient_coefficients_h2_norm_le_of_forcing_bound c₀ g ht he hr hEU hleft β hG)

private def ambientH2ControlBounds :=
  Classical.indefiniteDescription _
    (ambientH2Control c₀ g ht he hr hEU hleft β hG).property.2.2.2

private def ambientDiffusionClosenessControl :=
  Classical.indefiniteDescription _
    (ambient_diffusion_sub_baseline_norm_le c₀ g ht he hr hEU hleft β hG)

private def ambientParameterDerivativeControl :=
  Classical.indefiniteDescription _
    (exists_pos_parameterDerivative_contraction_radius (n := n) (c₀.pullbackMetric (g 0))
      (ambientDiffusionClosenessControl c₀ g ht he hr hEU hleft β hG).val
      (ambientH2ControlBounds c₀ g ht he hr hEU hleft β hG).val
      (ambientH2Control c₀ g ht he hr hEU hleft β hG).property.1)

private def ambientDiffusionProjection {T : ℝ}
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T) : Prop :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  (fun t => tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
    (fun t => tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))))

private def ambientReactionProjection {T : ℝ}
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T) : Prop :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  (fun t => (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b₂ t)) =ᵐ[timeMeasure T]
    (fun t => circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t))))

private theorem ambient_diffusion_h2_sub_baseline_norm_le :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    ∀ {ρ T : ℝ}, 0 ≤ ρ → T ≤ ρ →
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w a₂ →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ᵐ t ∂timeMeasure T,
        ‖H (a₂ t) - ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
          (DifferentialGeometry.Analysis.Sobolev.scalarCc g₀
            (AddCircle.laplacianPrincipalCoefficient g₀))‖ ≤
              (ambientDiffusionClosenessControl c₀ g ht he hr hEU hleft β hG).val * ρ := by
  intro C g₀ J H ρ T hρ hTρ w a₂ ha hbound hJ
  have htmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  filter_upwards [ha, htmem] with t hat htt
  rw [hat]
  exact (ambientDiffusionClosenessControl c₀ g ht he hr hEU hleft β hG).property
    hρ hTρ w hbound hJ t htt

private abbrev ambientDiffusionH2ClosenessAtState
    {ρ T : ℝ} (hρ : 0 ≤ ρ) (hTρ : T ≤ ρ)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T) :=
  ambient_diffusion_h2_sub_baseline_norm_le c₀ g ht he hr hEU hleft β hG hρ hTρ w a₂

private abbrev ambientParameterDerivativeContractionAtState
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T) :=
  (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).property.2.2.2
    hT hTρ hρδ a₂

private def ambientParameterDerivativeLiftAtRadius (δ : ℝ) : Prop :=
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∀ {ρ T : ℝ} (hT : 0 < T), T ≤ ρ → ρ ≤ δ →
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))
      let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ‖gforce‖ ≤ ρ / 4 →
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) →
      ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
        parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce =
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
            tensorHsInclusion (g := g₀) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
                2 (timeMeasure T) FH


private def ambientParameterDerivativeLiftAtControlRadius
    (C : ScalarVectorTimeCoefficients (c₀.pullbackMetric (g 0))
      (curveShorteningChartDiffusionCoefficient (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n)
      (fun z j => (curveShorteningParametricChartReaction (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z)).ofLp j)
      (firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β)
      (ambientFirstJet c₀ (g 0) e he))
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 2)))
    (J : (PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1))) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (1 : ℝ)))
    (K : PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1))) : Prop :=
    ∀ {ρ T : ℝ} (hT : 0 < T), T ≤ ρ → ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val →
      ∀ gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1),
      let alpha := fun t => tensorHsCongrL (c₀.pullbackMetric (g 0)) 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))
      let reaction := fun t => circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))
      let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) (c₀.pullbackMetric (g 0)) 1
      let m := coordinateMultiplication (ι := Fin n) (scalarHsMul (c₀.pullbackMetric (g 0)) 1 (by norm_num))
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ‖gforce‖ ≤ ρ / 4 →
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) →
      ∃ FH : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T,
        parameterDerivativeDuhamelForcing (ι := Fin n) (c₀.pullbackMetric (g 0)) 0 hT gforce =
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
            tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
                2 (timeMeasure T) FH

private def ambientParameterDerivativeLiftOfOperatorBounds : Prop :=
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) := c₀.pullbackMetric (g 0)
    let f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1) := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    ∀ (T : ℝ) (hT : 0 < T),
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let alpha : ℝ → TensorHs g₀ 0 0 ((1 : ℕ) : ℝ) := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))
      let reaction : ℝ → CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))
      let L : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
      let Q : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      let m : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ) →L[ℝ]
        CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) →L[ℝ] CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∀ b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
      ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w a₂ →
      ambientReactionProjection c₀ g ht he hr hEU hleft β hG w b₂ →
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) →
      ∀ C₂h C₂l : ℝ≥0,
      (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h) →
      (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l) →
      (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
        (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1 →
      (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
        (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1 →
      ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
        parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce =
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
            tensorHsInclusion (g := g₀) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
                2 (timeMeasure T) FH

private theorem ambient_parameterDerivative_forcing_lift_of_operator_bounds :
    ambientParameterDerivativeLiftOfOperatorBounds c₀ g ht he hr hEU hleft β hG := by
  unfold ambientParameterDerivativeLiftOfOperatorBounds
  intro C g₀ f₀ J T hT gforce field w alpha reaction L Q m a₂ b₂ ha hb heq C₂h C₂l hC₂h hC₂l hsmallh hsmalll
  have hweak := ambient_parameter_equation_of_h2_coefficients c₀ g ht he hr hEU hleft β hG
    T hT gforce w a₂ b₂ ha hb heq
  exact parameterDerivative_forcing_lift_of_contraction g₀ hT gforce
    (ambientSobolev c₀ (g 0) e he (((2 : ℕ) : ℝ) + 2)) a₂ b₂ C₂h C₂l hC₂h hC₂l
    hsmallh hsmalll hweak

private abbrev ambientParameterDerivativeOperatorLift
    (T : ℝ) (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T) :=
  ambient_parameterDerivative_forcing_lift_of_operator_bounds c₀ g ht he hr hEU hleft β hG
    T hT gforce w a₂ b₂

private def parameterDerivativeOperatorBoundsWithMargin {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) (q : ℝ) : Prop :=
  ∃ C₂h C₂l : ℝ≥0,
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h) ∧
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l) ∧
    (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal ≤ q ∧
    (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1

private def parameterDerivativeOperatorBounds
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) : Prop :=
  ∃ C₂h C₂l : ℝ≥0,
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h) ∧
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l) ∧
    (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1 ∧
    (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1

private theorem parameterDerivativeOperatorBounds_of_margin
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T q : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (hq : q < 1) (h : parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ q) :
    parameterDerivativeOperatorBounds (n := n) g₀ a₂ := by
  obtain ⟨C₂h, C₂l, hhigh, hlow, hmargin, hsmall⟩ := h
  exact ⟨C₂h, C₂l, hhigh, hlow, hmargin.trans_lt hq, hsmall⟩

private theorem ambient_h2_coefficient_contraction
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (ha : ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w a₂)
    (hanorm : ‖a₂‖ ≤ (ambientH2ControlBounds c₀ g ht he hr hEU hleft β hG).val *
      (Real.sqrt T + (1 + T) * ρ / 4))
    (hbound : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ)
    (hJ : ∀ t ∈ Icc 0 T, ‖((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
      (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap) (w t)‖ ≤
      (ScalarVectorTimeCoefficients.radius (ambientCoefficients c₀ g ht he hr hEU hleft β hG))) :
    parameterDerivativeOperatorBounds (n := n) (c₀.pullbackMetric (g 0)) a₂ := by
  have hclose₂ := ambientDiffusionH2ClosenessAtState c₀ g ht he hr hEU hleft β hG
    (hT.le.trans hTρ) hTρ w a₂ ha hbound hJ
  exact ambientParameterDerivativeContractionAtState c₀ g ht he hr hEU hleft β hG
    hT hTρ hρδ a₂ hclose₂ hanorm

private def ambientSobolevEquation
    (T : ℝ) (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) : Prop :=
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))
    let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
    (∀ᵐ t ∂timeMeasure T,
      L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t)

private theorem ambient_parameterDerivative_forcing_lift_for_coefficients
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (ha : ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w a₂)
    (hb : ambientReactionProjection c₀ g ht he hr hEU hleft β hG w b₂)
    (hanorm : ‖a₂‖ ≤ (ambientH2ControlBounds c₀ g ht he hr hEU hleft β hG).val *
      (Real.sqrt T + (1 + T) * ρ / 4))
    (hbound : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ)
    (hJ : ∀ t ∈ Icc 0 T, ‖((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
      (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap) (w t)‖ ≤
      (ScalarVectorTimeCoefficients.radius (ambientCoefficients c₀ g ht he hr hEU hleft β hG)))
    (heq : ambientSobolevEquation c₀ g ht he hr hEU hleft β hG T hT gforce w) :
    ∃ FH : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T,
      parameterDerivativeDuhamelForcing (ι := Fin n) (c₀.pullbackMetric (g 0)) 0 hT gforce =
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := c₀.pullbackMetric (g 0)) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
              2 (timeMeasure T) FH := by
  obtain ⟨C₂h, C₂l, hC₂h, hC₂l, hsmallh, hsmalll⟩ :=
    ambient_h2_coefficient_contraction c₀ g ht he hr hEU hleft β hG
      hT hTρ hρδ w a₂ ha hanorm hbound hJ
  have heq' := (show ambientSobolevEquation c₀ g ht he hr hEU hleft β hG T hT gforce w from heq)
  exact ambientParameterDerivativeOperatorLift c₀ g ht he hr hEU hleft β hG
    T hT gforce w a₂ b₂ ha hb heq' C₂h C₂l hC₂h hC₂l hsmallh hsmalll

private abbrev ambientH2CoefficientsAtState
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) :=
  (ambientH2ControlBounds c₀ g ht he hr hEU hleft β hG).property.choose_spec
    hT hTρ (hρδ.trans (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).property.2.1)
    gforce w

private theorem ambient_parameterDerivative_forcing_lift_at_small_state :
    ambientParameterDerivativeLiftAtControlRadius c₀ g ht he hr hEU hleft β hG
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG)
      (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
      ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
        (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
      (circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)) := by
  unfold ambientParameterDerivativeLiftAtControlRadius
  intro ρ T hT hTρ hρδ gforce field w alpha reaction L Q m hw hwu hbound hJ hforce heq
  obtain ⟨a₂, b₂, ha, hb, hanorm, _⟩ :=
    ambientH2CoefficientsAtState c₀ g ht he hr hEU hleft β hG
      hT hTρ hρδ gforce w hw hwu hbound hforce
  have hpa : ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w a₂ := ha
  have hpb : ambientReactionProjection c₀ g ht he hr hEU hleft β hG w b₂ := hb
  have heq' : ambientSobolevEquation c₀ g ht he hr hEU hleft β hG T hT gforce w := by
    simpa only [ambientSobolevEquation] using heq
  exact ambient_parameterDerivative_forcing_lift_for_coefficients c₀ g ht he hr hEU hleft β hG
    hT hTρ hρδ gforce w a₂ b₂ hpa hpb hanorm hbound hJ heq'



private def ambientParameterDerivativeLiftOfSmallState : Prop :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ δ ≤ 1 ∧
    ambientParameterDerivativeLiftAtRadius c₀ g ht he hr hEU hleft β hG δ

private theorem ambient_parameterDerivative_forcing_lift_of_small_state :
    ambientParameterDerivativeLiftOfSmallState c₀ g ht he hr hEU hleft β hG := by
  unfold ambientParameterDerivativeLiftOfSmallState
  intro C
  let co := ambientH2Control c₀ g ht he hr hEU hleft β hG
  let control := ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG
  refine ⟨control.val, control.property.1,
    control.property.2.1.trans co.property.2.1,
    control.property.2.1.trans co.property.2.2.1, ?_⟩
  exact ambient_parameterDerivative_forcing_lift_at_small_state c₀ g ht he hr hEU hleft β hG

end

private abbrev parameterDerivativeHighField
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :=
(ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ)))).comp
      ((AddCircle.parameterDerivativeHsPi (ι := Fin n) g₀ 2).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := g₀) (r := 0) (s := 0)
            (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))))

section

variable (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)

variable (gforce FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)

private theorem heatDuhamel_zero_eq_maximalRegularity
    (G : timeL2 (CircleHsPi g₀ (Fin n) ((0 : ℕ) : ℝ)) T) :
    heatDuhamelVectorField (g := g₀) (r := 0) (s := 0)
      (a := ((0 : ℕ) : ℝ)) hT 0 G =
    maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
      (a := ((0 : ℕ) : ℝ)) hT 0 G := by
  have hc := tensorResolventL2_isCompactOperator (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g₀ 0 0
  simpa only [map_zero] using heatDuhamelVectorField_inclusion
    (g := g₀) (r := 0) (s := 0) (a := ((0 : ℕ) : ℝ)) hT hc 0 G

private theorem heatDuhamel_zero_inclusion_eq_maximalRegularity :
    let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let J₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2))
    J₂.compLpL 2 (timeMeasure T)
      (heatDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 FH) =
      maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((0 : ℕ) : ℝ)) hT 0 (J₀.compLpL 2 (timeMeasure T) FH) := by
  intro J₀ J₂
  have hc := tensorResolventL2_isCompactOperator (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g₀ 0 0
  have hi := heatDuhamelVectorField_compLpL_tensorHsInclusion (ι := Fin n)
    (g := g₀) (r := 0) (s := 0) (a := ((0 : ℕ) : ℝ)) (b := ((1 : ℕ) : ℝ))
    (by norm_num) hT hc 0 FH
  change J₂.compLpL 2 (timeMeasure T) _ =
    heatDuhamelVectorField hT _ (J₀.compLpL 2 (timeMeasure T) FH) at hi
  rw [map_zero] at hi
  exact hi.trans (heatDuhamel_zero_eq_maximalRegularity g₀ hT _)

private theorem parameterDerivative_field_lift_of_forcing_lift :
    let G := parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce
    let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    let Dh := parameterDerivativeHighField (n := n) g₀
    let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let J₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2))
    G = J₀.compLpL 2 (timeMeasure T) FH →
    Dh.compLpL 2 (timeMeasure T) field = J₂.compLpL 2 (timeMeasure T)
      (heatDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 FH) := by
  intro G field Dh J₀ J₂ hG
  let V := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
    (a := ((0 : ℕ) : ℝ)) hT 0 G
  have hder : Dh.compLpL 2 (timeMeasure T) field = V :=
    (parameterDerivative_duhamel_vector_eq g₀ 0 hT gforce).1
  have hi := heatDuhamel_zero_inclusion_eq_maximalRegularity g₀ hT FH
  change J₂.compLpL 2 (timeMeasure T) _ =
    maximalRegularityDuhamelVectorField hT 0 (J₀.compLpL 2 (timeMeasure T) FH) at hi
  rw [← hG] at hi
  exact hder.trans hi.symm

end

section

variable (c₀ : SmoothImmersion (I := I) (M := M))

variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}

variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)

variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)

variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private def ambientSobolevSolutionOfCoefficientsWithRadiusLe
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (C : ScalarVectorTimeCoefficients (c₀.pullbackMetric (g 0))
      (curveShorteningChartDiffusionCoefficient (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n)
      (fun z j => curveShorteningParametricChartReaction (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j)
      (firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β)
      (ambientFirstJet c₀ (g 0) e he))
    {δ : ℝ} (hδ : 0 < δ) :
    {sol : PrecomposedCircleSolution (c₀.pullbackMetric (g 0))
      (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
      ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
        (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
      (ScalarVectorTimeCoefficients.radius_pos C) (ScalarVectorTimeCoefficients.diffusion C) (ScalarVectorTimeCoefficients.reaction C) //
      precomposedCircleSolutionRadius (c₀.pullbackMetric (g 0))
        (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
        ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
          (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
            (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
        (ScalarVectorTimeCoefficients.radius_pos C) (ScalarVectorTimeCoefficients.diffusion C) (ScalarVectorTimeCoefficients.reaction C) sol ≤ δ} :=
  precomposedCircleSolutionWithRadiusLe (c₀.pullbackMetric (g 0))
    (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
    ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
      (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
    (ScalarVectorTimeCoefficients.radius_pos C) hδ (ScalarVectorTimeCoefficients.diffusion C) (ScalarVectorTimeCoefficients.reaction C) (ScalarVectorTimeCoefficients.diffusionLipschitz C) (ScalarVectorTimeCoefficients.reactionLipschitz C)
    (ScalarVectorTimeCoefficients.diffusion_lipschitz C) (ScalarVectorTimeCoefficients.reaction_lipschitz C)
    (initial_diffusion_coefficients c₀ g he hr hEU hleft β C)


private abbrev ambientCappedSobolevSolutionSpec {δ : ℝ} (hδ : 0 < δ) :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let sol := ambientSobolevSolutionOfCoefficientsWithRadiusLe c₀ g he hr hEU hleft β C hδ
  precomposed_circle_solution_exists_with_radius_le g₀ f₀ J (ScalarVectorTimeCoefficients.radius_pos C)
    (ScalarVectorTimeCoefficients.diffusion C) (ScalarVectorTimeCoefficients.reaction C) sol.val sol.property

private def parameterDerivativeForcingFieldLift
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) : Prop :=
  let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
    (a := ((1 : ℕ) : ℝ)) hT 0 gforce
  ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
    parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce =
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
            2 (timeMeasure T) FH ∧
    (parameterDerivativeHighField (n := n) g₀).compLpL 2 (timeMeasure T) field =
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2))).compLpL
            2 (timeMeasure T)
              (heatDuhamelVectorField (g := g₀) (r := 0) (s := 0)
                (a := ((1 : ℕ) : ℝ)) hT 0 FH)

private def ambientSobolevSolutionFacts (ρ : ℝ) {T : ℝ} (hT : 0 < T)
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T) : Prop :=
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) := c₀.pullbackMetric (g 0)
    let f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1) := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let L : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
        (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) →L[ℝ] CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
          let field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0)
              (a := ((1 : ℕ) : ℝ)) hT 0 gforce
          u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
              (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0)
                (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
            (∀ᵐ t ∂(timeMeasure T), ‖K (field t)‖ ≤ ρ) ∧
            u.toFunL2 = (circleHsPiInclusion g₀ (Fin n)
              (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
                2 (timeMeasure T) field ∧
            timeH1.trace0 _ T u = 0 ∧
            timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + gforce ∧
            ‖gforce‖ ≤ ρ / 4 ∧
            (∀ᵐ t ∂(timeMeasure T), ∃ z : Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) (ScalarVectorTimeCoefficients.radius C),
              (z : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) = J (K (field t)) ∧
              L (field t) + gforce t = m (tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                ((ScalarVectorTimeCoefficients.diffusion C) t z)) (Q (f₀ + field t)) +
                circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  ((ScalarVectorTimeCoefficients.reaction C) t z)) ∧
            ∃ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
              ContinuousOn w (Set.Icc 0 T) ∧
              (∀ t ∈ Set.Icc 0 T,
                circleHsPiInclusion g₀ (Fin n)
                  (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by linarith)
                  (w t) = u.toFun t) ∧
              w =ᵐ[timeMeasure T] (fun t => K (field t)) ∧
              (∀ t ∈ Set.Icc 0 T, ‖w t‖ ≤ ρ) ∧ w 0 = 0 ∧
              (∀ t ∈ Set.Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) ∧
              let alpha : ℝ → TensorHs g₀ 0 0 ((1 : ℕ) : ℝ) := fun t => tensorHsCongrL g₀ 0 0
                (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))
              let reaction : ℝ → CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := fun t => circleHsPiCongr g₀ (Fin n)
                (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))
              let S : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g₀ 0 0 1 := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
                (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
              let P : CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) →L[ℝ] CircleHsPi g₀ (Fin n) 1 := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => S)
              let K₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
                CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := circleHsPiInclusion g₀ (Fin n)
                (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              let f : ℝ → ℝ → Fin n → ℝ := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P (K₀ f₀ + u.toFun t))
                (x : AddCircle (1 : ℝ))
              (∀ᵐ t ∂timeMeasure T,
                L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) ∧
              (∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
                HasDerivAt (fun s => f s x)
                  (scalarH1ToContinuous g₀ (S (alpha t)) (x : AddCircle (1 : ℝ)) •
                    deriv (deriv (f t)) x + scalarH1PiToContinuous g₀ (P (reaction t))
                      (x : AddCircle (1 : ℝ))) t)

private def ambientSobolevSolutionWithParameterDerivativeLift : Prop :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ ρ ≤ 1 ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
      ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
        ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce

private theorem ambient_parameterDerivative_lift_of_solution_facts
    {δ ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ) (hρδ : ρ ≤ δ)
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : ambientParameterDerivativeLiftAtRadius c₀ g ht he hr hEU hleft β hG δ) :
    parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce := by
  rcases hfacts with ⟨_, _, _, _, _, hforce, _, w,
    hw, _, hwu, hbound, _, hJ, heq', _⟩
  obtain ⟨FH, hFH⟩ := hlift hT hTρ hρδ gforce w hw hwu hbound hJ hforce heq'
  exact ⟨FH, hFH, parameterDerivative_field_lift_of_forcing_lift
    (c₀.pullbackMetric (g 0)) hT gforce FH hFH⟩


private theorem ambient_sobolev_solution_exists_with_parameterDerivative_lift_of_radius
    {δ : ℝ} (hδ : 0 < δ)
    (hlift : ambientParameterDerivativeLiftAtRadius c₀ g ht he hr hEU hleft β hG δ) :
    ambientSobolevSolutionWithParameterDerivativeLift c₀ g ht he hr hEU hleft β hG := by
  unfold ambientSobolevSolutionWithParameterDerivativeLift
  intro C g₀
  obtain ⟨ρ, hρ, hρC, hρ1, hρδ, T, hT, hTρ, u, gforce, hpacket⟩ :=
    ambientCappedSobolevSolutionSpec c₀ g ht he hr hEU hleft β hG hδ
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hpacket, ?_⟩
  exact ambient_parameterDerivative_lift_of_solution_facts c₀ g ht he hr hEU hleft β hG
    hT hTρ hρδ u gforce hpacket hlift


private theorem ambient_sobolev_solution_exists_with_parameterDerivative_lift :
    ambientSobolevSolutionWithParameterDerivativeLift c₀ g ht he hr hEU hleft β hG := by
  obtain ⟨δ, hδ, _, _, hlift⟩ :=
    ambient_parameterDerivative_forcing_lift_of_small_state c₀ g ht he hr hEU hleft β hG
  exact ambient_sobolev_solution_exists_with_parameterDerivative_lift_of_radius
    c₀ g ht he hr hEU hleft β hG hδ hlift

private def ambientSobolevFourthOrderLift
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) : Prop :=
  ∃ field₄ : timeL2 (CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2)) T,
    (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))).compLpL
          2 (timeMeasure T) field₄ =
      maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce

private theorem ambient_fourth_order_lift_of_parameterDerivative_lift
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hlift : parameterDerivativeForcingFieldLift g₀ hT gforce) :
    ambientSobolevFourthOrderLift g₀ hT gforce := by
  rcases hlift with ⟨FH, _, hfield⟩
  let U := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
    (a := ((1 : ℕ) : ℝ)) hT 0 gforce
  let V := heatDuhamelVectorField (g := g₀) (r := 0) (s := 0)
    (a := ((1 : ℕ) : ℝ)) hT 0 FH
  let Dh : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 2) := parameterDerivativeHighField g₀
  let J₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2))
  change Dh.compLpL 2 (timeMeasure T) U = J₂.compLpL 2 (timeMeasure T) V at hfield
  apply AddCircle.exists_timeL2_tensorHsInclusion_eq_of_parameterDerivative_lift
    g₀ 1 (σ := ((0 : ℕ) : ℝ) + 2) (by norm_num) U V
  filter_upwards [Dh.coeFn_compLpL U, J₂.coeFn_compLpL V] with t hDh hJ
  intro i
  have ht : Dh (U t) = J₂ (V t) := by
    rw [← hDh, ← hJ]
    exact congrArg (fun z : timeL2 (CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 2)) T => z t) hfield
  have hi := congrArg (fun z => z i) ht
  simpa only [Dh, J₂, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.piLpMap_apply, AddCircle.parameterDerivativeHsPi_apply] using hi

private def ambientSobolevSolutionWithFourthOrderLift : Prop :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ ρ ≤ 1 ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
      ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
        ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce ∧
          ambientSobolevFourthOrderLift g₀ hT gforce

private theorem ambient_sobolev_solution_exists_with_fourth_order_lift :
    ambientSobolevSolutionWithFourthOrderLift c₀ g ht he hr hEU hleft β hG := by
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift⟩ :=
    ambient_sobolev_solution_exists_with_parameterDerivative_lift
      c₀ g ht he hr hEU hleft β hG
  exact ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift,
    ambient_fourth_order_lift_of_parameterDerivative_lift
      (c₀.pullbackMetric (g 0)) hT gforce hlift⟩

private theorem ambient_spatial_contDiff_two_of_parameterDerivative_forcing_lift
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hlift : parameterDerivativeForcingFieldLift g₀ hT gforce) :
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let u := maximalRegularityDuhamelVectorMap (g := g₀) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t))
      (x : AddCircle (1 : ℝ))
    (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t)) ∧
      ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f p.1)) p.2) (Icc 0 T ×ˢ univ) := by
  intro P u S f
  obtain ⟨FH, hFH, _⟩ := hlift
  obtain ⟨w, hw, hwlo, _⟩ :=
    exists_continuousOn_representative_of_parameterDerivative_forcing_lift g₀ 0 hT gforce FH hFH
  have h := AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
    g₀ 2 (fun t => P f₀ + S (u.toFun t))
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)) (f₀ + w t))
    ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))).continuous.comp_continuousOn
      (continuousOn_const.add hw)) (fun t ht => by
      apply PiLp.ext
      intro i
      simp only [ContinuousLinearMap.piLpMap_apply, PiLp.add_apply,
        ← tensorHsInclusion_trans_apply, map_add]
      change _ = (P f₀) i + (S (u.toFun t)) i
      congr 1
      have hwi := congrArg (fun z => z i) (hwlo t ht)
      have hwi' := congrArg (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))) hwi
      simpa only [S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
        ← tensorHsInclusion_trans_apply] using hwi')
  simpa only [f, iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat] using h

private theorem ambient_sobolev_solution_exists_with_contDiff_two :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift g₀ hT gforce ∧
            ambientSobolevFourthOrderLift g₀ hT gforce ∧
            let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t))
              (x : AddCircle (1 : ℝ))
            (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t)) ∧
              ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f p.1)) p.2) (Icc 0 T ×ˢ univ) := by
  intro C g₀ f₀ P S
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hfour⟩ :=
    ambient_sobolev_solution_exists_with_fourth_order_lift c₀ g ht he hr hEU hleft β hG
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hfour, ?_⟩
  rw [hfacts.1]
  exact ambient_spatial_contDiff_two_of_parameterDerivative_forcing_lift g₀ hT f₀ gforce hlift


private theorem circleHsPi_eq_of_inclusion_eq
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (V : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (h : circleHsPiInclusion g₀ (Fin n) (by linarith :
        ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) v =
      circleHsPiInclusion g₀ (Fin n) (by linarith :
        ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2) V) :
    v = circleHsPiInclusion g₀ (Fin n) (by linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) V := by
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  have hi := congrArg (fun z => z i) h
  simpa only [circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
    ← tensorHsInclusion_trans_apply] using hi

private theorem scalarVectorTimeCoefficients_rhs_continuousOn
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    {T : ℝ}
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T)) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))
      ContinuousOn (fun t => m (alpha t) (Q (f₀ + W t)) + reaction t) (Icc 0 T) := by
  intro K Q m hJW alpha reaction
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) (ScalarVectorTimeCoefficients.radius C) := fun t =>
    ⟨J (K (W t)), by simpa only [Metric.mem_closedBall, dist_zero_right] using hJW t t.2⟩
  have hz : Continuous z :=
    (J.continuous.comp (K.continuous.comp
      (continuousOn_iff_continuous_domRestrict.mp hW))).subtype_mk _
  have halpha : ContinuousOn alpha (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ((tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))).continuous.comp
        ((ScalarVectorTimeCoefficients.diffusion_lipschitz C).continuous.comp (continuous_subtype_val.prodMk hz))).congr
    intro t
    change tensorHsCongrL g₀ 0 0 _ ((ScalarVectorTimeCoefficients.diffusion C) t (z t)) =
      tensorHsCongrL g₀ 0 0 _ (extendClosedBall _ (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))
    exact congrArg (tensorHsCongrL g₀ 0 0 _) (extendClosedBall_apply
      (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))) (z t).2).symm
  have hreaction : ContinuousOn reaction (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ((circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))).continuous.comp
        ((ScalarVectorTimeCoefficients.reaction_lipschitz C).continuous.comp (continuous_subtype_val.prodMk hz))).congr
    intro t
    change circleHsPiCongr g₀ (Fin n) _ ((ScalarVectorTimeCoefficients.reaction C) t (z t)) =
      circleHsPiCongr g₀ (Fin n) _ (extendClosedBall _ (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))
    exact congrArg (circleHsPiCongr g₀ (Fin n) _) (extendClosedBall_apply
      (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))) (z t).2).symm
  have hRHS : ContinuousOn (fun t => m (alpha t) (Q (f₀ + W t)) + reaction t) (Icc 0 T) :=
    ((m.continuous.comp_continuousOn halpha).clm_apply
      (Q.continuous.comp_continuousOn (continuousOn_const.add hW))).add hreaction
  exact hRHS

private def scalarVectorClassicalTimeEquation
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    {ρ T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) : Prop :=
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    ∃ W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2),
      ContinuousOn W (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, K₀ (W t) = u.toFun t) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖K (W t)‖ ≤ ρ) ∧
      (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C)) ∧
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))
      ContinuousOn (fun t => m (alpha t) (Q (f₀ + W t)) + reaction t) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt u.toFun
        (m (alpha t) (Q (f₀ + W t)) + reaction t) (Icc 0 T) t

private theorem scalarVectorTimeCoefficients_hasDerivWithinAt_of_parameterDerivative_lift
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    {ρ T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) :
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField hT 0 gforce
    u = maximalRegularityDuhamelVectorMap hT 0 gforce →
    parameterDerivativeForcingFieldLift g₀ hT gforce →
    ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
    (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
      (by linarith : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (w t) = u.toFun t) →
    (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
    (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    (∀ᵐ t ∂timeMeasure T,
      L (field t) + gforce t =
        m (tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))))
          (Q (f₀ + field t)) +
        circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))) →
    scalarVectorClassicalTimeEquation (ρ := ρ) g₀ F G S u₀ C hT f₀ J u gforce := by
  intro Q m L field hu hlift w hwlow hwbound hJ heq
  let K := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
  let K₀ := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
  change ∃ W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2), _
  rcases hlift with ⟨FH, hFH, _⟩
  obtain ⟨W, hW, hWlow, hWfield⟩ :=
    exists_continuousOn_representative_of_parameterDerivative_forcing_lift
      g₀ 0 hT gforce FH hFH
  have hWlow' : ∀ t ∈ Icc 0 T, K₀ (W t) = u.toFun t := by
    intro t htt
    rw [hu]
    exact hWlow t htt
  have hwW (t : ℝ) (htt : t ∈ Icc 0 T) : w t = K (W t) :=
    circleHsPi_eq_of_inclusion_eq g₀ (w t) (W t)
      ((hwlow t htt).trans (hWlow' t htt).symm)
  have hJW (t : ℝ) (htt : t ∈ Icc 0 T) : ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C) := by
    rw [← hwW t htt]
    exact hJ t htt
  refine ⟨W, hW, hWlow', hWfield, ?_, hJW, ?_⟩
  · intro t htt
    rw [← hwW t htt]
    exact hwbound t htt
  intro alpha reaction
  have hRHS : ContinuousOn (fun t => m (alpha t) (Q (f₀ + W t)) + reaction t) (Icc 0 T) :=
    scalarVectorTimeCoefficients_rhs_continuousOn g₀ _ _ _ _ C f₀ J W hW hJW
  refine ⟨hRHS, ?_⟩
  have hder : u.deriv = L.compLpL 2 (timeMeasure T) field + gforce := by
    rw [hu]
    exact maximalRegularityDuhamelVectorMap_timeDeriv_eq hT
      (tensorResolventL2_isCompactOperator
        (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g₀ 0 0) 0 gforce
  have hrep : u.deriv =ᵐ[timeMeasure T]
      (fun t => m (alpha t) (Q (f₀ + W t)) + reaction t) := by
    rw [hder]
    filter_upwards [Lp.coeFn_add (L.compLpL 2 (timeMeasure T) field) gforce,
      L.coeFn_compLpL field, heq, hWfield, ae_restrict_mem measurableSet_Icc]
      with t hadd hL htEq htW htmem
    rw [hadd, Pi.add_apply, hL, htEq, ← htW]
    change m _ (Q (f₀ + W t)) + _ = m _ (Q (f₀ + W t)) + _
    rw [hwW t htmem]
  intro t htt
  exact u.hasDerivWithinAt_toFun_of_continuousOn hRHS hrep htt

private theorem ambientCoefficients_eval_of_sobolev_representative
    {ρ T : ℝ} (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F := fun t (x : ℝ) => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    let alpha := fun t => tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))
    let reaction := fun t => circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))
    (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by norm_num) (w t) = u.toFun t) →
    (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ ScalarVectorTimeCoefficients.radius C) →
    ∀ t ∈ Icc 0 T, ∀ x : ℝ,
      let q := (t, F t x, deriv (F t) x)
      q ∈ curveShorteningChartFirstJetDomain D
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∧
      scalarH1ToContinuous g₀
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) (alpha t))
        (x : AddCircle (1 : ℝ)) = curveShorteningChartDiffusionCoefficient
          (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β q ∧
      WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S (reaction t))
        (x : AddCircle (1 : ℝ))) = curveShorteningParametricChartReaction
          (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β q := by
  intro C g₀ f₀ J P S F alpha reaction hwu hJ t htt x
  have hcoeff {a b : ℝ} (hab : a = b) (z : TensorHs g₀ 0 0 a) :
      (tensorHsCongr g₀ 0 0 hab z).coeff = z.coeff := by
    cases hab
    rfl
  let w₂ := circleHsPiCongr g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) (w t)
  have hv : J (w t) ∈ Metric.closedBall 0 (ScalarVectorTimeCoefficients.radius C) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hJ t htt
  let v : Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
      (ScalarVectorTimeCoefficients.radius C) := ⟨J (w t), hv⟩
  have hvJ : v.val = circleFirstJet g₀ w₂ := rfl
  have htime : t ∈ Icc 0 (ScalarVectorTimeCoefficients.radius C) :=
    ⟨htt.1, htt.2.trans (hTρ.trans hρC)⟩
  have hgeom := ambientCoefficients_eval_of_eq_circleFirstJet
    c₀ g ht he hr hEU hleft β hG t htime w₂ v hvJ x
  have hF : F t = fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) +
      WithLp.toLp 2 (fun i => scalarH1ToContinuous g₀
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1) (w₂ i))
        (y : AddCircle (1 : ℝ))) := by
    funext y
    apply PiLp.ext
    intro i
    change scalarH1ToContinuous g₀ ((P f₀ + S (u.toFun t)) i)
      (y : AddCircle (1 : ℝ)) = _
    rw [PiLp.add_apply, map_add, ContinuousMap.add_apply]
    congr 1
    · exact scalarH1ToContinuous_ambientSobolev c₀ (g 0) e he (by norm_num) _ i
    · rw [← hwu t htt]
      apply congrArg (fun z => scalarH1ToContinuous g₀ z (y : AddCircle (1 : ℝ)))
      apply TensorHs.ext
      simp only [S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
        tensorHsInclusion_coeff, w₂, circleHsPiCongr_apply, tensorHsCongrL_apply, hcoeff]
  change (t, F t x, deriv (F t) x) ∈ _ ∧ _ ∧ _
  have hgeom' : (t, F t x, deriv (F t) x) ∈ curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∧
    scalarH1ToContinuous g₀ (ScalarVectorTimeCoefficients.diffusion C t v)
      (x : AddCircle (1 : ℝ)) = curveShorteningChartDiffusionCoefficient
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (t, F t x, deriv (F t) x) ∧
    ∀ j, scalarH1ToContinuous g₀ (ScalarVectorTimeCoefficients.reaction C t v j)
      (x : AddCircle (1 : ℝ)) = curveShorteningParametricChartReaction
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
          (t, F t x, deriv (F t) x) j := by
    simpa only [hF] using hgeom
  refine ⟨hgeom'.1, ?_, ?_⟩
  · rw [← hgeom'.2.1]
    apply congrArg (fun z => scalarH1ToContinuous g₀ z (x : AddCircle (1 : ℝ)))
    apply TensorHs.ext
    simp only [alpha, extendClosedBall_apply _ _ _ _ hv,
      tensorHsInclusion_coeff, tensorHsCongrL_apply, hcoeff, v]
  · apply PiLp.ext
    intro i
    rw [← hgeom'.2.2 i]
    change scalarH1ToContinuous g₀ ((S (reaction t)) i) (x : AddCircle (1 : ℝ)) = _
    apply congrArg (fun z => scalarH1ToContinuous g₀ z (x : AddCircle (1 : ℝ)))
    apply TensorHs.ext
    simp only [reaction, extendClosedBall_apply _ _ _ _ hv, S, circleHsPiInclusion,
      ContinuousLinearMap.piLpMap_apply, circleHsPiCongr_apply,
      tensorHsInclusion_coeff, tensorHsCongrL_apply, hcoeff, v]

private theorem ambient_firstJet_mem_of_sobolev_solution_facts
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F := fun t (x : ℝ) => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    ∀ t ∈ Icc 0 T, ∀ x : ℝ, (t, F t x, deriv (F t) x) ∈
      curveShorteningChartFirstJetDomain D
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β := by
  intro g₀ f₀ P S F t htt x
  rcases hfacts with ⟨_, _, _, _, _, _, _, w, _, hwu, _, _, _, hJ, _, _⟩
  exact (ambientCoefficients_eval_of_sobolev_representative c₀ g ht he hr hEU hleft β hG
    hTρ hρC u w hwu hJ t htt x).1

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambient_first_order_regular_of_sobolev_representative
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {T : ℝ}
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric g) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric g) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hw : ContinuousOn w (Icc 0 T))
    (hwu : ∀ t ∈ Icc 0 T, circleHsPiInclusion (c₀.pullbackMetric g) (Fin n)
      (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by norm_num) (w t) = u.toFun t)
    (hu₀ : u.toFun 0 = 0) :
    let g₀ := c₀.pullbackMetric g
    let f₀ := ambientSobolev c₀ g e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F := fun t (x : ℝ) => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    (∀ t, Function.Periodic (F t) 1) ∧
      ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1) (Icc 0 1 ×ˢ Icc 0 T) ∧
      ContinuousOn (fun p : ℝ × ℝ => deriv (F p.2) p.1) (Icc 0 1 ×ˢ Icc 0 T) ∧
      ∀ x, F 0 x = e (c₀.map (x : AddCircle (1 : ℝ))) := by
  intro g₀ f₀ P S F
  let f := fun t (x : ℝ) =>
    scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ))
  let K := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
  have h := AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
    g₀ 1 (fun t => P f₀ + S (u.toFun t)) (fun t => K f₀ + w t)
    (continuousOn_const.add hw) (fun t ht => by
      apply PiLp.ext
      intro i
      simp only [ContinuousLinearMap.piLpMap_apply, PiLp.add_apply, map_add]
      change _ = (P f₀) i + (S (u.toFun t)) i
      apply congrArg₂ (· + ·)
      · exact (tensorHsInclusion_trans_apply
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) (f₀ i)).symm
      · have hi := congrArg (fun z => z i) (hwu t ht)
        have hi' := congrArg (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))) hi
        simpa only [S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
          ← tensorHsInclusion_trans_apply] using hi')
  have hf : ∀ t ∈ Icc 0 T, ContDiff ℝ 1 (f t) := h.1
  have hd : ContinuousOn (fun p : ℝ × ℝ => deriv (f p.1) p.2) (Icc 0 T ×ˢ univ) := by
    simpa only [f, iteratedDeriv_succ, iteratedDeriv_zero] using h.2
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have hder (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) :
      deriv (F t) x = L (deriv (f t) x) := by
    exact ((PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (f t x)).comp_hasDerivAt x
      ((hf t ht).differentiable (by norm_num) x).hasDerivAt).deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t x
    simp only [F, AddCircle.coe_add_period]
  · apply L.continuous.comp_continuousOn
    have hstate : ContinuousOn (fun t => P f₀ + S (u.toFun t)) (Icc 0 T) :=
      continuousOn_const.add (S.continuous.comp_continuousOn u.continuousOn_toFun)
    exact (((scalarH1PiToContinuous g₀).continuous.comp_continuousOn hstate).comp
      continuousOn_snd (fun _ hp => hp.2)).eval
        ((AddCircle.continuous_mk' 1).comp continuous_fst).continuousOn
  · have hswap : ContinuousOn (fun p : ℝ × ℝ => (p.2, p.1))
        (Icc 0 1 ×ˢ Icc 0 T) := continuousOn_snd.prodMk continuousOn_fst
    have hd' := L.continuous.comp_continuousOn
      (hd.comp hswap (fun _ hp => ⟨hp.2, mem_univ _⟩))
    apply hd'.congr
    intro p hp
    exact hder p.2 hp.2 p.1
  · intro x
    simp only [F, hu₀, map_zero, add_zero]
    apply PiLp.ext
    intro i
    exact congrArg (fun z => z i)
      (scalarH1PiToContinuous_ambientSobolev c₀ g e he
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2) (x : AddCircle (1 : ℝ)))

private theorem ambient_classical_time_equation_of_parameterDerivative_lift
    {ρ T : ℝ} (hT : 0 < T)
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    scalarVectorClassicalTimeEquation (ρ := ρ) g₀ _ _ _ _ C hT f₀ J u gforce := by
  intro C g₀ f₀ J
  rcases hfacts with ⟨hu, _, _, _, _, _, _, w,
    _, hwlow, _, hwbound, _, hJ, heq, _⟩
  exact scalarVectorTimeCoefficients_hasDerivWithinAt_of_parameterDerivative_lift
    g₀ _ _ _ _ C hT f₀ J u gforce hu hlift w hwlow hwbound
    (by simpa only [C, g₀, J] using hJ)
    (by simpa only [C, g₀, f₀, J] using heq)

private theorem ambient_chart_equation_of_parameterDerivative_lift
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    ∀ t ∈ Icc 0 T, ∀ x : ℝ, HasDerivWithinAt (fun τ => F τ x)
      (curveShorteningParametricChartRhs
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
        (t, F t x, deriv (F t) x, deriv (deriv (F t)) x)) (Icc 0 T) t := by
  intro g₀ f₀ P S F
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let K := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
  let K₀ := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
  have hresult := ambient_classical_time_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT u gforce hfacts hlift
  obtain ⟨W, _, hWlo, _, _, hJW, htime⟩ := hresult
  let alpha := fun t => tensorHsCongrL g₀ 0 0
    (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))
  let reaction := fun t => circleHsPiCongr g₀ (Fin n)
    (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))
  have hlink (t : ℝ) (htt : t ∈ Icc 0 T) :
      K₀ (f₀ + W t) = K₀ f₀ + u.toFun t := by rw [map_add, hWlo t htt]
  have hclassical := hasDerivWithinAt_of_circle_sobolev_equation g₀ u.toFun
    (fun t => f₀ + W t) (K₀ f₀) alpha reaction hlink htime.2
  have hwlow (t : ℝ) (htt : t ∈ Icc 0 T) :
      circleHsPiInclusion g₀ (Fin n)
        (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by norm_num) (K (W t)) = u.toFun t := by
    rw [← hWlo t htt]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (W t i)).symm
  have hcoeff := ambientCoefficients_eval_of_sobolev_representative
    c₀ g ht he hr hEU hleft β hG hTρ hρC u (fun t => K (W t)) hwlow hJW
  let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t))
    (x : AddCircle (1 : ℝ))
  have hlo (t : ℝ) : S (K₀ f₀ + u.toFun t) = P f₀ + S (u.toFun t) := by
    rw [map_add]
    congr 1
  have hc : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
      HasDerivWithinAt (fun τ => f τ x)
        (scalarH1ToContinuous g₀
          (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) (alpha t))
            (x : AddCircle (1 : ℝ)) • deriv (deriv (f t)) x +
          scalarH1PiToContinuous g₀ (S (reaction t)) (x : AddCircle (1 : ℝ))) (Icc 0 T) t := by
    dsimp only [f]
    simp_rw [← hlo]
    exact hclassical
  intro t htt x
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  have hd (q : ℝ → (Fin n → ℝ)) (hq : Differentiable ℝ q) :
      deriv (fun y => L (q y)) = fun y => L (deriv q y) := by
    funext y
    exact (L.hasFDerivAt.comp_hasDerivAt y (hq y).hasDerivAt).deriv
  have hf' : ContDiff ℝ 1 (deriv (f t)) := (hc t htt).1.deriv'
  have hsecond : deriv (deriv (F t)) x = L (deriv (deriv (f t)) x) := by
    change deriv (deriv (fun y => L (f t y))) x = _
    rw [hd (f t) ((hc t htt).1.differentiable (by norm_num))]
    rw [hd (deriv (f t)) (hf'.differentiable (by norm_num))]
  have hh := L.hasFDerivAt.comp_hasDerivWithinAt t ((hc t htt).2 x)
  have hdiff := (hcoeff t htt x).2.1
  have hreact := (hcoeff t htt x).2.2
  have hh' : HasDerivWithinAt (fun τ => F τ x)
      (scalarH1ToContinuous g₀
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) (alpha t))
          (x : AddCircle (1 : ℝ)) • deriv (deriv (F t)) x +
        WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S (reaction t))
          (x : AddCircle (1 : ℝ)))) (Icc 0 T) t := by
    rw [hsecond]
    change HasDerivWithinAt (fun τ => L (f τ x))
      (_ • L (deriv (deriv (f t)) x) +
        L (scalarH1PiToContinuous g₀ (S (reaction t)) (x : AddCircle (1 : ℝ))))
      (Icc 0 T) t
    simpa only [map_add, map_smul, Function.comp_def] using hh
  rw [hdiff, hreact] at hh'
  exact hh'

private theorem ambient_mem_range_of_parameterDerivative_lift [I.Boundaryless]
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    ∀ t ∈ Icc 0 T, ∀ x : ℝ, F t x ∈ range e := by
  intro g₀ f₀ P S F
  have hchart := ambient_chart_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  have hspatial := ambient_spatial_contDiff_two_of_parameterDerivative_forcing_lift
    g₀ hT f₀ gforce hlift
  have hu := hfacts.1
  rw [← hu] at hspatial
  rcases hfacts with ⟨_, _, _, _, _, _, _, w, hw, hwu, _, _, hw₀, _, _, _⟩
  have hu₀ : u.toFun 0 = 0 := by
    rw [← hwu 0 ⟨le_rfl, hT.le⟩, hw₀, map_zero]
  obtain ⟨hper, hcont, hDu, hinit⟩ :=
    ambient_first_order_regular_of_sobolev_representative c₀ (g 0) he u w hw hwu hu₀
  change ∀ t, Function.Periodic (F t) 1 at hper
  change ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1) (Icc 0 1 ×ˢ Icc 0 T) at hcont
  change ContinuousOn (fun p : ℝ × ℝ => deriv (F p.2) p.1) (Icc 0 1 ×ˢ Icc 0 T) at hDu
  change ∀ x, F 0 x = e (c₀.map (x : AddCircle (1 : ℝ))) at hinit
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  have hx (x t : ℝ) (htt : t ∈ Ioo 0 T) : ContDiffAt ℝ 2 (F t) x := by
    exact (L.contDiff.comp (hspatial.1 t ⟨htt.1.le, htt.2.le⟩)).contDiffAt
  have hrange := periodic_mem_range_of_retraction_equation_of_firstJet_mem
    g he hr hG hEU hleft β (u := fun x t => F t x) hT (fun x t => hper t x) hcont
    (fun x => by rw [hinit x]; exact mem_range_self _) hx hDu
    (fun x t htt => hjet t htt x)
    (fun x t htt => (hchart t ⟨htt.1.le, htt.2.le⟩ x).hasDerivAt
      (Icc_mem_nhds htt.1 htt.2))
  intro t htt x
  exact hrange x t htt

private theorem ambient_sobolev_solution_exists_with_mem_range [I.Boundaryless] :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ScalarVectorTimeCoefficients.radius C ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift g₀ hT gforce ∧
            ambientSobolevFourthOrderLift g₀ hT gforce ∧
            let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t))
              (x : AddCircle (1 : ℝ))
            (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t)) ∧
              ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f p.1)) p.2) (Icc 0 T ×ˢ univ) ∧
              ∀ t ∈ Icc 0 T, ∀ x : ℝ, WithLp.toLp 2 (f t x) ∈ range e := by
  intro C g₀ f₀ P S
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hfour, hc, hd⟩ :=
    ambient_sobolev_solution_exists_with_contDiff_two c₀ g ht he hr hEU hleft β hG
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hfour, hc, hd, ?_⟩
  exact ambient_mem_range_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift


private theorem ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift
    [I.Boundaryless] {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
    let c : CurveMap M := fun z t => r (d z t)
    (∀ z, c z 0 = c₀.map z) ∧
      (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
      (∀ t ∈ Icc 0 T, ContMDiff 𝓘(ℝ, ℝ) I 2 (fun x : ℝ => c.lift x t)) ∧
      c.ImmersedOn (I := I) (Icc 0 T) := by
  intro g₀ f₀ P S d c
  have himage := ambient_mem_range_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  have hspatial := ambient_spatial_contDiff_two_of_parameterDerivative_forcing_lift
    g₀ hT f₀ gforce hlift
  have hu := hfacts.1
  rw [← hu] at hspatial
  rcases hfacts with ⟨_, _, _, _, _, _, _, w, hw, hwu, _, _, hw₀, _, _, _⟩
  have hu₀ : u.toFun 0 = 0 := by
    rw [← hwu 0 ⟨le_rfl, hT.le⟩, hw₀, map_zero]
  obtain ⟨_, _, _, hinit⟩ :=
    ambient_first_order_regular_of_sobolev_representative c₀ (g 0) he u w hw hwu hu₀
  change ∀ x : ℝ, d (x : AddCircle (1 : ℝ)) 0 = e (c₀.map (x : AddCircle (1 : ℝ))) at hinit
  have hrange (z : AddCircle (1 : ℝ)) (t : ℝ) (htt : t ∈ Icc 0 T) : d z t ∈ range e := by
    induction z using QuotientAddGroup.induction_on with
    | H x => exact himage t htt x
  have hce (z : AddCircle (1 : ℝ)) (t : ℝ) (htt : t ∈ Icc 0 T) : e (c z t) = d z t := by
    obtain ⟨p, hp⟩ := hrange z t htt
    change e (r (d z t)) = d z t
    rw [← hp, hleft]
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  have hd (t : ℝ) (htt : t ∈ Icc 0 T) :
      ContDiff ℝ 2 (fun x : ℝ => d.lift x t) :=
    L.contDiff.comp (hspatial.1 t htt)
  have hc (t : ℝ) (htt : t ∈ Icc 0 T) :
      ContMDiff 𝓘(ℝ, ℝ) I 2 (fun x : ℝ => c.lift x t) :=
    (hr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiff
      (hd t htt).contMDiff (fun x => hEU (hrange (x : AddCircle (1 : ℝ)) t htt))
  refine ⟨?_, hce, hc, ?_⟩
  · intro z
    induction z using QuotientAddGroup.induction_on with
    | H x => change r (d (x : AddCircle (1 : ℝ)) 0) = _; rw [hinit x, hleft]
  · intro x t htt hzero
    have hdne : deriv (fun y => d.lift y t) x ≠ 0 := by
      have hpos := (hjet t htt x).2.2
      let B := Tensor.Coordinates.chartGramBilin (Geometry.Riemannian.retractionMetric (g t) he hr) β
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β).symm (d.lift x t))
      change 0 < B (deriv (fun y => d.lift y t) x) (deriv (fun y => d.lift y t) x) at hpos
      intro h
      rw [h, map_zero] at hpos
      exact lt_irrefl _ hpos
    have hcomp := mfderiv_comp_apply x (he.mdifferentiableAt (by simp))
      ((hc t htt).mdifferentiableAt (by norm_num)) (1 : ℝ)
    have heq : (fun y : ℝ => e (c.lift y t)) = fun y => d.lift y t :=
      funext (fun y => hce (y : AddCircle (1 : ℝ)) t htt)
    change e ∘ (fun y : ℝ => c.lift y t) = (fun y => d.lift y t) at heq
    rw [heq, mfderiv_eq_fderiv] at hcomp
    change deriv (fun y => d.lift y t) x =
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e (c.lift x t) (c.X (I := I) x t) at hcomp
    rw [hzero, map_zero] at hcomp
    exact hdne hcomp

private theorem ambient_contDiffOn_one_of_parameterDerivative_lift
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    ContDiffOn ℝ 1 (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ)) := by
  intro g₀ f₀ P S F
  have hchart := ambient_chart_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  have hspatial := ambient_spatial_contDiff_two_of_parameterDerivative_forcing_lift
    g₀ hT f₀ gforce hlift
  rw [← hfacts.1] at hspatial
  rcases hfacts with ⟨_, _, _, _, _, _, _, w, hw, hwu, _, _, hw₀, _, _, _⟩
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀
    (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ))
  change (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t)) ∧
    ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f p.1)) p.2) (Icc 0 T ×ˢ univ) at hspatial
  have hd (q : ℝ → (Fin n → ℝ)) (hq : Differentiable ℝ q) :
      deriv (fun y => L (q y)) = fun y => L (deriv q y) := by
    funext y
    exact (L.hasFDerivAt.comp_hasDerivAt y (hq y).hasDerivAt).deriv
  have hFd (t : ℝ) (htt : t ∈ Icc 0 T) :
      deriv (F t) = fun y => L (deriv (f t) y) :=
    hd (f t) ((hspatial.1 t htt).differentiable (by norm_num))
  have hFdd (t : ℝ) (htt : t ∈ Icc 0 T) :
      deriv (deriv (F t)) = fun y => L (deriv (deriv (f t)) y) := by
    rw [hFd t htt]
    exact hd (deriv (f t)) (show Differentiable ℝ (deriv (f t)) from
      (show ContDiff ℝ 1 (deriv (f t)) from (hspatial.1 t htt).deriv').differentiable (by norm_num))
  let K := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
  have hfirst := AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
    g₀ 1 (fun t => P f₀ + S (u.toFun t)) (fun t => K f₀ + w t)
    (continuousOn_const.add hw) (fun t htt => by
      apply PiLp.ext
      intro i
      simp only [ContinuousLinearMap.piLpMap_apply, PiLp.add_apply, map_add]
      change _ = (P f₀) i + (S (u.toFun t)) i
      apply congrArg₂ (· + ·)
      · exact (tensorHsInclusion_trans_apply
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) (f₀ i)).symm
      · have hi := congrArg (fun z => z i) (hwu t htt)
        have hi' := congrArg (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))) hi
        simpa only [S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
          ← tensorHsInclusion_trans_apply] using hi')
  have hC0 : ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ)) := by
    apply L.continuous.comp_continuousOn
    have hstate : ContinuousOn (fun t => P f₀ + S (u.toFun t)) (Icc 0 T) :=
      continuousOn_const.add (S.continuous.comp_continuousOn u.continuousOn_toFun)
    exact (((scalarH1PiToContinuous g₀).continuous.comp_continuousOn hstate).comp
      continuousOn_fst (fun _ hp => hp.1)).eval
        ((AddCircle.continuous_mk' 1).comp continuous_snd).continuousOn
  have hDx : ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2)
      (Icc 0 T ×ˢ (univ : Set ℝ)) := by
    have hh : ContinuousOn (fun p : ℝ × ℝ => deriv (f p.1) p.2)
        (Icc 0 T ×ˢ (univ : Set ℝ)) := by
      simpa only [f, iteratedDeriv_succ, iteratedDeriv_zero] using hfirst.2
    apply (L.continuous.comp_continuousOn hh).congr
    intro p hp
    exact congrFun (hFd p.1 hp.1) p.2
  have hDxx : ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (F p.1)) p.2)
      (Icc 0 T ×ˢ (univ : Set ℝ)) := by
    apply (L.continuous.comp_continuousOn (hspatial.2.mono
      (fun p hp => ⟨hp.1, mem_univ _⟩))).congr
    intro p hp
    exact congrFun (hFdd p.1 hp.1) p.2
  apply contDiffOn_one_of_parametric_chart_equation hG β (hab := hT) (hV := isOpen_univ)
    hC0 (fun t htt => (L.contDiff.comp (hspatial.1 t htt)).differentiable (by norm_num) |>.differentiableOn) hDx hDxx
  · intro t ht x hx
    exact hjet t ht x
  · intro t ht x hx
    exact hchart t ht x

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
private theorem contMDiffOn_retraction_of_contDiffOn
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (d : CurveMap (EuclideanSpace ℝ (Fin n))) (J : Set ℝ)
    (hd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => d.lift p.2 p.1) (J ×ˢ univ))
    (hmap : ∀ x t, t ∈ J → d.lift x t ∈ (U : Set (EuclideanSpace ℝ (Fin n)))) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun p : ℝ × ℝ => r (d.lift p.1 p.2)) (univ ×ˢ J) := by
  have hswap : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (p.2, p.1)) (univ ×ˢ J) :=
    contDiffOn_snd.prodMk contDiffOn_fst
  have hd' : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => d.lift p.1 p.2) (univ ×ˢ J) :=
    hd.comp hswap (fun _ hp => ⟨hp.2, hp.1⟩)
  exact (hr.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp hd'.contMDiffOn
    (fun p hp => hmap p.1 p.2 hp.2)

private theorem ambient_retraction_contMDiffOn_one_of_parameterDerivative_lift
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
    let c : CurveMap M := fun z t => r (d z t)
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun p : ℝ × ℝ => c.lift p.1 p.2)
      (univ ×ˢ Icc 0 T) := by
  intro g₀ f₀ P S d c
  have hjoint : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => d.lift p.2 p.1)
      (Icc 0 T ×ˢ univ) :=
    ambient_contDiffOn_one_of_parameterDerivative_lift
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hjet : ∀ t ∈ Icc 0 T, ∀ x : ℝ,
      (t, d.lift x t, deriv (fun y => d.lift y t) x) ∈
        curveShorteningChartFirstJetDomain D
          (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β :=
    ambient_firstJet_mem_of_sobolev_solution_facts
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  apply contMDiffOn_retraction_of_contDiffOn (U := U) (r := r) hr d (Icc 0 T) hjoint
  intro x t htt
  simpa only [DifferentialGeometry.extChartAt_opens_target, U.isOpen.interior_eq] using
    (hjet t htt x).2.1

private theorem ambient_sobolev_solution_exists_with_retraction_regular [I.Boundaryless] :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ScalarVectorTimeCoefficients.radius C ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift g₀ hT gforce ∧
            ambientSobolevFourthOrderLift g₀ hT gforce ∧
            let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
              (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
            let c : CurveMap M := fun z t => r (d z t)
            (∀ z, c z 0 = c₀.map z) ∧
              (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
              ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun p : ℝ × ℝ => c.lift p.1 p.2)
                (univ ×ˢ Icc 0 T) ∧
              (∀ t ∈ Icc 0 T, ContMDiff 𝓘(ℝ, ℝ) I 2 (fun x : ℝ => c.lift x t)) ∧
              c.ImmersedOn (I := I) (Icc 0 T) ∧
              ∀ x t, t ∈ Icc 0 T →
                mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e (c.lift x t)
                  (c.velocity (I := I) (Icc 0 T) x t) =
                    d.velocity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Icc 0 T) x t := by
  intro C g₀ f₀ P S
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hfour, _⟩ :=
    ambient_sobolev_solution_exists_with_mem_range c₀ g ht he hr hEU hleft β hG
  obtain ⟨hinit, hce, hc2, himm⟩ :=
    ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hc1 := ambient_retraction_contMDiffOn_one_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce,
    hfacts, hlift, hfour, hinit, hce, hc1, hc2, himm, ?_⟩
  let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
    (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
  let c : CurveMap M := fun z t => r (d z t)
  change ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun p : ℝ × ℝ => c.lift p.1 p.2)
    (univ ×ˢ Icc 0 T) at hc1
  change ∀ z t, t ∈ Icc 0 T → e (c z t) = d z t at hce
  intro x t htt
  have hslice : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) 1
      (fun τ : ℝ => (x, τ)) (Icc 0 T) :=
    (show ContDiffOn ℝ 1 (fun τ : ℝ => (x, τ)) (Icc 0 T) from
      contDiffOn_const.prodMk contDiffOn_id).contMDiffOn
  have htime : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c.lift x) (Icc 0 T) t :=
    ((hc1.comp hslice (fun τ hτ => ⟨mem_univ x, hτ⟩)) t htt).mdifferentiableWithinAt (by norm_num)
  have hvel := CurveMap.velocity_comp he htime (uniqueDiffOn_Icc hT t htt)
  have heq : CurveMap.velocity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun z τ => e (c z τ)) (Icc 0 T) x t =
        d.velocity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Icc 0 T) x t := by
    unfold CurveMap.velocity
    have h := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (f₁ := fun τ => e (c.lift x τ)) (f := d.lift x)
      (fun τ hτ => hce (x : AddCircle (1 : ℝ)) τ hτ) htt
    exact congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) h
  exact hvel.symm.trans heq

private theorem ambient_retraction_parametric_equation_of_parameterDerivative_lift [I.Boundaryless]
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
    let c : CurveMap M := fun z t => r (d z t)
    ∀ x t, t ∈ Icc 0 T → c.velocity (I := I) (Icc 0 T) x t =
      c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  intro g₀ f₀ P S d c
  have hcjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1
      (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ Icc 0 T) :=
    ambient_retraction_contMDiffOn_one_of_parameterDerivative_lift
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hfinite := ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hce : ∀ z t, t ∈ Icc 0 T → e (c z t) = d z t := hfinite.2.1
  have hcspace : ∀ t ∈ Icc 0 T, ContMDiff 𝓘(ℝ, ℝ) I 2 (fun x => c.lift x t) :=
    hfinite.2.2.1
  have hpde : ∀ t ∈ Icc 0 T, ∀ x,
      HasDerivWithinAt (fun s => d.lift x s)
        (curveShorteningParametricChartRhs
          (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
          (t, d.lift x t, deriv (fun y => d.lift y t) x,
            deriv (deriv (fun y => d.lift y t)) x)) (Icc 0 T) t :=
    ambient_chart_equation_of_parameterDerivative_lift
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  let j : M → U := fun p => ⟨e p, hEU (mem_range_self p)⟩
  have hj : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ j :=
    (ContMDiff.subtypeVal_comp_iff U j).mp he
  have hmetric : ∀ t p v w,
      (Geometry.Riemannian.retractionMetric (g t) he hr).inner (j p)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) j p v)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) j p w) = (g t).inner p v w := by
    intro t p v w
    rw [← mfderiv_subtypeVal_comp j p]
    exact Geometry.Riemannian.retractionMetric_inner_map (g t) he hr hEU hleft p v w
  intro x t htt
  have htime : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c.lift x) (Icc 0 T) t := by
    have hslice : ContMDiffWithinAt 𝓘(ℝ, ℝ) I 1 (c.lift x) (Icc 0 T) t :=
      (hcjoint (x, t) ⟨mem_univ _, htt⟩).comp t
        ((contDiffWithinAt_const.prodMk contDiffWithinAt_id).contMDiffWithinAt)
        (fun s hs => ⟨mem_univ x, hs⟩)
    exact hslice.mdifferentiableWithinAt one_ne_zero
  apply CurveMap.velocity_eq_parametric_acceleration_of_comp_of_contMDiffAt hj hmetric
    (fun s => Geometry.Riemannian.hasVanishingSecondFundamentalFormAlongCurves_retractionMetric
      (g s) he hr hEU hleft) htime (hcspace t htt x) (uniqueDiffOn_Icc hT t htt)
  apply CurveMap.velocity_eq_parametric_acceleration_of_chart_of_contMDiffAt β x t
    ((hj.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t htime)
    ((hj.contMDiffAt.of_le (by decide : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp x (hcspace t htt x))
    (uniqueDiffOn_Icc hT t htt)
    (by rw [DifferentialGeometry.extChartAt_opens_source]; trivial)
  have hspace : (fun y => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β
      (j (c.lift y t))) = (fun y => d.lift y t) := by
    funext y
    exact hce (y : AddCircle (1 : ℝ)) t htt
  change HasDerivWithinAt (fun s => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β
    (j (c.lift x s)))
    (curveShorteningParametricChartRhs
      (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
      (t, extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β (j (c.lift x t)),
        deriv (fun y => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β (j (c.lift y t))) x,
        deriv (deriv (fun y => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β
          (j (c.lift y t)))) x)) (Icc 0 T) t
  rw [hspace, show extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β (j (c.lift x t)) =
    d.lift x t from congrFun hspace x]
  apply (hpde t htt x).congr
  · intro s hs
    exact hce (x : AddCircle (1 : ℝ)) s hs
  · exact hce (x : AddCircle (1 : ℝ)) t htt

private theorem ambient_sobolev_solution_exists_with_parametric_equation [I.Boundaryless] :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ScalarVectorTimeCoefficients.radius C ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift g₀ hT gforce ∧
            ambientSobolevFourthOrderLift g₀ hT gforce ∧
            let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
              (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
            let c : CurveMap M := fun z t => r (d z t)
            (∀ z, c z 0 = c₀.map z) ∧
              (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
              ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun p : ℝ × ℝ => c.lift p.1 p.2)
                (univ ×ˢ Icc 0 T) ∧
              (∀ t ∈ Icc 0 T, ContMDiff 𝓘(ℝ, ℝ) I 2 (fun x : ℝ => c.lift x t)) ∧
              c.ImmersedOn (I := I) (Icc 0 T) ∧
              (∀ x t, t ∈ Icc 0 T →
                mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e (c.lift x t)
                  (c.velocity (I := I) (Icc 0 T) x t) =
                    d.velocity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Icc 0 T) x t) ∧
              ∀ x t, t ∈ Icc 0 T → c.velocity (I := I) (Icc 0 T) x t =
                c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  intro C g₀ f₀ P S
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce,
    hfacts, hlift, hfour, hinit, hce, hc1, hc2, himm, hvel⟩ :=
    ambient_sobolev_solution_exists_with_retraction_regular c₀ g ht he hr hEU hleft β hG
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce,
    hfacts, hlift, hfour, hinit, hce, hc1, hc2, himm, hvel, ?_⟩
  exact ambient_retraction_parametric_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem curveMap_smoothOn_retraction_of_contDiffOn
    {d : CurveMap (EuclideanSpace ℝ (Fin n))} {J : Set ℝ}
    {r : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.2 p.1) (J ×ˢ univ))
    (hU : ∀ x t, t ∈ J → d.lift x t ∈ U) :
    CurveMap.SmoothOn (I := I) (fun z t => r (d z t)) J := by
  have hswap : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.2, p.1))
      (univ ×ˢ J) := contDiffOn_snd.prodMk contDiffOn_fst
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.2, p.1))
      (univ ×ˢ J) (J ×ˢ univ) := fun _ hp => ⟨hp.2, hp.1⟩
  have hdsmooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.1 p.2)
      (univ ×ˢ J) := hd.comp hswap hmap
  exact hr.comp hdsmooth.contMDiffOn (fun p hp => hU p.1 p.2 hp.2)

private theorem ambient_retraction_smooth_of_contDiffOn
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hsmooth :
      let g₀ := c₀.pullbackMetric (g 0)
      let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
      let P := circleHsPiInclusion g₀ (Fin n)
        (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
      let S := circleHsPiInclusion g₀ (Fin n)
        (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
      let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
        (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
      ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ))) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
    let c : CurveMap M := fun z t => r (d z t)
    c.SmoothOn (I := I) (Icc 0 T) := by
  intro g₀ f₀ P S d c
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.2 p.1)
    (Icc 0 T ×ˢ univ) at hsmooth
  apply curveMap_smoothOn_retraction_of_contDiffOn (d := d) (J := Icc 0 T) hr hsmooth
  intro x t ht
  simpa only [d, g₀, f₀, P, S, CurveMap.lift,
    DifferentialGeometry.extChartAt_opens_target, U.isOpen.interior_eq] using
    (hjet t ht x).2.1

private theorem ambient_retraction_exists_reparametrization_of_contDiffOn [I.Boundaryless]
    (hg : MetricFamilySmoothOn D g)
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce)
    (hsmooth :
      let g₀ := c₀.pullbackMetric (g 0)
      let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
      let P := circleHsPiInclusion g₀ (Fin n)
        (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
      let S := circleHsPiInclusion g₀ (Fin n)
        (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
      let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
        (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
      ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ))) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
    let c : CurveMap M := fun z t => r (d z t)
    (∀ z, c z 0 = c₀.map z) ∧
      (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
      c.SmoothOn (I := I) (Icc 0 T) ∧
      c.ImmersedOn (I := I) (Icc 0 T) ∧
      ∃ φ : CircleReparametrization (Icc 0 T),
        (∀ z, φ.map 0 z = z) ∧
        CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) g (Icc 0 T) ∧
        (∀ z, c (φ.map 0 z) 0 = c₀.map z) ∧
        (∀ z t, t ∈ Icc 0 T → e (c (φ.map t z) t) = d (φ.map t z) t) ∧
        ∀ t, t ∈ Icc 0 T →
          range (fun z => e (c (φ.map t z) t)) = range (fun z => d z t) := by
  intro g₀ f₀ P S d c
  have hfinite := ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hparametric := ambient_retraction_parametric_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hcsmooth : c.SmoothOn (I := I) (Icc 0 T) :=
    ambient_retraction_smooth_of_contDiffOn
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hsmooth
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  have hJD : Icc (0 : ℝ) T ⊆ D.regular := fun t htt => (hjet t htt 0).1
  have hgeo := CurveMap.isGeometricSolutionOn_of_parabolicGauge
    hg (uniqueDiffOn_Icc hT) hJD hcsmooth hfinite.2.2.2 hparametric
  obtain ⟨φ, hφ, hsol⟩ := hgeo.exists_reparametrization_isSolutionOn hg hT hJD
  refine ⟨hfinite.1, hfinite.2.1, hcsmooth, hfinite.2.2.2, φ, hφ, hsol, ?_, ?_, ?_⟩
  · intro z
    rw [hφ]
    exact hfinite.1 z
  · intro z t ht
    exact hfinite.2.1 (φ.map t z) t ht
  · intro t ht
    have hpoint : (fun z => e (c (φ.map t z) t)) =
        (fun z => d z t) ∘ (φ.map t) := by
      funext z
      exact hfinite.2.1 (φ.map t z) t ht
    rw [hpoint]
    exact (φ.map t).surjective.range_comp (fun z => d z t)

end

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

open private exists_pos_contraction_radius from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleContractionRadius

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_pos_parameterPrincipal_norm_le {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ), ‖a - q‖ ≤ ε →
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ a‖ ≤ (1 / 4 : ℝ) ∧
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ a‖ ≤ (1 / 4 : ℝ) := by
  intro q
  let m := scalarHsMul g₀ 1 (by norm_num)
  let c := (scalarH1ToContinuous g₀).comp (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Z := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let M := scalarH0ContinuousMul g₀
  let Ch := ‖m‖ * ‖AddCircle.parameterSecondDerivativeHs g₀ 1‖
  let Cl := ‖M‖ * ‖c‖ * ‖Z.comp (AddCircle.parameterSecondDerivativeHs g₀ 0)‖
  have hCh : 0 ≤ Ch := by positivity
  have hCl : 0 ≤ Cl := by positivity
  let ε := (1 / 4 : ℝ) / (Ch + Cl + 1)
  have hε : 0 < ε := by positivity
  have hεeq : ε * (Ch + Cl + 1) = 1 / 4 := by
    exact div_mul_cancel₀ _ (by positivity)
  have hChε : Ch * ε ≤ 1 / 4 := by
    nlinarith [mul_nonneg hCl hε.le]
  have hClε : Cl * ε ≤ 1 / 4 := by
    nlinarith [mul_nonneg hCh hε.le]
  refine ⟨ε, hε, ?_⟩
  intro a ht
  constructor
  · calc
      _ ≤ ‖m‖ * ‖a - q‖ * ‖AddCircle.parameterSecondDerivativeHs g₀ 1‖ :=
        AddCircle.norm_parameterPrincipalOperatorHsPi_le g₀ a
      _ ≤ ‖m‖ * ε * ‖AddCircle.parameterSecondDerivativeHs g₀ 1‖ := by gcongr
      _ = Ch * ε := by dsimp only [Ch]; ring
      _ ≤ 1 / 4 := hChε
  · calc
      _ ≤ ‖M‖ * (‖c‖ * ‖a - q‖) *
          ‖Z.comp (AddCircle.parameterSecondDerivativeHs g₀ 0)‖ :=
        AddCircle.norm_parameterPrincipalOperatorH0Pi_le g₀ a
      _ ≤ ‖M‖ * (‖c‖ * ε) * ‖Z.comp (AddCircle.parameterSecondDerivativeHs g₀ 0)‖ := by gcongr
      _ = Cl * ε := by dsimp only [Cl]; ring
      _ ≤ 1 / 4 := hClε

private theorem exists_pos_parameterDrift_norm_lt {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (A : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
      0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      Real.sqrt (1 + T) * (eLpNorm
        (fun t => AddCircle.parameterDriftOperatorHsPi (ι := Fin n) g₀ (a₂ t))
        2 (timeMeasure T)).toReal < 1 / 4 ∧
      Real.sqrt (1 + T) * (eLpNorm
        (fun t => AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t))
        2 (timeMeasure T)).toReal < 1 / 4 := by
  let D := AddCircle.parameterDerivativeHs g₀ 1
  let m := scalarHsMul g₀ 1 (by norm_num)
  let d := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
    (scalarCc g₀ (AddCircle.laplacianDriftCoefficient g₀))
  let c := (scalarH1ToContinuous g₀).comp (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Z := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let D₀ := Z.comp (AddCircle.parameterDerivativeHs g₀ 0)
  let M := scalarH0ContinuousMul g₀
  let Kh := ‖m‖ * ‖D‖ ^ 2
  let Kl := ‖M‖ * ‖c‖ * ‖D‖ * ‖D₀‖
  let Bh := ‖m‖ * ‖d‖ * ‖D‖
  let Bl := ‖M‖ * ‖c‖ * ‖d‖ * ‖D₀‖
  let K := max Kh Kl
  let B := max Bh Bl
  have hKh : 0 ≤ Kh := by positivity
  have hKl : 0 ≤ Kl := by positivity
  have hBh : 0 ≤ Bh := by positivity
  have hBl : 0 ≤ Bl := by positivity
  obtain ⟨δ, hδ, hδR, hδ1, hsmall⟩ := exists_pos_contraction_radius
    0 (4 * K * A) (4 * B) le_rfl (by positivity) (by positivity) hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hnorm
  have hρ : 0 ≤ ρ := hT.le.trans hTρ
  have hcommon : Real.sqrt (1 + T) *
      (K * A * (Real.sqrt T + (1 + T) * ρ / 4) + Real.sqrt T * B) < 1 / 4 := by
    have hs := hsmall hT.le hTρ hρδ
    simp only [zero_mul, zero_add] at hs
    nlinarith
  let hh := AddCircle.memLp_parameterDriftOperatorHsPi (ι := Fin n) g₀ (Lp.memLp a₂)
  let hl := AddCircle.memLp_parameterDriftOperatorH0Pi (ι := Fin n) g₀ (Lp.memLp a₂)
  have hnh : ‖hh.toLp (fun t => AddCircle.parameterDriftOperatorHsPi (ι := Fin n) g₀ (a₂ t))‖ ≤
      K * A * (Real.sqrt T + (1 + T) * ρ / 4) + Real.sqrt T * B := by
    calc
      _ ≤ Kh * ‖a₂‖ + Real.sqrt T * Bh := AddCircle.norm_toLp_parameterDriftOperatorHsPi_le g₀ a₂
      _ ≤ Kh * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * Bh :=
        add_le_add (mul_le_mul_of_nonneg_left hnorm hKh) le_rfl
      _ ≤ K * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * B :=
        add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg T))
      _ = _ := by ring
  have hnl : ‖hl.toLp (fun t => AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t))‖ ≤
      K * A * (Real.sqrt T + (1 + T) * ρ / 4) + Real.sqrt T * B := by
    calc
      _ ≤ Kl * ‖a₂‖ + Real.sqrt T * Bl := AddCircle.norm_toLp_parameterDriftOperatorH0Pi_le g₀ a₂
      _ ≤ Kl * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * Bl :=
        add_le_add (mul_le_mul_of_nonneg_left hnorm hKl) le_rfl
      _ ≤ K * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * B :=
        add_le_add
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg T))
      _ = _ := by ring
  have hhbound := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hnh (Real.sqrt_nonneg (1 + T))) hcommon
  have hlbound := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hnl (Real.sqrt_nonneg (1 + T))) hcommon
  exact ⟨by simpa only [Lp.norm_toLp] using hhbound,
    by simpa only [Lp.norm_toLp] using hlbound⟩

private theorem exists_pos_parameterDerivative_contraction_margin {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ ε : ℝ, 0 < ε ∧ ∀ A : ℝ≥0, ∀ R : ℝ, 0 < R →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
        0 < T → T ≤ ρ → ρ ≤ δ →
        ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
        (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ ε) →
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
        parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ (3 / 4) := by
  intro H q
  obtain ⟨ε, hε, hp⟩ := exists_pos_parameterPrincipal_norm_le (n := n) g₀
  refine ⟨ε, hε, ?_⟩
  intro A R hR
  obtain ⟨δ, hδ, hδR, hδ1, hd⟩ := exists_pos_parameterDrift_norm_lt (n := n) g₀ A hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  have hT1 : T ≤ 1 := hTρ.trans (hρδ.trans hδ1)
  obtain ⟨hdh, hdl⟩ := hd hT hTρ hρδ a₂ hnorm
  have hph : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (H (a₂ t))‖ ≤ (1 / 4 : ℝ) := by
    filter_upwards [hclose] with t ht
    exact (hp _ ht).1
  have hpl : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (H (a₂ t))‖ ≤ (1 / 4 : ℝ) := by
    filter_upwards [hclose] with t ht
    exact (hp _ ht).2
  have hquarter : (1 / 4 : ℝ) * (1 + T) ≤ 1 / 2 := by
    calc
      (1 / 4 : ℝ) * (1 + T) ≤ (1 / 4 : ℝ) * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hT1) (by norm_num)
      _ = 1 / 2 := by norm_num
  have hmargin : (1 / 4 : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal ≤ 3 / 4 := by
    exact (add_lt_add_of_le_of_lt hquarter hdh).le.trans_eq (by norm_num)
  have hsmalll : (1 / 4 : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      ‖(AddCircle.memLp_parameterDriftOperatorH0Pi (ι := Fin n) g₀ (Lp.memLp a₂)).toLp
        (fun t => AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t))‖ < 1 := by
    rw [Lp.norm_toLp]
    exact (add_lt_add_of_le_of_lt hquarter hdl).trans (by norm_num)
  obtain ⟨hpl', hsmalll'⟩ := parameterDerivativeH0Pi_normalized_contraction g₀ a₂
    (1 / 4) hpl hsmalll
  exact ⟨1 / 4, 1 / 4, hph, hpl', hmargin, hsmalll'⟩

private theorem exists_pos_parameterDerivative_contraction_threshold {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ ε : ℝ, 0 < ε ∧ ∀ A : ℝ≥0, ∀ R : ℝ, 0 < R →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
        0 < T → T ≤ ρ → ρ ≤ δ →
        ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
        (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ ε) →
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
        parameterDerivativeOperatorBounds (n := n) g₀ a₂ := by
  intro H q
  obtain ⟨ε, hε, hcontract⟩ := exists_pos_parameterDerivative_contraction_margin (n := n) g₀
  refine ⟨ε, hε, ?_⟩
  intro A R hR
  obtain ⟨δ, hδ, hδR, hδ1, hmargin⟩ := hcontract A R hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  exact parameterDerivativeOperatorBounds_of_margin g₀ a₂ (by norm_num : (3 / 4 : ℝ) < 1)
    (hmargin hT hTρ hρδ a₂ hclose hnorm)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_normalized_timeL2_h2_coefficients
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 2) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) 2) T) :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)
    let P₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H₂)
    ∃ aa : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
    ∃ bb : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
      (fun t => H (aa t)) =ᵐ[timeMeasure T] (fun t => H₂ (a₂ t)) ∧
      (fun t => P (bb t)) =ᵐ[timeMeasure T] (fun t => P₂ (b₂ t)) ∧
      ‖aa‖ ≤ ‖a₂‖ ∧ ‖bb‖ ≤ ‖b₂‖ := by
  intro H P H₂ P₂
  let S := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ 2)
  let SP := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => S)
  let aa := S.compLpL 2 (timeMeasure T) a₂
  let bb := SP.compLpL 2 (timeMeasure T) b₂
  have hS : ‖S‖ ≤ 1 := tensorHsInclusion_opNorm_le_one _
  have hSP : ‖SP‖ ≤ 1 := ContinuousLinearMap.norm_piLpMap_le _ zero_le_one (fun _ => hS)
  refine ⟨aa, bb, ?_, ?_, ?_, ?_⟩
  · filter_upwards [S.coeFn_compLpL a₂] with t ht
    change H (aa t) = _
    rw [ht]
    exact (tensorHsInclusion_trans_apply _ _ _).symm
  · filter_upwards [SP.coeFn_compLpL b₂] with t ht
    change P (bb t) = _
    rw [ht]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ 2) (b₂ t i)).symm
  · exact (S.norm_compLp_le a₂).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hS (norm_nonneg a₂))
  · exact (SP.norm_compLp_le b₂).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hSP (norm_nonneg b₂))

private theorem ambient_coefficients_h2_norm_le_of_translated_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ δ ≤ 1 ∧
      ∃ A B : ℝ≥0, ∀ f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2),
      ‖f - f₀‖ ≤ δ / 2 → ∀ {ρ T : ℝ} (hT : 0 < T), T ≤ ρ → ρ ≤ δ / 2 →
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) → w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) → ‖gforce‖ ≤ ρ / 4 →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (f - f₀) + w t)))) ∧
        (fun t => P (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (f - f₀) + w t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) ∧
        ‖b₂‖ ≤ B * (Real.sqrt T + (1 + T) * ρ / 4) := by
  intro C g₀ f₀ J K H P
  obtain ⟨δ, hδ, hδC, hδ1, A, B, hA, hB, hab⟩ :=
    ambient_coefficients_h2_norm_le_of_small_state c₀ g ht he hr hEU hleft β hG
  let D := 1 + δ / 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨δ, hδ, hδC, hδ1, ⟨A * D, mul_nonneg hA hD⟩, ⟨B * D, mul_nonneg hB hD⟩, ?_⟩
  intro f hf ρ T hT hTρ hρδ gforce field w hw hwu hbound hforce
  let field' := TimeSobolev.const T (f - f₀) + field
  let w' := fun t => K (f - f₀) + w t
  have hKnorm : ‖K‖ ≤ 1 := ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
    (fun _ => tensorHsInclusion_opNorm_le_one _)
  have hKf : ‖K (f - f₀)‖ ≤ δ / 2 := (K.le_opNorm _).trans
    ((show ‖K‖ * ‖f - f₀‖ ≤ ‖f - f₀‖ from by simpa only [one_mul] using mul_le_mul_of_nonneg_right hKnorm (norm_nonneg (f - f₀))).trans hf)
  have hw' : ContinuousOn w' (Icc 0 T) := continuousOn_const.add hw
  have hwu' : w' =ᵐ[timeMeasure T] fun t => K (field' t) := by
    filter_upwards [hwu, TimeSobolev.coeFn_const (T := T) (f - f₀),
      Lp.coeFn_add (TimeSobolev.const T (f - f₀)) field] with t ht hc hsum
    change K (f - f₀) + w t = K ((TimeSobolev.const T (f - f₀) + field) t)
    rw [hsum, Pi.add_apply, hc, map_add, ht]
  have hb' (t : ℝ) (ht : t ∈ Icc 0 T) : ‖w' t‖ ≤ δ := by
    exact (norm_add_le _ _).trans (by linarith [hbound t ht])
  obtain ⟨a₂, b₂, ha₂, hb₂, hanorm, hbnorm⟩ :=
    hab T (by linarith) field' w' hw' hwu' hb'
  obtain ⟨aa, bb, haa, hbb, haanorm, hbbnorm⟩ :=
    exists_normalized_timeL2_h2_coefficients g₀ a₂ b₂
  have hfield : ‖field‖ ≤ (1 + T) * ρ / 4 :=
    (norm_maximalRegularityDuhamelVectorField_zero_le hT gforce).trans
      (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hforce (by linarith : 0 ≤ 1 + T))
  have hfield' : ‖field'‖ ≤ Real.sqrt T * (δ / 2) + (1 + T) * ρ / 4 := by
    calc
      ‖field'‖ ≤ ‖TimeSobolev.const T (f - f₀)‖ + ‖field‖ := norm_add_le _ _
      _ = Real.sqrt T * ‖f - f₀‖ + ‖field‖ := by rw [TimeSobolev.norm_const]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hf (Real.sqrt_nonneg T)) hfield
  have htotal : Real.sqrt T + ‖field'‖ ≤ D * (Real.sqrt T + (1 + T) * ρ / 4) := by
    dsimp only [D]
    have hpos : 0 ≤ (1 + T) * ρ / 4 := by have : 0 ≤ ρ := hT.le.trans hTρ; positivity
    nlinarith [mul_nonneg (by positivity : 0 ≤ δ / 2) hpos]
  refine ⟨aa, bb, haa.trans ha₂, hbb.trans hb₂,
    haanorm.trans (hanorm.trans ?_), hbbnorm.trans (hbnorm.trans ?_)⟩
  · change A * (Real.sqrt T + ‖field'‖) ≤ (A * D) * (Real.sqrt T + (1 + T) * ρ / 4)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left htotal hA
  · change B * (Real.sqrt T + ‖field'‖) ≤ (B * D) * (Real.sqrt T + (1 + T) * ρ / 4)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left htotal hB

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

open private vectorTensorHsNormedSpace from DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients

noncomputable section
attribute [local instance] vectorTensorHsNormedSpace
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩


private theorem exists_pos_parameterDerivative_translated_margin_radius
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (A Cα : ℝ≥0) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (Jn : ℝ) (hJn : 0 ≤ Jn) :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (DifferentialGeometry.Analysis.Sobolev.scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R / 2 ∧ δ ≤ 1 ∧ 2 * Jn * δ ≤ r ∧
      ∀ {ρ T : ℝ}, 0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ (Cα : ℝ) * (2 * δ)) →
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ (3 / 4) := by
  intro H q
  obtain ⟨ε, hε, hεcontract⟩ := exists_pos_parameterDerivative_contraction_margin (n := n) g₀
  let r₀ := min (R / 2) (min (r / (2 * (1 + Jn))) (ε / (2 * (1 + (Cα : ℝ)))))
  have hr₀ : 0 < r₀ := by dsimp only [r₀]; positivity
  have hrR : r₀ ≤ R / 2 := min_le_left _ _
  have hrJ : 2 * Jn * r₀ ≤ r := by
    have hp : r₀ ≤ r / (2 * (1 + Jn)) := (min_le_right _ _).trans (min_le_left _ _)
    have he := (le_div_iff₀ (by positivity : 0 < 2 * (1 + Jn))).mp hp
    nlinarith
  have hrα : (Cα : ℝ) * (2 * r₀) ≤ ε := by
    have hp : r₀ ≤ ε / (2 * (1 + (Cα : ℝ))) := (min_le_right _ _).trans (min_le_right _ _)
    have he := (le_div_iff₀ (by positivity : 0 < 2 * (1 + (Cα : ℝ)))).mp hp
    nlinarith [Cα.coe_nonneg]
  obtain ⟨δ, hδ, hδr, hδ1, hcontract⟩ := hεcontract A r₀ hr₀
  refine ⟨δ, hδ, hδr.trans hrR, hδ1, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hδr (by positivity)).trans hrJ
  · intro ρ T hT hTρ hρδ a₂ hclose hnorm
    apply hcontract hT hTρ hρδ a₂ ?_ hnorm
    filter_upwards [hclose] with t ht
    exact ht.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hδr (by norm_num : (0 : ℝ) ≤ 2)) Cα.coe_nonneg).trans hrα)

private theorem translated_state_norm_bounds
    {X Y Z : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    (K : X →L[ℝ] Y) (J : Y →L[ℝ] Z) (hK : ‖K‖ ≤ 1)
    {δ R : ℝ} (hJ : 2 * ‖J‖ * δ ≤ R) (f : X) (hf : ‖f‖ ≤ δ)
    {A : Type*} (s : Set A) (w : A → Y) (hw : ∀ t ∈ s, ‖w t‖ ≤ δ) :
    (∀ t ∈ s, ‖K f + w t‖ ≤ 2 * δ) ∧ (∀ t ∈ s, ‖J (K f + w t)‖ ≤ R) := by
  have hKnorm : ‖K‖ * ‖f‖ ≤ ‖f‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (norm_nonneg f)
  have hKf : ‖K f‖ ≤ δ := (K.le_opNorm f).trans (hKnorm.trans hf)
  have hnorm (t : A) (ht : t ∈ s) : ‖K f + w t‖ ≤ 2 * δ :=
    (norm_add_le _ _).trans (by linarith only [hKf, hw t ht])
  refine ⟨hnorm, ?_⟩
  intro t ht
  exact (J.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hnorm t ht) (norm_nonneg J)).trans
    (by nlinarith only [hJ]))

private theorem ambient_translated_coefficients_h2_and_margin
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ δ ≤ 1 ∧
      ∀ f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2), ‖f - f₀‖ ≤ δ →
      ∀ {ρ T : ℝ} (hT : 0 < T), T ≤ ρ → ρ ≤ δ →
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) → w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) → ‖gforce‖ ≤ ρ / 4 →
      (∀ t ∈ Icc 0 T, ‖J (K (f - f₀) + w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) ∧
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (f - f₀) + w t)))) ∧
        (fun t => P (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (f - f₀) + w t)))) ∧
        parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ (3 / 4) := by
  intro C g₀ f₀ J K H P
  obtain ⟨δ₀, hδ₀, hδ₀C, hδ₀1, A, B, hab⟩ :=
    ambient_coefficients_h2_norm_le_of_translated_state c₀ g ht he hr hEU hleft β hG
  obtain ⟨Cα, hclose⟩ := ambient_diffusion_sub_baseline_norm_le c₀ g ht he hr hEU hleft β hG
  obtain ⟨δ, hδ, hδδ, hδ1, hδJ, hcontract⟩ :=
    exists_pos_parameterDerivative_translated_margin_radius (n := n) g₀ A Cα hδ₀
      (ScalarVectorTimeCoefficients.radius_pos C) ‖J‖ (norm_nonneg J)
  have hδC : δ ≤ ScalarVectorTimeCoefficients.radius C :=
    (hδδ.trans (by linarith only [hδ₀])).trans hδ₀C
  refine ⟨δ, hδ, hδC, hδ1, ?_⟩
  intro f hf ρ T hT hTρ hρδ gforce field w hw hwu hbound hforce
  let w' := fun t => K (f - f₀) + w t
  obtain ⟨hw', hJw⟩ := translated_state_norm_bounds K J
    (ContinuousLinearMap.norm_piLpMap_le _ zero_le_one (fun _ => tensorHsInclusion_opNorm_le_one _))
    hδJ (f - f₀) hf (Icc 0 T) w (fun t ht => (hbound t ht).trans hρδ)
  obtain ⟨a₂, b₂, ha₂, hb₂, hanorm, _⟩ :=
    hab f (hf.trans hδδ) hT hTρ (hρδ.trans hδδ) gforce w hw hwu hbound hforce
  refine ⟨hJw, a₂, b₂, ha₂, hb₂, ?_⟩
  have hδtwo : 0 ≤ 2 * δ := by positivity
  have hTtwo : T ≤ 2 * δ := by linarith only [hTρ, hρδ, hδ]
  have hclosew := hclose hδtwo hTtwo w'
  dsimp only [C, g₀, J, K, w'] at hw' hJw
  have hpoint0 := hclosew hw'
  have hpoint := hpoint0 hJw
  apply hcontract hT hTρ hρδ a₂ ?_ hanorm
  have htmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  filter_upwards [ha₂, htmem] with t hat htt
  rw [hat]
  exact hpoint t htt

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
variable (c₀ : SmoothImmersion (I := I) (M := M))
variable {e : M → EuclideanSpace ℝ (Fin n)}
variable (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambient_original_forcing_higher_equation
    (gM : SmoothRiemannianMetric I M) {m : ℕ} (hm : 2 ≤ m)
    {T : ℝ} (hT : 0 < T)
    (F₂ : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((2 : ℕ) : ℝ)) T)
    (a₂ : ℝ → TensorHs (c₀.pullbackMetric gM) 0 0 ((2 : ℕ) : ℝ))
    (b₂ : ℝ → CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((2 : ℕ) : ℝ))
    (U : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((m : ℝ) + 2)) T)
    (a : ℝ → TensorHs (c₀.pullbackMetric gM) 0 0 (m : ℝ))
    (b : ℝ → CircleHsPi (c₀.pullbackMetric gM) (Fin n) (m : ℝ))
    (ha : ContinuousOn a (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T)) :
    let g₀ := c₀.pullbackMetric gM
    let J := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (show ((2 : ℕ) : ℝ) ≤ (m : ℝ) by exact_mod_cast hm)
    let K := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (show ((2 : ℕ) : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right hm 2)
    let U₂ := maximalRegularityDuhamelVectorField hT 0 F₂
    (fun t => J (a t)) =ᵐ[timeMeasure T] a₂ →
    (∀ᵐ t ∂timeMeasure T, ∀ i, J (b t i) = b₂ t i) →
    (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => K)).compLpL
      2 (timeMeasure T) U = U₂ →
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ) (U₂ t i) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (a₂ t)
          (AddCircle.parameterSecondDerivativeHs g₀ 2
            (ambientSobolev c₀ gM e he (((2 : ℕ) : ℝ) + 2) i + U₂ t i)) + b₂ t i) →
    ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) (m : ℝ)) T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => J)).compLpL
        2 (timeMeasure T) FH = F₂ ∧
      U = maximalRegularityDuhamelVectorField hT 0 FH ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) (m : ℝ) (U t i) + FH t i =
          scalarHsMul g₀ m (by simpa using (show 1 ≤ m by omega)) (a t)
            (AddCircle.parameterSecondDerivativeHs g₀ m
              (ambientSobolev c₀ gM e he ((m : ℝ) + 2) i + U t i)) + b t i := by
  intro g₀ J K U₂ ha₂ hb₂ hU heq
  let f₀ := ambientSobolev c₀ gM e he ((m : ℝ) + 2)
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => K)
  have hUae : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, K (U t i) = U₂ t i := by
    have hP := P.coeFn_compLpL U
    rw [hU] at hP
    filter_upwards [hP] with t ht
    intro i
    exact congrArg (fun z => z i) ht.symm
  have hf₀ (i : Fin n) : K (f₀ i) = ambientSobolev c₀ gM e he (((2 : ℕ) : ℝ) + 2) i := by
    change tensorHsInclusion _ (ccTensorToHs g₀ 0 ((m : ℝ) + 2) _) = _
    rw [tensorHsInclusion_ccTensorToHs]
    rfl
  have hweak : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ) (K (U t i)) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (J (a t))
          (AddCircle.parameterSecondDerivativeHs g₀ 2 (K (f₀ i + U t i))) + J (b t i) := by
    filter_upwards [ha₂, hb₂, hUae, heq] with t hat hbt hUt het
    intro i
    rw [K.map_add, hf₀, hUt i, hat, hbt i]
    exact het i
  exact AddCircle.exists_timeL2_parabolic_forcing_lift_of_continuousOn
    g₀ (by decide : 1 ≤ 2) hm hT f₀ U F₂ a b ha hb hU hweak

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
