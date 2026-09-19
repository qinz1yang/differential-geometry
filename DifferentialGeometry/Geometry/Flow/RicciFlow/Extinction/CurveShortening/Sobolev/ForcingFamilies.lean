import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientFamilies
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcingContinuity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleLinearizedLift

open private
  CircleHsPi
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CircleHsPi
  circleHsPiInclusion
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHsPiInclusion
  circleHsPiCongr
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients

open private
  circleFirstJet
  DifferentialGeometry.Analysis.Parabolic.circleFirstJet from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState

open private
  referenceCircleSolutionFacts
  DifferentialGeometry.Analysis.Parabolic.referenceCircleSolutionFacts
  reference_solution_exists_continuousOn_representative
  DifferentialGeometry.Analysis.Parabolic.reference_solution_exists_continuousOn_representative
  reference_parameterDerivative_weakEquation_of_h2_coefficients
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.reference_parameterDerivative_weakEquation_of_h2_coefficients
  DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions

open private
  referenceCircleSymmetricCoefficientFacts
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.referenceCircleSymmetricCoefficientFacts
  referenceCirclePrincipalNormBounds
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.referenceCirclePrincipalNormBounds from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions

open private
  reference_shifted_principalCoefficient_tendsto_top
  DifferentialGeometry.Analysis.Parabolic.reference_shifted_principalCoefficient_tendsto_top
  reference_selected_initial_coefficients_tendsto_timeShift
  DifferentialGeometry.Analysis.Parabolic.reference_selected_initial_coefficients_tendsto_timeShift
  reference_shifted_high_principal_exists_tendsto_top
  DifferentialGeometry.Analysis.Parabolic.reference_shifted_high_principal_exists_tendsto_top
  reference_exists_coefficient_representatives_timeShift
  DifferentialGeometry.Analysis.Parabolic.reference_exists_coefficient_representatives_timeShift from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientFamilies

noncomputable section


open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts
    reference_parameterDerivative_weakEquation_of_h2_coefficients)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_selected_parameterDerivative_forcing_tendsto_timeShift
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (hf₄ : Tendsto f₄ l (𝓝 (f₄ x₀)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (u : X → timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hforce : Tendsto gforce l (𝓝 (gforce x₀)))
    (W : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hW₀ : ContinuousOn (W x₀) (Icc 0 T))
    (hW : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (aTop : X → Lp (TensorHs g₀ 0 0 1) ∞ (timeMeasure T))
    (FH : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (Ch Cl : X → ℝ≥0) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    (∀ x, K₄ (f₄ x) = (f x).val) →
    (∀ x, W x =ᵐ[timeMeasure T] fun t => K (V x t)) →
    (∀ x, referenceCircleSolutionFacts g₀ (f x).val
      (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z) ρ hT (u x) (gforce x)) →
    (∀ᶠ x in l, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W x t‖ ≤ ρ) →
    -ρ ≤ σ x₀ → σ x₀ + T ≤ ρ → (∀ t ∈ Icc 0 T, ‖W x₀ t‖ ≤ ρ) →
    (∀ x, (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha (f x) (σ x + t) (W x t)))) →
    (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₂ x t))
      =ᵐ[timeMeasure T] (fun t => Cpi (reaction (f x) (σ x + t) (W x t)))) →
    (∀ x, aTop x =ᵐ[timeMeasure T] fun t => alpha (f x) (σ x + t) (W x t)) →
    ∀ (hCh : ∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (AH (a₂ x t))‖ ≤ Ch x),
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (AH (a₂ x t))‖ ≤ Cl x) →
    (Ch x₀ : ℝ) < 1 → (Cl x₀ : ℝ) < 1 →
    (∀ x, parameterDerivativeDuhamelForcing g₀ 0 hT (gforce x) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Z)).compLpL
        2 (timeMeasure T) (FH x)) →
    Tendsto FH l (𝓝 (FH x₀)) := by
  intro K K₄ K₀ P J AH C Cpi Z V hcoeff hbase hWV hfacts hgood hσlo hσhi hbound₀
    ha₂ hb₂ haTop hCh hCl hChlt hCllt hLift
  have hf : Tendsto (fun x => (f x).val) l (𝓝 (f x₀).val) := by
    have h := (K₄.continuous.tendsto (f₄ x₀)).comp hf₄
    change Tendsto (fun x => K₄ (f₄ x)) l (𝓝 (K₄ (f₄ x₀))) at h
    simpa only [hbase] using h
  let SD := maximalRegularityVectorFieldL (ι := Fin n) (g := g₀) (r := 0) (s := 0)
    ((1 : ℕ) : ℝ) hT.le
  have hSD : Tendsto (fun x => SD (gforce x)) l (𝓝 (SD (gforce x₀))) :=
    (SD.continuous.tendsto (gforce x₀)).comp hforce
  have hSD_eq (z : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) :
      SD z = maximalRegularityDuhamelVectorField hT 0 z :=
    maximalRegularityVectorFieldL_eq_duhamel hT z
  have hV : Tendsto V l (𝓝 (V x₀)) := by
    simpa only [hSD_eq] using hSD
  have hpair := reference_selected_initial_coefficients_tendsto_timeShift
    g₀ T x₀ σ hσ fref f hf F G hF hG hS alpha reaction V hV W hW₀ hW a₂ b₂
    hcoeff hWV hgood hσlo hσhi hbound₀ ha₂ hb₂
  have haT : Tendsto a₂ l (𝓝 (a₂ x₀)) := (continuous_fst.tendsto _).comp hpair
  have hbT : Tendsto b₂ l (𝓝 (b₂ x₀)) := (continuous_snd.tendsto _).comp hpair
  have haTopT := reference_shifted_principalCoefficient_tendsto_top
    g₀ T P J σ (σ x₀) hσ fref f (f x₀) W (W x₀) hf hW₀ hW
    F G hF hS alpha reaction hcoeff hgood hσlo hσhi hbound₀ aTop (aTop x₀)
    haTop (haTop x₀)
  let aTopNat := fun x => C.compLpL ∞ (timeMeasure T) (aTop x)
  have haTopNat : Tendsto aTopNat l (𝓝 (aTopNat x₀)) :=
    ((C.compLpL ∞ (timeMeasure T)).continuous.tendsto (aTop x₀)).comp haTopT
  apply tendsto_parameterDerivative_forcing_lift g₀ hT x₀ gforce f₄ a₂ b₂ FH
    aTopNat Ch Cl hforce hf₄ haT hbT haTopNat
  · intro x
    have ha (x : X) : (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
        (fun t => C (alpha (f x) (σ x + t) (K (V x t)))) := by
      filter_upwards [ha₂ x, hWV x] with t hat hwt
      simpa only [hwt] using hat
    have hb (x : X) : (fun t => ContinuousLinearMap.piLpMap 2
        (fun _ : Fin n => AH) (b₂ x t)) =ᵐ[timeMeasure T]
        (fun t => Cpi (reaction (f x) (σ x + t) (K (V x t)))) := by
      filter_upwards [hb₂ x, hWV x] with t hbt hwt
      simpa only [hwt] using hbt
    have hw := reference_parameterDerivative_weakEquation_of_h2_coefficients g₀
      (f x).val (f₄ x) (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z)
      hT (u x) (gforce x) (a₂ x) (b₂ x) (hfacts x) (hbase x) (ha x) (hb x)
    exact hw
  · intro x
    filter_upwards [C.coeFn_compLpL (aTop x), haTop x, ha₂ x] with t hct hat hat₂
    change aTopNat x t = C (aTop x t) at hct
    exact hct.trans ((congrArg C hat).trans hat₂.symm)
  · exact hCh
  · exact hCl
  · exact hChlt
  · exact hCllt
  · exact hLift

end DifferentialGeometry.Analysis.Parabolic

end


noncomputable section


open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts
    reference_parameterDerivative_weakEquation_of_h2_coefficients
    referenceCirclePrincipalNormBounds)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_selected_parameterDerivative_forcing_tendsto_timeShift
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (hf₄ : Tendsto f₄ l (𝓝 (f₄ x₀)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (u : X → timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hforce : Tendsto gforce l (𝓝 (gforce x₀)))
    (W : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hW₀ : ContinuousOn (W x₀) (Icc 0 T))
    (hW : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (aTop : X → Lp (TensorHs g₀ 0 0 1) ∞ (timeMeasure T))
    :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    referenceCirclePrincipalNormBounds (n := n) g₀ ρ alpha →
    (∀ x, K₄ (f₄ x) = (f x).val) →
    (∀ x, W x =ᵐ[timeMeasure T] fun t => K (V x t)) →
    (∀ x, referenceCircleSolutionFacts g₀ (f x).val
      (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z) ρ hT (u x) (gforce x)) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W x t‖ ≤ ρ) →
    (∀ x, (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha (f x) (σ x + t) (W x t)))) →
    (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₂ x t))
      =ᵐ[timeMeasure T] (fun t => Cpi (reaction (f x) (σ x + t) (W x t)))) →
    (∀ x, aTop x =ᵐ[timeMeasure T] fun t => alpha (f x) (σ x + t) (W x t)) →
    ∃ FH : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      (∀ x, parameterDerivativeDuhamelForcing g₀ 0 hT (gforce x) =
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Z)).compLpL
          2 (timeMeasure T) (FH x)) ∧ Tendsto FH l (𝓝 (FH x₀)) := by
  classical
  intro K K₄ K₀ P J AH C Cpi Z V hcoeff hprincipal hbase hWV hfacts hgood ha₂ hb₂ haTop
  have hbounds (x : X) :
      (∀ᵐ t ∂timeMeasure T,
        ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (AH (a₂ x t))‖ ≤ (1 / 4 : ℝ)) ∧
      (∀ᵐ t ∂timeMeasure T,
        ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (AH (a₂ x t))‖ ≤ (1 / 4 : ℝ)) := by
    have hpair : ∀ᵐ t ∂timeMeasure T,
        ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (AH (a₂ x t))‖ ≤ (1 / 4 : ℝ) ∧
        ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (AH (a₂ x t))‖ ≤ (1 / 4 : ℝ) := by
      filter_upwards [ha₂ x, ae_restrict_mem measurableSet_Icc] with t hat htt
      have ht : σ x + t ∈ Icc (-ρ) ρ := by
        constructor <;> linarith [htt.1, htt.2, (hgood x).1, (hgood x).2.1]
      have hp := hprincipal (f x) (σ x + t) ht (W x t) ((hgood x).2.2 t htt)
      rw [hat]
      exact hp
    exact ⟨hpair.mono fun _ h => h.1, hpair.mono fun _ h => h.2⟩
  have hex (x : X) : ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      parameterDerivativeDuhamelForcing g₀ 0 hT (gforce x) =
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Z)).compLpL
          2 (timeMeasure T) FH := by
    apply exists_parameterDerivative_forcing_lift_of_principal_norm_lt_one
      g₀ hT (gforce x) (f₄ x) (a₂ x) (b₂ x) (1 / 4) (1 / 4)
      (by simpa [AH] using (hbounds x).1) (by simpa [AH] using (hbounds x).2)
      (by norm_num) (by norm_num)
    have ha : (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
        (fun t => C (alpha (f x) (σ x + t) (K (V x t)))) := by
      filter_upwards [ha₂ x, hWV x] with t hat hwt
      simpa only [hwt] using hat
    have hb : (fun t => ContinuousLinearMap.piLpMap 2
        (fun _ : Fin n => AH) (b₂ x t)) =ᵐ[timeMeasure T]
        (fun t => Cpi (reaction (f x) (σ x + t) (K (V x t)))) := by
      filter_upwards [hb₂ x, hWV x] with t hbt hwt
      simpa only [hwt] using hbt
    exact reference_parameterDerivative_weakEquation_of_h2_coefficients g₀
      (f x).val (f₄ x) (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z)
      hT (u x) (gforce x) (a₂ x) (b₂ x) (hfacts x) (hbase x) ha hb
  choose FH hFH using hex
  refine ⟨FH, hFH, ?_⟩
  exact reference_selected_parameterDerivative_forcing_tendsto_timeShift g₀ hT x₀ σ hσ
    fref f f₄ hf₄ F G hF hG hS alpha reaction u gforce hforce W hW₀ hW a₂ b₂ aTop
    FH (fun _ => 1 / 4) (fun _ => 1 / 4) hcoeff hbase hWV hfacts
    (Eventually.of_forall hgood) (hgood x₀).1 (hgood x₀).2.1 (hgood x₀).2.2
    ha₂ hb₂ haTop (by intro x; simpa [AH] using (hbounds x).1)
    (by intro x; simpa [AH] using (hbounds x).2) (by norm_num) (by norm_num) hFH

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open private exists_tendsto_timeL2_parabolic_forcing_lift from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcingContinuity
open private weakParameterEquation from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleLinearizedLift

attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts
    referenceCirclePrincipalNormBounds
    reference_parameterDerivative_weakEquation_of_h2_coefficients)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_initial_high_principal_tendsto_top
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (T : ℝ) (x₀ : X) (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (hf : Tendsto (fun x => (f x).val) l (𝓝 (f x₀).val))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (W₃ : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (hW₃ : ∀ x, ContinuousOn (W₃ x) (Icc 0 T))
    (hW₃lim : TendstoUniformlyOn W₃ (W₃ x₀) l (Icc 0 T))
    (W : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    (∀ x, ∀ t ∈ Icc 0 T, K (W₃ x t) = W x t) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W x t‖ ≤ ρ) →
    (∀ x, (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha (f x) (σ x + t) (W x t)))) →
    ∃ aTop₂ : X → Lp (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) ∞ (timeMeasure T),
      (∀ x, aTop₂ x =ᵐ[timeMeasure T] a₂ x) ∧ Tendsto aTop₂ l (𝓝 (aTop₂ x₀)) := by
  intro K K₀ P J AH C hcoeff hW₃low hgood ha₂
  let A1 := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  have hCA (v : TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) : C (A1 v) = AH v := by
    have h := tensorHsCongrL_incl (g := g₀) (r := 0) (s := 0)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (rfl : ((1 : ℕ) : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    simpa only [C, A1, AH, ContinuousLinearMap.comp_apply,
      tensorHsCongrL_refl, ContinuousLinearMap.id_apply] using congrArg (fun L => L v) h
  have ha₂real (x : X) : (fun t => A1 (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (W x t)) := by
    filter_upwards [ha₂ x] with t ht
    apply (tensorHsCongr g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))).injective
    change C (A1 (a₂ x t)) = C (alpha (f x) (σ x + t) (W x t))
    rw [hCA]
    exact ht
  let E := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((0 + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
  let Eback := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((0 + 1 + 1 : ℕ) : ℝ) + 1)
  let Elow := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 + 1 + 1 : ℕ) : ℝ) + 1)
  have hEback (v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) :
      Eback (E v) = v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hElow (v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) :
      Elow (E v) = K v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  let fHigh := fun x => E (f x).val
  let WHigh := fun x t => E (W₃ x t)
  have hfHigh : Tendsto fHigh l (𝓝 (fHigh x₀)) :=
    (E.continuous.tendsto (f x₀).val).comp hf
  have hWHigh (x : X) : ContinuousOn (WHigh x) (Icc 0 T) :=
    E.continuous.comp_continuousOn (hW₃ x)
  have hWHighlim : TendstoUniformlyOn WHigh (WHigh x₀) l (Icc 0 T) :=
    E.uniformContinuous.comp_tendstoUniformlyOn hW₃lim
  have hWHighlow (x : X) (t : ℝ) (ht : t ∈ Icc 0 T) : Elow (WHigh x t) = W x t := by
    exact (hElow (W₃ x t)).trans (hW₃low x t ht)
  obtain ⟨aTop₂, haTop₂, haTop₂lim⟩ := reference_shifted_high_principal_exists_tendsto_top
    g₀ 0 T x₀ σ hσ fref f fHigh WHigh hWHigh hfHigh hWHighlim
    (by norm_num : ((0 + 1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 1)
    a₂ F G hF hS alpha reaction hcoeff
    (fun x => hEback (f x).val)
    (by intro x; refine ⟨(hgood x).1, (hgood x).2.1, ?_⟩
        intro t ht
        change ‖Elow (WHigh x t)‖ ≤ ρ
        simpa only [hWHighlow x t ht] using (hgood x).2.2 t ht)
    (by intro x
        filter_upwards [ha₂real x, ae_restrict_mem measurableSet_Icc] with t hat htt
        change A1 (a₂ x t) = alpha (f x) (σ x + t) (Elow (WHigh x t))
        simpa only [hWHighlow x t htt] using hat)
  have haTop₂eq (x : X) : aTop₂ x =ᵐ[timeMeasure T] a₂ x := by
    filter_upwards [haTop₂ x] with t ht
    refine ht.trans ?_
    apply TensorHs.ext
    rfl
  exact ⟨aTop₂, haTop₂eq, haTop₂lim⟩

private theorem reference_exists_initial_duhamel_representatives
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (gforce FH : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hforce : Tendsto gforce l (𝓝 (gforce x₀)))
    (hFHlim : Tendsto FH l (𝓝 (FH x₀))) :
    let Z := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    let K₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    (∀ x, parameterDerivativeDuhamelForcing g₀ 0 hT (gforce x) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Z)).compLpL
        2 (timeMeasure T) (FH x)) →
    ∃ V₄ : X → timeL2 (CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2)) T,
    ∃ W₃ : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2),
      (∀ x, K₄.compLpL 2 (timeMeasure T) (V₄ x) = V x) ∧
      (∀ x, ContinuousOn (W₃ x) (Icc 0 T)) ∧
      (∀ x, W₃ x =ᵐ[timeMeasure T] V x) ∧
      Tendsto V₄ l (𝓝 (V₄ x₀)) ∧ TendstoUniformlyOn W₃ (W₃ x₀) l (Icc 0 T) := by
  classical
  intro Z K₄ V hFH
  choose V₄raw W₃ hV₄raw hW₃ hW₃map hW₃ae using fun x =>
    exists_representatives_of_parameterDerivative_forcing_lift g₀ hT (gforce x) (FH x) (hFH x)
  have hstates := tendsto_duhamel_representatives_of_parameterDerivative_forcing_lift
    g₀ hT (gforce x₀) (FH x₀) gforce FH (V₄raw x₀) V₄raw (W₃ x₀) W₃
    (hFH x₀) hFH (hV₄raw x₀) hV₄raw (hW₃ x₀) hW₃ (hW₃ae x₀) hW₃ae hforce hFHlim
  let Q₄ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((2 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 3)
  let V₄ := fun x => Q₄.compLpL 2 (timeMeasure T) (V₄raw x)
  have hV₄lim : Tendsto V₄ l (𝓝 (V₄ x₀)) :=
    ((Q₄.compLpL 2 (timeMeasure T)).continuous.tendsto (V₄raw x₀)).comp hstates.1
  let K₄raw := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 3)
  have hV₄ (x : X) : K₄.compLpL 2 (timeMeasure T) (V₄ x) = V x := by
    have hraw : K₄raw.compLpL 2 (timeMeasure T) (V₄raw x) = V x := hV₄raw x
    have hp := K₄raw.coeFn_compLpL (V₄raw x)
    rw [hraw] at hp
    apply Lp.ext
    filter_upwards [K₄.coeFn_compLpL (V₄ x), Q₄.coeFn_compLpL (V₄raw x), hp]
      with t ht hqt hpt
    change V₄ x t = Q₄ (V₄raw x t) at hqt
    change V x t = K₄raw (V₄raw x t) at hpt
    rw [ht, hqt, hpt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact ⟨V₄, W₃, hV₄, hW₃, hW₃ae, hV₄lim, hstates.2⟩

private theorem reference_initial_forcing_weak_equation_of_projection
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (V₄ : timeL2 (CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2)) T)
    (aN : Lp (TensorHs g₀ 0 0 ((2 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (bN : timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T) :
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let MP₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => M₂)
    let J₂₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let Kscalar := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let V := maximalRegularityDuhamelVectorField hT 0 gforce
    weakParameterEquation g₀ hT gforce f₄ a₂ b₂ →
    (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Kscalar)).compLpL
      2 (timeMeasure T) V₄ = V →
    aN =ᵐ[timeMeasure T] (fun t => M₂ (a₂ t)) →
    bN =ᵐ[timeMeasure T] (fun t => MP₂ (b₂ t)) →
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
        (Kscalar (V₄ t i)) + gforce t i =
        scalarHsMul g₀ 1 (by norm_num) (J₂₁ (aN t))
          (AddCircle.parameterSecondDerivativeHs g₀ 1 (Kscalar (f₄ i + V₄ t i))) +
            J₂₁ (bN t i) := by
  intro M₂ MP₂ J₂₁ Kscalar V hw hv haN hbN
  let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  have hJM₂ (v : TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) :
      J₂₁ (M₂ v) = AH v := by
    apply TensorHs.ext
    rfl
  have hprojection := (ContinuousLinearMap.piLpMap 2
    (fun _ : Fin n => Kscalar)).coeFn_compLpL V₄
  rw [hv] at hprojection
  filter_upwards [hw, haN, hbN, hprojection] with t hwt hat hbt hvt
  intro i
  have hvi := congrArg (fun z => z i) hvt
  change V t i = Kscalar (V₄ t i) at hvi
  have hbi : bN t i = M₂ (b₂ t i) := congrArg (fun z => z i) hbt
  rw [hat, hbi, hJM₂, hJM₂, Kscalar.map_add, ← hvi]
  exact hwt i

private theorem reference_h2_forcing_eq_of_projection
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (F G : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g 0 0 ((2 : ℕ) : ℝ))) T) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)))
    J.compLpL 2 (timeMeasure T) F = J.compLpL 2 (timeMeasure T) G → F = G := by
  intro J h
  apply Lp.ext
  filter_upwards [J.coeFn_compLpL F, J.coeFn_compLpL G] with t hf hg
  have heq := hf.symm.trans ((congrArg (fun f => f t) h).trans hg)
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
  exact congrArg (fun v => v i) heq

private theorem reference_exists_normalized_h2_forcing_coefficients
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (V₄ : X → timeL2 (CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (aTop₂ : X → Lp (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) ∞ (timeMeasure T))
    (haTop₂lim : Tendsto aTop₂ l (𝓝 (aTop₂ x₀)))
    (hb₂lim : Tendsto b₂ l (𝓝 (b₂ x₀)))
    (haTop₂eq : ∀ x, aTop₂ x =ᵐ[timeMeasure T] a₂ x)
    (hweak : ∀ x, weakParameterEquation g₀ hT (gforce x) (f₄ x) (a₂ x) (b₂ x)) :
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    (∀ x, (circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
        2 (timeMeasure T) (V₄ x) = V x) →
    ∃ (aN : X → Lp (TensorHs g₀ 0 0 ((2 : ℕ) : ℝ)) ∞ (timeMeasure T))
      (bN : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T),
      Tendsto aN l (𝓝 (aN x₀)) ∧ Tendsto bN l (𝓝 (bN x₀)) ∧
      (∀ x, aN x =ᵐ[timeMeasure T] fun t => M₂ (a₂ x t)) ∧
      (∀ x, bN x =ᵐ[timeMeasure T]
        fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => M₂) (b₂ x t)) ∧
      let J₂₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
      let Kscalar := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
      ∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
          (Kscalar (V₄ x t i)) + gforce x t i =
          scalarHsMul g₀ 1 (by norm_num) (J₂₁ (aN x t))
            (AddCircle.parameterSecondDerivativeHs g₀ 1 (Kscalar (f₄ x i + V₄ x t i))) +
              J₂₁ (bN x t i) := by
  intro M₂ V hV₄
  let MP₂ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ) :=
    ContinuousLinearMap.piLpMap (𝕜 := ℝ)
      (E := fun _ : Fin n => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1))
      (F := fun _ : Fin n => TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
      2 (fun _ : Fin n => M₂)
  let aTop₂N := fun x => M₂.compLpL ∞ (timeMeasure T) (aTop₂ x)
  let b₂N := fun x => MP₂.compLpL 2 (timeMeasure T) (b₂ x)
  have haTop₂Nlim : Tendsto aTop₂N l (𝓝 (aTop₂N x₀)) :=
    ((M₂.compLpL ∞ (timeMeasure T)).continuous.tendsto (aTop₂ x₀)).comp haTop₂lim
  have hb₂Nlim : Tendsto b₂N l (𝓝 (b₂N x₀)) :=
    ((MP₂.compLpL 2 (timeMeasure T)).continuous.tendsto (b₂ x₀)).comp hb₂lim
  have haTop₂Nae (x : X) : aTop₂N x =ᵐ[timeMeasure T] fun t => M₂ (a₂ x t) :=
    (M₂.coeFn_compLpL (aTop₂ x)).trans ((haTop₂eq x).fun_comp M₂)
  have hb₂Nae (x : X) : b₂N x =ᵐ[timeMeasure T] fun t => MP₂ (b₂ x t) :=
    MP₂.coeFn_compLpL (b₂ x)
  let J₂₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
  let Kscalar := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
  have hlowPDE (x : X) : ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
        (Kscalar (V₄ x t i)) + gforce x t i =
        scalarHsMul g₀ 1 (by norm_num) (J₂₁ (aTop₂N x t))
          (AddCircle.parameterSecondDerivativeHs g₀ 1 (Kscalar (f₄ x i + V₄ x t i))) +
            J₂₁ (b₂N x t i) := by
    exact reference_initial_forcing_weak_equation_of_projection g₀ hT (gforce x) (f₄ x)
      (a₂ x) (b₂ x) (V₄ x) (aTop₂N x) (b₂N x) (hweak x) (hV₄ x)
      (haTop₂Nae x) (hb₂Nae x)
  exact ⟨aTop₂N, b₂N, haTop₂Nlim, hb₂Nlim, haTop₂Nae, hb₂Nae, hlowPDE⟩

private theorem reference_exists_h2_forcing_representative
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (V₄ : X → timeL2 (CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (aTop₂ : X → Lp (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) ∞ (timeMeasure T))
    (hf₄ : Tendsto f₄ l (𝓝 (f₄ x₀)))
    (hV₄lim : Tendsto V₄ l (𝓝 (V₄ x₀)))
    (haTop₂lim : Tendsto aTop₂ l (𝓝 (aTop₂ x₀)))
    (hb₂lim : Tendsto b₂ l (𝓝 (b₂ x₀)))
    (haTop₂eq : ∀ x, aTop₂ x =ᵐ[timeMeasure T] a₂ x)
    (hweak : ∀ x, weakParameterEquation g₀ hT (gforce x) (f₄ x) (a₂ x) (b₂ x)) :
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    (∀ x, (circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
        2 (timeMeasure T) (V₄ x) = V x) →
    ∃ F₂ : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (F₂ x) = gforce x) ∧
      (∀ x, V₄ x = maximalRegularityDuhamelVectorField hT 0 (F₂ x)) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (V₄ x t i) + F₂ x t i =
          scalarHsMul g₀ 2 (by norm_num) (M₂ (a₂ x t))
            (AddCircle.parameterSecondDerivativeHs g₀ 2
              (f₄ x i + V₄ x t i)) + M₂ (b₂ x t i)) ∧
      Tendsto F₂ l (𝓝 (F₂ x₀)) := by
  intro M₂ V hV₄
  obtain ⟨aTop₂N, b₂N, haTop₂Nlim, hb₂Nlim, haTop₂Nae, hb₂Nae, hlowPDE⟩ :=
    reference_exists_normalized_h2_forcing_coefficients g₀ hT x₀ f₄ V₄ gforce a₂ b₂ aTop₂
      haTop₂lim hb₂lim haTop₂eq hweak hV₄
  obtain ⟨F₂, hF₂, hV₂, hPDE₂, hF₂lim⟩ :=
    exists_tendsto_timeL2_parabolic_forcing_lift
      (P := X) (ι := Fin n) (l := l) (n := 1) (m := 2) (T := T)
      g₀ (by decide : 1 ≤ 1)
      (by decide : 1 ≤ 2) hT x₀ f₄ V₄ gforce aTop₂N b₂N hf₄ hV₄lim haTop₂Nlim hb₂Nlim
      hV₄ hlowPDE
  refine ⟨F₂, hF₂, hV₂, ?_, hF₂lim⟩
  intro x
  filter_upwards [hPDE₂ x, haTop₂Nae x, hb₂Nae x] with t ht hat hbt
  intro i
  have hbi : b₂N x t i = M₂ (b₂ x t i) := congrArg (fun z => z i) hbt
  simpa only [hat, hbi] using ht i

private theorem reference_h2_forcing_representative_transport
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (F : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (F₂ : timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T)
    (V₄ : timeL2 (CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2)) T)
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T) :
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let K₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    K₄.compLpL 2 (timeMeasure T) V₄ = maximalRegularityDuhamelVectorField hT 0 F →
    V₄ = maximalRegularityDuhamelVectorField hT 0 F₂ →
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
        (V₄ t i) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (M₂ (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g₀ 2 (f₄ i + V₄ t i)) + M₂ (b₂ t i)) →
    K₄.compLpL 2 (timeMeasure T)
      (maximalRegularityDuhamelVectorField hT 0 F₂) =
        maximalRegularityDuhamelVectorField hT 0 F ∧
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
        (maximalRegularityDuhamelVectorField hT 0 F₂ t i) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (M₂ (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g₀ 2
            (f₄ i + maximalRegularityDuhamelVectorField hT 0 F₂ t i)) + M₂ (b₂ t i) := by
  intro M₂ K₄ hproject hfield heq
  constructor
  · exact (congrArg (fun v => K₄.compLpL 2 (timeMeasure T) v) hfield).symm.trans hproject
  · exact hfield ▸ heq

private theorem reference_exists_h2_forcing_solution
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (V₄ : X → timeL2 (CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (aTop₂ : X → Lp (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) ∞ (timeMeasure T))
    (hf₄ : Tendsto f₄ l (𝓝 (f₄ x₀)))
    (hV₄lim : Tendsto V₄ l (𝓝 (V₄ x₀)))
    (haTop₂lim : Tendsto aTop₂ l (𝓝 (aTop₂ x₀)))
    (hb₂lim : Tendsto b₂ l (𝓝 (b₂ x₀)))
    (haTop₂eq : ∀ x, aTop₂ x =ᵐ[timeMeasure T] a₂ x)
    (hweak : ∀ x, weakParameterEquation g₀ hT (gforce x) (f₄ x) (a₂ x) (b₂ x)) :
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    (∀ x, (circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
        2 (timeMeasure T) (V₄ x) = V x) →
    ∃ F₂ : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (F₂ x) = gforce x) ∧
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 (F₂ x)) = V x) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
          scalarHsMul g₀ 2 (by norm_num) (M₂ (a₂ x t))
            (AddCircle.parameterSecondDerivativeHs g₀ 2
              (f₄ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + M₂ (b₂ x t i)) ∧
      Tendsto F₂ l (𝓝 (F₂ x₀)) := by
  intro M₂ V hV₄
  obtain ⟨F₂, hF₂, hV₂, hPDE₂, hF₂lim⟩ :=
    reference_exists_h2_forcing_representative g₀ hT x₀ f₄ V₄ gforce a₂ b₂ aTop₂
      hf₄ hV₄lim haTop₂lim hb₂lim haTop₂eq hweak hV₄
  have htransport (x : X) := reference_h2_forcing_representative_transport
    g₀ hT (f₄ x) (gforce x) (F₂ x) (V₄ x) (a₂ x) (b₂ x)
    (hV₄ x) (hV₂ x) (hPDE₂ x)
  exact ⟨F₂, hF₂, fun x => (htransport x).1, fun x => (htransport x).2, hF₂lim⟩

private theorem reference_exists_h2_forcing_of_weak_equation
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (V₄ : X → timeL2 (CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (aTop₂ : X → Lp (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) ∞ (timeMeasure T))
    (hf₄ : Tendsto f₄ l (𝓝 (f₄ x₀)))
    (hV₄lim : Tendsto V₄ l (𝓝 (V₄ x₀)))
    (haTop₂lim : Tendsto aTop₂ l (𝓝 (aTop₂ x₀)))
    (hb₂lim : Tendsto b₂ l (𝓝 (b₂ x₀)))
    (haTop₂eq : ∀ x, aTop₂ x =ᵐ[timeMeasure T] a₂ x)
    (hweak : ∀ x, weakParameterEquation g₀ hT (gforce x) (f₄ x) (a₂ x) (b₂ x)) :
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    (∀ x, (circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
        2 (timeMeasure T) (V₄ x) = V x) →
    ∃ F₂ : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (F₂ x) = gforce x) ∧
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 (F₂ x)) = V x) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
          scalarHsMul g₀ 2 (by norm_num) (M₂ (a₂ x t))
            (AddCircle.parameterSecondDerivativeHs g₀ 2
              (f₄ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + M₂ (b₂ x t i)) ∧
      Tendsto F₂ l (𝓝 (F₂ x₀)) ∧
      ∀ F₂' : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
        (∀ x, (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) (F₂' x) = gforce x) →
        Tendsto F₂' l (𝓝 (F₂' x₀)) := by
  intro M₂ V hV₄
  obtain ⟨F₂, hF₂, hV₂, hPDE₂, hF₂lim⟩ :=
    reference_exists_h2_forcing_solution g₀ hT x₀ f₄ V₄ gforce a₂ b₂ aTop₂
      hf₄ hV₄lim haTop₂lim hb₂lim haTop₂eq hweak hV₄
  refine ⟨F₂, hF₂, hV₂, hPDE₂, hF₂lim, ?_⟩
  intro F₂' hF₂'
  have hfamily : F₂' = F₂ := funext fun x =>
    reference_h2_forcing_eq_of_projection g₀ (F₂' x) (F₂ x)
      ((hF₂' x).trans (hF₂ x).symm)
  simpa only [hfamily] using hF₂lim



private theorem reference_exists_h2_forcing_tendsto_timeShift
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (hf₄ : Tendsto f₄ l (𝓝 (f₄ x₀)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (u : X → timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hforce : Tendsto gforce l (𝓝 (gforce x₀)))
    (W : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hWcont : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (hW : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (aTop : X → Lp (TensorHs g₀ 0 0 1) ∞ (timeMeasure T))
    :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    referenceCirclePrincipalNormBounds (n := n) g₀ ρ alpha →
    (∀ x, K₄ (f₄ x) = (f x).val) →
    (∀ x, W x =ᵐ[timeMeasure T] fun t => K (V x t)) →
    (∀ x, referenceCircleSolutionFacts g₀ (f x).val
      (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z) ρ hT (u x) (gforce x)) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W x t‖ ≤ ρ) →
    (∀ x, (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha (f x) (σ x + t) (W x t)))) →
    (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₂ x t))
      =ᵐ[timeMeasure T] (fun t => Cpi (reaction (f x) (σ x + t) (W x t)))) →
    (∀ x, aTop x =ᵐ[timeMeasure T] fun t => alpha (f x) (σ x + t) (W x t)) →
    ∃ F₂ : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (F₂ x) = gforce x) ∧
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 (F₂ x)) = V x) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
          scalarHsMul g₀ 2 (by norm_num) (M₂ (a₂ x t))
            (AddCircle.parameterSecondDerivativeHs g₀ 2
              (f₄ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + M₂ (b₂ x t i)) ∧
      Tendsto F₂ l (𝓝 (F₂ x₀)) ∧
      ∀ F₂' : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
        (∀ x, (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) (F₂' x) = gforce x) →
        Tendsto F₂' l (𝓝 (F₂' x₀)) := by
  classical
  intro K K₄ K₀ P J AH C Cpi M₂ V hcoeff hprincipal hbase hWV hfacts hgood ha₂ hb₂ haTop
  obtain ⟨FH, hFH, hFHlim⟩ :=
    reference_exists_selected_parameterDerivative_forcing_tendsto_timeShift g₀ hT x₀ σ hσ
      fref f f₄ hf₄ F G hF hG hS alpha reaction u gforce hforce W (hWcont x₀) hW
      a₂ b₂ aTop hcoeff hprincipal hbase hWV hfacts hgood ha₂ hb₂ haTop
  obtain ⟨V₄, W₃, hV₄, hW₃, hW₃ae, hV₄lim, hW₃lim⟩ :=
    reference_exists_initial_duhamel_representatives g₀ hT x₀ gforce FH hforce hFHlim hFH
  have hW₃low (x : X) : ∀ t ∈ Icc 0 T, K (W₃ x t) = W x t := by
    apply Measure.eqOn_Icc_of_ae_eq (μ := (volume : Measure ℝ)) (ne_of_lt hT)
      _ (K.continuous.comp_continuousOn (hW₃ x)) (hWcont x)
    exact ((hW₃ae x).fun_comp K).trans (hWV x).symm
  have hf : Tendsto (fun x => (f x).val) l (𝓝 (f x₀).val) := by
    have h := (K₄.continuous.tendsto (f₄ x₀)).comp hf₄
    change Tendsto (fun x => K₄ (f₄ x)) l (𝓝 (K₄ (f₄ x₀))) at h
    simpa only [hbase] using h
  obtain ⟨aTop₂, haTop₂eq, haTop₂lim⟩ :=
    reference_exists_initial_high_principal_tendsto_top g₀ T x₀ σ hσ fref f hf
      F G hF hS alpha reaction W₃ hW₃ hW₃lim W a₂ hcoeff hW₃low hgood ha₂
  have hVlim : Tendsto V l (𝓝 (V x₀)) := by
    let D := maximalRegularityVectorFieldL (ι := Fin n) (g := g₀) (r := 0) (s := 0)
      ((1 : ℕ) : ℝ) hT.le
    have h : Tendsto (fun x => D (gforce x)) l (𝓝 (D (gforce x₀))) :=
      (D.continuous.tendsto (gforce x₀)).comp hforce
    have hD (z : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) :
        D z = maximalRegularityDuhamelVectorField hT 0 z :=
      maximalRegularityVectorFieldL_eq_duhamel hT z
    simpa only [hD] using h
  have hpair := reference_selected_initial_coefficients_tendsto_timeShift
    g₀ T x₀ σ hσ fref f hf F G hF hG hS alpha reaction V hVlim
    W (hWcont x₀) hW a₂ b₂ hcoeff hWV (Eventually.of_forall hgood)
    (hgood x₀).1 (hgood x₀).2.1 (hgood x₀).2.2 ha₂ hb₂
  have hb₂lim : Tendsto b₂ l (𝓝 (b₂ x₀)) := (continuous_snd.tendsto _).comp hpair
  have hweak (x : X) : weakParameterEquation g₀ hT (gforce x) (f₄ x) (a₂ x) (b₂ x) := by
    have ha : (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
        (fun t => C (alpha (f x) (σ x + t) (K (V x t)))) := by
      filter_upwards [ha₂ x, hWV x] with t hat hwt
      simpa only [hwt] using hat
    have hb : (fun t => ContinuousLinearMap.piLpMap 2
        (fun _ : Fin n => AH) (b₂ x t)) =ᵐ[timeMeasure T]
        (fun t => Cpi (reaction (f x) (σ x + t) (K (V x t)))) := by
      filter_upwards [hb₂ x, hWV x] with t hbt hwt
      simpa only [hwt] using hbt
    exact reference_parameterDerivative_weakEquation_of_h2_coefficients g₀
      (f x).val (f₄ x) (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z)
      hT (u x) (gforce x) (a₂ x) (b₂ x) (hfacts x) (hbase x) ha hb
  exact reference_exists_h2_forcing_of_weak_equation g₀ hT x₀ f₄ V₄ gforce a₂ b₂
    aTop₂ hf₄ hV₄lim haTop₂lim hb₂lim haTop₂eq hweak hV₄

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

private theorem reference_exists_continuousOn_h3_representatives_of_forcing_lift
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F₁ : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (F₂ : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T)
    (W₂ : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    {U : Set X} (hF₂ : ContinuousOn F₂ U)
    (hW₂ : ∀ x, ContinuousOn (W₂ x) (Icc 0 T)) :
    let J₂₁ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let K₂₃ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₃₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((3 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ) + 2)
    let K₂₃' := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((3 : ℕ) : ℝ))
    (∀ x, J₂₁.compLpL 2 (timeMeasure T) (F₂ x) = F₁ x) →
    (∀ x, W₂ x =ᵐ[timeMeasure T] fun t =>
      K₂₃ (maximalRegularityDuhamelVectorField hT 0 (F₁ x) t)) →
    ∃ W₃ : X → ℝ → CircleHsPi g₀ (Fin n) ((3 : ℕ) : ℝ),
      (∀ x, ContinuousOn (W₃ x) (Icc 0 T)) ∧
      (∀ x, W₃ x =ᵐ[timeMeasure T] fun t =>
        K₃₄ (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t)) ∧
      (∀ x, ∀ t ∈ Icc 0 T, K₂₃' (W₃ x t) = W₂ x t) ∧
      ∀ x₀ ∈ U, TendstoUniformlyOn W₃ (W₃ x₀) (𝓝[U] x₀) (Icc 0 T) := by
  classical
  intro J₂₁ K₂₃ K₃₄ K₂₃' hFpin hWpin
  have hc := tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g₀ 0 0
  let R := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 2)
  have hex (x : X) :
      ∃ W : ℝ → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 1),
        ContinuousOn W (Icc 0 T) ∧
        W =ᵐ[timeMeasure T] fun t =>
          R (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t) := by
    obtain ⟨W, hW, _, hpin⟩ :=
      maximalRegularityDuhamelVectorMap_exists_continuousOn_representative hT hc 0 (F₂ x)
    exact ⟨W, hW, hpin⟩
  choose W hW hpin using hex
  let N := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((3 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ) + 1)
  let W₃ := fun x t => N (W x t)
  have hW₃ (x : X) : ContinuousOn (W₃ x) (Icc 0 T) :=
    N.continuous.comp_continuousOn (hW x)
  have hN (v : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2)) :
      N (R v) = K₃₄ v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hpin₃ (x : X) : W₃ x =ᵐ[timeMeasure T] fun t =>
      K₃₄ (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t) := by
    filter_upwards [hpin x] with t ht
    change N (W x t) = _
    rw [ht]
    exact hN _
  let L := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
  have hfield (x : X) :
      L.compLpL 2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 (F₂ x)) =
        maximalRegularityDuhamelVectorField hT 0 (F₁ x) := by
    have h := maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) hT hc 0 (F₂ x)
    change L.compLpL 2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 (F₂ x)) =
      maximalRegularityDuhamelVectorField hT (L 0)
        (J₂₁.compLpL 2 (timeMeasure T) (F₂ x)) at h
    rw [map_zero, hFpin x] at h
    exact h
  have hlow (x : X) : (fun t => K₂₃' (W₃ x t)) =ᵐ[timeMeasure T] W₂ x := by
    have hprojection := L.coeFn_compLpL (maximalRegularityDuhamelVectorField hT 0 (F₂ x))
    rw [hfield x] at hprojection
    filter_upwards [hpin₃ x, hWpin x, hprojection] with t h₃ h₂ hp
    rw [h₃, h₂, hp]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  refine ⟨W₃, hW₃, hpin₃, ?_, ?_⟩
  · intro x t ht
    exact Measure.eqOn_Icc_of_ae_eq (μ := (volume : Measure ℝ)) hT.ne (hlow x)
      (K₂₃'.continuous.comp_continuousOn (hW₃ x)) (hW₂ x) ht
  · intro x₀ hx₀
    have hlim := tendstoUniformlyOn_continuousOn_duhamel_representatives hT
      (F₂ x₀) F₂ (W x₀) W (hW x₀) hW (hpin x₀) hpin (hF₂ x₀ hx₀)
    exact N.uniformContinuous.comp_tendstoUniformlyOn hlim

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section


attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts referenceCirclePrincipalNormBounds)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_h2_forcing_family_timeShift
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (hf₄ : Tendsto f₄ l (𝓝 (f₄ x₀)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (u : X → timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hforce : Tendsto gforce l (𝓝 (gforce x₀)))
    (W : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hWcont : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (hW : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    referenceCirclePrincipalNormBounds (n := n) g₀ ρ alpha →
    (∀ x, K₄ (f₄ x) = (f x).val) →
    (∀ x, W x =ᵐ[timeMeasure T] fun t => K (V x t)) →
    (∀ x, referenceCircleSolutionFacts g₀ (f x).val
      (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z) ρ hT (u x) (gforce x)) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W x t‖ ≤ ρ) →
    ∃ (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
      (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T),
      (∀ x, (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
        (fun t => C (alpha (f x) (σ x + t) (W x t)))) ∧
      (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₂ x t))
        =ᵐ[timeMeasure T] (fun t => Cpi (reaction (f x) (σ x + t) (W x t)))) ∧
    ∃ F₂ : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (F₂ x) = gforce x) ∧
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 (F₂ x)) = V x) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
          scalarHsMul g₀ 2 (by norm_num) (M₂ (a₂ x t))
            (AddCircle.parameterSecondDerivativeHs g₀ 2
              (f₄ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + M₂ (b₂ x t i)) ∧
      Tendsto F₂ l (𝓝 (F₂ x₀)) ∧
      ∀ F₂' : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
        (∀ x, (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) (F₂' x) = gforce x) →
        Tendsto F₂' l (𝓝 (F₂' x₀)) := by
  classical
  intro K K₄ K₀ P J AH C Cpi M₂ V hcoeff hprincipal hbase hWV hfacts hgood
  choose a₂ b₂ aTop haRaw hbRaw haTop _ using fun x =>
    reference_exists_coefficient_representatives_timeShift g₀ hT (σ x) fref (f x)
      (gforce x) (W x) (hWcont x) F G hF hG hS alpha reaction hcoeff (hWV x)
      (hgood x).1 (hgood x).2.1 (hgood x).2.2
  let AR := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  have hAH (v : TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) : AH v = C (AR v) := by
    have h := congrArg (fun L => L v) (tensorHsCongrL_incl (g := g₀) (r := 0) (s := 0)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (rfl : ((1 : ℕ) : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))
    simpa only [ContinuousLinearMap.comp_apply, tensorHsCongrL_refl,
      ContinuousLinearMap.id_apply] using h.symm
  have ha₂ (x : X) : (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha (f x) (σ x + t) (W x t))) := by
    filter_upwards [haRaw x] with t ht
    exact (hAH _).trans (congrArg C ht)
  have hb₂ (x : X) :
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₂ x t))
        =ᵐ[timeMeasure T] (fun t => Cpi (reaction (f x) (σ x + t) (W x t))) := by
    filter_upwards [hbRaw x] with t ht
    refine Eq.trans ?_ (congrArg Cpi ht)
    apply PiLp.ext
    intro i
    change AH (b₂ x t i) = C (AR (b₂ x t i))
    exact hAH _
  obtain ⟨F₂, hF₂, hV₂, hPDE₂, hF₂lim, hselected⟩ :=
    reference_exists_h2_forcing_tendsto_timeShift g₀ hT x₀ σ hσ fref f f₄ hf₄
      F G hF hG hS alpha reaction u gforce hforce W hWcont hW a₂ b₂ aTop
      hcoeff hprincipal hbase hWV hfacts hgood ha₂ hb₂ haTop
  exact ⟨a₂, b₂, ha₂, hb₂, F₂, hF₂, hV₂, hPDE₂, hF₂lim, hselected⟩

end DifferentialGeometry.Analysis.Parabolic

end


noncomputable section


attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts referenceCirclePrincipalNormBounds)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_h2_forcing_family_of_solution_timeShift
    {X : Type*} {n : ℕ} {l : Filter X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (hf₄ : Tendsto f₄ l (𝓝 (f₄ x₀)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (u : X → timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hforce : Tendsto gforce l (𝓝 (gforce x₀)))
    :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    referenceCirclePrincipalNormBounds (n := n) g₀ ρ alpha →
    (∀ x, K₄ (f₄ x) = (f x).val) →
    (∀ x, referenceCircleSolutionFacts g₀ (f x).val
      (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z) ρ hT (u x) (gforce x)) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ) →
    ∃ W : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      (∀ x, ContinuousOn (W x) (Icc 0 T)) ∧
      (∀ x, ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (W x t) = (u x).toFun t) ∧
      (∀ x, W x =ᵐ[timeMeasure T] fun t => K (V x t)) ∧
      (∀ x, ∀ t ∈ Icc 0 T, ‖W x t‖ ≤ ρ) ∧
      (∀ x, W x 0 = 0) ∧ TendstoUniformlyOn W (W x₀) l (Icc 0 T) ∧
    ∃ (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
      (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T),
      (∀ x, (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
        (fun t => C (alpha (f x) (σ x + t) (W x t)))) ∧
      (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₂ x t))
        =ᵐ[timeMeasure T] (fun t => Cpi (reaction (f x) (σ x + t) (W x t)))) ∧
    ∃ F₂ : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (F₂ x) = gforce x) ∧
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 (F₂ x)) = V x) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
          scalarHsMul g₀ 2 (by norm_num) (M₂ (a₂ x t))
            (AddCircle.parameterSecondDerivativeHs g₀ 2
              (f₄ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + M₂ (b₂ x t i)) ∧
      Tendsto F₂ l (𝓝 (F₂ x₀)) ∧
      ∀ F₂' : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
        (∀ x, (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) (F₂' x) = gforce x) →
        Tendsto F₂' l (𝓝 (F₂' x₀)) := by
  classical
  intro K K₄ K₀ P J AH C Cpi M₂ V hcoeff hprincipal hbase hfacts htime
  have hex (x : X) :
      ∃ W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
        ContinuousOn W (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (W t) = (u x).toFun t) ∧
        W =ᵐ[timeMeasure T] (fun t => K (V x t)) ∧
        (∀ t ∈ Icc 0 T, ‖W t‖ ≤ ρ) ∧ W 0 = 0 := by
    obtain ⟨W, hWcont, hWlow, hWV, hWnorm, hWzero, _⟩ :=
      reference_solution_exists_continuousOn_representative g₀ (f x).val
        (fun t z => alpha (f x) (σ x + t) z)
        (fun t z => reaction (f x) (σ x + t) z) hT (u x) (gforce x) (hfacts x)
    exact ⟨W, hWcont, hWlow, hWV, hWnorm, hWzero⟩
  choose W hWcont hWlow hWV hWnorm hWzero using hex
  have hW : TendstoUniformlyOn W (W x₀) l (Icc 0 T) :=
    tendstoUniformlyOn_continuousOn_duhamel_representatives hT
      (gforce x₀) gforce (W x₀) W (hWcont x₀) hWcont (hWV x₀) hWV hforce
  obtain ⟨a₂, b₂, ha₂, hb₂, F₂, hF₂, hV₂, hPDE₂, hF₂lim, hselected⟩ :=
    reference_exists_h2_forcing_family_timeShift g₀ hT x₀ σ hσ fref f f₄ hf₄
      F G hF hG hS alpha reaction u gforce hforce W hWcont hW
      hcoeff hprincipal hbase hWV hfacts
      (fun x => ⟨(htime x).1, (htime x).2, hWnorm x⟩)
  exact ⟨W, hWcont, hWlow, hWV, hWnorm, hWzero, hW,
    a₂, b₂, ha₂, hb₂, F₂, hF₂, hV₂, hPDE₂, hF₂lim, hselected⟩

end DifferentialGeometry.Analysis.Parabolic

end


noncomputable section


attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts referenceCirclePrincipalNormBounds)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_continuousOn_h2_forcing_family_timeShift
    {X : Type*} [TopologicalSpace X] {n : ℕ} {U : Set X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (σ : X → ℝ) (hσ : ContinuousOn σ U)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (hf₄ : ContinuousOn f₄ U)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (u : X → timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hforce : ContinuousOn gforce U)
    :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    referenceCirclePrincipalNormBounds (n := n) g₀ ρ alpha →
    (∀ x, K₄ (f₄ x) = (f x).val) →
    (∀ x, referenceCircleSolutionFacts g₀ (f x).val
      (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z) ρ hT (u x) (gforce x)) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ) →
    ∃ W : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      (∀ x, ContinuousOn (W x) (Icc 0 T)) ∧
      (∀ x, ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (W x t) = (u x).toFun t) ∧
      (∀ x, W x =ᵐ[timeMeasure T] fun t => K (V x t)) ∧
      (∀ x, ∀ t ∈ Icc 0 T, ‖W x t‖ ≤ ρ) ∧
      (∀ x, W x 0 = 0) ∧
      (∀ x₀ ∈ U, TendstoUniformlyOn W (W x₀) (𝓝[U] x₀) (Icc 0 T)) ∧
    ∃ (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
      (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T),
      (∀ x, (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
        (fun t => C (alpha (f x) (σ x + t) (W x t)))) ∧
      (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₂ x t))
        =ᵐ[timeMeasure T] (fun t => Cpi (reaction (f x) (σ x + t) (W x t)))) ∧
    ∃ F₂ : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (F₂ x) = gforce x) ∧
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 (F₂ x)) = V x) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
          scalarHsMul g₀ 2 (by norm_num) (M₂ (a₂ x t))
            (AddCircle.parameterSecondDerivativeHs g₀ 2
              (f₄ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + M₂ (b₂ x t i)) ∧
      ContinuousOn F₂ U ∧
      ∀ F₂' : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
        (∀ x, (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) (F₂' x) = gforce x) →
        ContinuousOn F₂' U := by
  classical
  intro K K₄ K₀ P J AH C Cpi M₂ V hcoeff hprincipal hbase hfacts htime
  have hex (x : X) := reference_exists_h2_forcing_family_of_solution_timeShift
    g₀ hT x σ (tendsto_pure_nhds σ x) fref f f₄ (tendsto_pure_nhds f₄ x)
    F G hF hG hS alpha reaction u gforce (tendsto_pure_nhds gforce x)
    hcoeff hprincipal hbase hfacts htime
  choose Wfamily hWcontFamily hWlowFamily hWVFamily hWnormFamily hWzeroFamily
    _ aFamily bFamily haFamily hbFamily forceFamily hforceFamily hVFamily hPDEFamily
    _ _ using hex
  let W := fun x => Wfamily x x
  let a₂ := fun x => aFamily x x
  let b₂ := fun x => bFamily x x
  let F₂ := fun x => forceFamily x x
  have hWcont (x : X) : ContinuousOn (W x) (Icc 0 T) := hWcontFamily x x
  have hWlow (x : X) : ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (W x t) = (u x).toFun t :=
    hWlowFamily x x
  have hWV (x : X) : W x =ᵐ[timeMeasure T] fun t => K (V x t) := hWVFamily x x
  have hWnorm (x : X) : ∀ t ∈ Icc 0 T, ‖W x t‖ ≤ ρ := hWnormFamily x x
  have hWzero (x : X) : W x 0 = 0 := hWzeroFamily x x
  have hWlim (x₀ : X) (hx₀ : x₀ ∈ U) :
      TendstoUniformlyOn W (W x₀) (𝓝[U] x₀) (Icc 0 T) :=
    tendstoUniformlyOn_continuousOn_duhamel_representatives hT
      (gforce x₀) gforce (W x₀) W (hWcont x₀) hWcont (hWV x₀) hWV (hforce x₀ hx₀)
  have hpin (x : X) : (circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
        2 (timeMeasure T) (F₂ x) = gforce x := hforceFamily x x
  have hselected (F₂' : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T)
      (hF₂' : ∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (F₂' x) = gforce x) : ContinuousOn F₂' U := by
    intro x₀ hx₀
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlim⟩ :=
      reference_exists_h2_forcing_family_of_solution_timeShift
        g₀ hT x₀ σ (hσ x₀ hx₀) fref f f₄ (hf₄ x₀ hx₀)
        F G hF hG hS alpha reaction u gforce (hforce x₀ hx₀)
        hcoeff hprincipal hbase hfacts htime
    exact hlim F₂' hF₂'
  refine ⟨W, hWcont, hWlow, hWV, hWnorm, hWzero, hWlim,
    a₂, b₂, ?_, ?_, F₂, hpin, ?_, ?_, hselected F₂ hpin, hselected⟩
  · intro x
    exact haFamily x x
  · intro x
    exact hbFamily x x
  · intro x
    exact hVFamily x x
  · intro x
    exact hPDEFamily x x

end DifferentialGeometry.Analysis.Parabolic

end


noncomputable section


attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
  (referenceCircleSymmetricCoefficientFacts referenceCirclePrincipalNormBounds)

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_exists_continuousOn_h2_forcing_h3_state_timeShift
    {X : Type*} [TopologicalSpace X] {n : ℕ} {U : Set X}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (σ : X → ℝ) (hσ : ContinuousOn σ U)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (f₄ : X → CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (hf₄ : ContinuousOn f₄ U)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (u : X → timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : X → timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hforce : ContinuousOn gforce U)
    :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp K₀
    let J := (circleFirstJet (ι := Fin n) g₀).comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let M₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let V := fun x => maximalRegularityDuhamelVectorField hT 0 (gforce x)
    referenceCircleSymmetricCoefficientFacts g₀ fref P J F G S δ ρ alpha reaction →
    referenceCirclePrincipalNormBounds (n := n) g₀ ρ alpha →
    (∀ x, K₄ (f₄ x) = (f x).val) →
    (∀ x, referenceCircleSolutionFacts g₀ (f x).val
      (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z) ρ hT (u x) (gforce x)) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ) →
    ∃ W : X → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      (∀ x, ContinuousOn (W x) (Icc 0 T)) ∧
      (∀ x, ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (W x t) = (u x).toFun t) ∧
      (∀ x, W x =ᵐ[timeMeasure T] fun t => K (V x t)) ∧
      (∀ x, ∀ t ∈ Icc 0 T, ‖W x t‖ ≤ ρ) ∧
      (∀ x, W x 0 = 0) ∧
      (∀ x₀ ∈ U, TendstoUniformlyOn W (W x₀) (𝓝[U] x₀) (Icc 0 T)) ∧
    ∃ (a₂ : X → timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
      (b₂ : X → timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T),
      (∀ x, (fun t => AH (a₂ x t)) =ᵐ[timeMeasure T]
        (fun t => C (alpha (f x) (σ x + t) (W x t)))) ∧
      (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₂ x t))
        =ᵐ[timeMeasure T] (fun t => Cpi (reaction (f x) (σ x + t) (W x t)))) ∧
    ∃ F₂ : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (F₂ x) = gforce x) ∧
      (∀ x, (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 (F₂ x)) = V x) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
          scalarHsMul g₀ 2 (by norm_num) (M₂ (a₂ x t))
            (AddCircle.parameterSecondDerivativeHs g₀ 2
              (f₄ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + M₂ (b₂ x t i)) ∧
      ContinuousOn F₂ U ∧
      (∀ F₂' : X → timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
        (∀ x, (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) (F₂' x) = gforce x) →
        ContinuousOn F₂' U) ∧
      ∃ W₃ : X → ℝ → CircleHsPi g₀ (Fin n) ((3 : ℕ) : ℝ),
        (∀ x, ContinuousOn (W₃ x) (Icc 0 T)) ∧
        (∀ x, W₃ x =ᵐ[timeMeasure T] fun t =>
          circleHsPiInclusion g₀ (Fin n)
            (by norm_num : ((3 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ) + 2)
              (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t)) ∧
        (∀ x, ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((3 : ℕ) : ℝ)) (W₃ x t) = W x t) ∧
        ∀ x₀ ∈ U, TendstoUniformlyOn W₃ (W₃ x₀) (𝓝[U] x₀) (Icc 0 T) := by
  intro K K₄ K₀ P J AH C Cpi M₂ V hcoeff hprincipal hbase hfacts htime
  obtain ⟨W, hWcont, hWlow, hWV, hWnorm, hWzero, hWlim,
      a₂, b₂, ha₂, hb₂, F₂, hF₂, hV₂, hPDE₂, hF₂cont, hselected⟩ :=
    reference_exists_continuousOn_h2_forcing_family_timeShift
      g₀ hT σ hσ fref f f₄ hf₄ F G hF hG hS alpha reaction u gforce hforce
      hcoeff hprincipal hbase hfacts htime
  obtain ⟨W₃, hW₃cont, hW₃ae, hW₃low, hW₃lim⟩ :=
    reference_exists_continuousOn_h3_representatives_of_forcing_lift
      g₀ hT gforce F₂ W hF₂cont hWcont hF₂ hWV
  exact ⟨W, hWcont, hWlow, hWV, hWnorm, hWzero, hWlim,
    a₂, b₂, ha₂, hb₂, F₂, hF₂, hV₂, hPDE₂, hF₂cont, hselected,
    W₃, hW₃cont, hW₃ae, hW₃low, hW₃lim⟩

end DifferentialGeometry.Analysis.Parabolic

end

open private
  parameterDerivativeForcingFieldLift
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.parameterDerivativeForcingFieldLift
  parameterDerivative_field_lift_of_forcing_lift
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.parameterDerivative_field_lift_of_forcing_lift from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

private theorem reference_parameterDerivative_forcing_field_lift_timeShift
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (σ : ℝ)
    (fref : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : Metric.closedBall fref δ)
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let K₄ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let AH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let V := maximalRegularityDuhamelVectorField hT 0 gforce
    referenceCirclePrincipalNormBounds (n := n) g₀ ρ alpha →
    K₄ f₄ = f.val →
    (W =ᵐ[timeMeasure T] fun t => K (V t)) →
    referenceCircleSolutionFacts g₀ f.val
      (fun t z => alpha f (σ + t) z)
      (fun t z => reaction f (σ + t) z) ρ hT u gforce →
    (-ρ ≤ σ ∧ σ + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W t‖ ≤ ρ) →
    (fun t => AH (a₂ t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha f (σ + t) (W t))) →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => AH) (b₂ t))
      =ᵐ[timeMeasure T] (fun t => Cpi (reaction f (σ + t) (W t))) →
    parameterDerivativeForcingFieldLift g₀ hT gforce := by
  intro K K₄ AH C Cpi V hprincipal hbase hWV hfacts hgood ha₂ hb₂
  have hpair : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (AH (a₂ t))‖ ≤ (1 / 4 : ℝ) ∧
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (AH (a₂ t))‖ ≤ (1 / 4 : ℝ) := by
    filter_upwards [ha₂, ae_restrict_mem measurableSet_Icc] with t hat htt
    have ht : σ + t ∈ Icc (-ρ) ρ := by
      constructor <;> linarith [htt.1, htt.2, hgood.1, hgood.2.1]
    have hp := hprincipal f (σ + t) ht (W t) (hgood.2.2 t htt)
    rw [hat]
    exact hp
  have ha : (fun t => AH (a₂ t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha f (σ + t) (K (V t)))) := by
    filter_upwards [ha₂, hWV] with t hat hwt
    simpa only [hwt] using hat
  have hb : (fun t => ContinuousLinearMap.piLpMap 2
      (fun _ : Fin n => AH) (b₂ t)) =ᵐ[timeMeasure T]
      (fun t => Cpi (reaction f (σ + t) (K (V t)))) := by
    filter_upwards [hb₂, hWV] with t hbt hwt
    simpa only [hwt] using hbt
  obtain ⟨FH, hFH⟩ := exists_parameterDerivative_forcing_lift_of_principal_norm_lt_one
    g₀ hT gforce f₄ a₂ b₂ (1 / 4) (1 / 4)
    (by simpa [AH] using hpair.mono (fun _ h => h.1))
    (by simpa [AH] using hpair.mono (fun _ h => h.2))
    (by norm_num) (by norm_num)
    (reference_parameterDerivative_weakEquation_of_h2_coefficients g₀
      f.val f₄ (fun t z => alpha f (σ + t) z)
      (fun t z => reaction f (σ + t) z)
      hT u gforce a₂ b₂ hfacts hbase ha hb)
  exact ⟨FH, hFH, parameterDerivative_field_lift_of_forcing_lift g₀ hT gforce FH hFH⟩

end DifferentialGeometry.Analysis.Parabolic

end
