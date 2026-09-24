import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.LinearTransport
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleDerivativeForcingLift
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientFamilies
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions

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
  referenceCircleSymmetricCoefficientFacts
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.referenceCircleSymmetricCoefficientFacts from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
open private
  DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
open private
  exists_tendsto_forcing_successor_of_coefficient_lift
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_tendsto_forcing_successor_of_coefficient_lift
  scalarSobolevPiInclusion
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.scalarSobolevPiInclusion from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleDerivativeForcingLift
open private
  reference_successor_principal_from_projection
  DifferentialGeometry.Analysis.Parabolic.reference_successor_principal_from_projection
  reference_exists_selected_coefficient_family_nat
  DifferentialGeometry.Analysis.Parabolic.reference_exists_selected_coefficient_family_nat from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientFamilies
open private
  compLpL_injective_of_injective
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.compLpL_injective_of_injective from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.LinearTransport
open private
  duhamel_parabolic_equation_of_common_baseline
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.duhamel_parabolic_equation_of_common_baseline from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcing

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev QuasiLinear MaximalRegularity
open AddCircle

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

private theorem reference_exists_tendsto_forcing_successor
    {X : Type*} {n : ℕ} {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (fHigh : X → CircleHsPi g (Fin n) (((k + 3 : ℕ) : ℝ) + 2))
    (force : X → timeL2 (CircleHsPi g (Fin n) ((k + 2 : ℕ) : ℝ)) T)
    (W : X → ℝ → CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ))
    (hW : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (a : X → timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (b : X → timeL2 (CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ)) T)
    (aTop₁ : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (Ch Cl : X → ℝ≥0)
    (hforce : Tendsto force l (𝓝 (force x₀)))
    (hfHigh : Tendsto fHigh l (𝓝 (fHigh x₀)))
    (ha : Tendsto a l (𝓝 (a x₀))) (hb : Tendsto b l (𝓝 (b x₀)))
    (hWlim : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (haTop₁lim : Tendsto aTop₁ l (𝓝 (aTop₁ x₀)))
    (diffusion : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (drift : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hdiffusion : ContDiffOn ℝ ∞ diffusion S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin n) 1) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let R := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
    let K₀ := circleHsPiInclusion g (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P₀ := (circleFirstJet (ι := Fin n) g).comp K₀
    let J₀ := (circleFirstJet (ι := Fin n) g).comp (circleHsPiCongr g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let Aphys := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith [hk] :
        (1 : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let U := fun x => maximalRegularityDuhamelVectorField hT 0 (force x)
    referenceCircleSymmetricCoefficientFacts g fref P₀ J₀ diffusion drift S δ ρ alpha reaction →
    (∀ x, R (fHigh x) = (f x).val) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ) →
    (∀ x, (fun t => Aphys (a x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (L (W x t)))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i, W x t i = K (U x t i)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U x t i) +
        force x t i = scalarHsMul g (k + 2) (by simp) (J (a x t))
          (parameterSecondDerivativeHs g (k + 2) (P (fHigh x i) + U x t i)) + J (b x t i)) →
    (∀ x, aTop₁ x =ᵐ[timeMeasure T] (fun t => A (a x t))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := Fin n) g (A (a x t))‖ ≤ Ch x) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := Fin n) g (A (a x t))‖ ≤ Cl x) →
    (∀ x, (Ch x : ℝ) < 1) → (∀ x, (Cl x : ℝ) < 1) →
    ∃ (forceNext : X → timeL2 (CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ)) T)
      (Vnext : X → timeL2 (CircleHsPi g (Fin n) (((k + 3 : ℕ) : ℝ) + 2)) T)
      (Wnext : X → ℝ → CircleHsPi g (Fin n) (((k + 2 : ℕ) : ℝ) + 2)),
      (∀ x, (ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : Fin n => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
        (F := fun _ : Fin n => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)) 2 (fun _ : Fin n => J)).compLpL
        2 (timeMeasure T) (forceNext x) = force x) ∧
      (∀ x, Vnext x = maximalRegularityDuhamelVectorField hT 0 (forceNext x)) ∧
      (∀ x, ContinuousOn (Wnext x) (Icc 0 T)) ∧
      (∀ x t, t ∈ Icc 0 T →
        ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : Fin n => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))
        (F := fun _ : Fin n => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) 2 (fun _ : Fin n => K) (Wnext x t) = W x t) ∧
      (∀ x, Wnext x =ᵐ[timeMeasure T]
        fun t => ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : Fin n => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))
        (F := fun _ : Fin n => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)) 2 (fun _ : Fin n => P) (Vnext x t)) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 3 : ℕ) : ℝ) (Vnext x t i) +
          forceNext x t i = scalarHsMul g (k + 3) (by simp) (a x t)
            (parameterSecondDerivativeHs g (k + 3) (fHigh x i + Vnext x t i)) + b x t i) ∧
      Tendsto forceNext l (𝓝 (forceNext x₀)) ∧
      Tendsto Vnext l (𝓝 (Vnext x₀)) ∧
      TendstoUniformlyOn Wnext (Wnext x₀) l (Icc 0 T) := by
  intro J A P K R L K₀ P₀ J₀ Aphys U hcoeff hf hgood haPhysical hWU hPDE
    haTop₁ hCh hCl hChlt hCllt
  apply exists_tendsto_forcing_successor_of_coefficient_lift
    (X := X) (ι := Fin n) (l := l) (T := T)
    (g := g) (k := k) (hT := hT) (x₀ := x₀) (F := force) (f := fHigh)
    (W := W) (hW := hW) (a := a) (b := b) (aTop := aTop₁) (Ch := Ch) (Cl := Cl)
    (hF := hforce) (hf := hfHigh) (ha := ha) (hb := hb) (hWlim := hWlim)
    (haToplim := haTop₁lim)
    (hcoeffLift := fun Wnext hWnext hWproject hWnextlim =>
      reference_successor_principal_from_projection
        (X := X) (n := n) (l := l) g k T x₀ σ hσ fref f fHigh W Wnext
        hWnext hfHigh hWnextlim a diffusion drift hdiffusion hS alpha reaction
        hcoeff hf hgood haPhysical hWproject)
    hWU hPDE haTop₁ hCh hCl hChlt hCllt

end DifferentialGeometry.Analysis.Parabolic

end


noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev QuasiLinear MaximalRegularity
open AddCircle

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

private theorem reference_selected_forcing_successor
    {X : Type*} {n : ℕ} {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {T : ℝ} (hT : 0 < T) (x₀ : X)
    (σ : X → ℝ) (hσ : Tendsto σ l (𝓝 (σ x₀)))
    (fref : CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (fHigh : X → CircleHsPi g (Fin n) (((k + 3 : ℕ) : ℝ) + 2))
    (force : X → timeL2 (CircleHsPi g (Fin n) ((k + 2 : ℕ) : ℝ)) T)
    (W : X → ℝ → CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ))
    (forceSelected : X → timeL2 (CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ)) T)
    (Wselected : X → ℝ → CircleHsPi g (Fin n) (((k + 2 : ℕ) : ℝ) + 2))
    (hW : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (a : X → timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (b : X → timeL2 (CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ)) T)
    (aTop₁ : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (Ch Cl : X → ℝ≥0)
    (hforce : Tendsto force l (𝓝 (force x₀)))
    (hfHigh : Tendsto fHigh l (𝓝 (fHigh x₀)))
    (ha : Tendsto a l (𝓝 (a x₀))) (hb : Tendsto b l (𝓝 (b x₀)))
    (hWlim : TendstoUniformlyOn W (W x₀) l (Icc 0 T))
    (haTop₁lim : Tendsto aTop₁ l (𝓝 (aTop₁ x₀)))
    (diffusion : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (drift : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hdiffusion : ContDiffOn ℝ ∞ diffusion S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin n) 1) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let R := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
    let K₀ := circleHsPiInclusion g (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P₀ := (circleFirstJet (ι := Fin n) g).comp K₀
    let J₀ := (circleFirstJet (ι := Fin n) g).comp (circleHsPiCongr g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let Aphys := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith [hk] :
        (1 : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let U := fun x => maximalRegularityDuhamelVectorField hT 0 (force x)
    referenceCircleSymmetricCoefficientFacts g fref P₀ J₀ diffusion drift S δ ρ alpha reaction →
    (∀ x, R (fHigh x) = (f x).val) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ) →
    (∀ x, (fun t => Aphys (a x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (L (W x t)))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i, W x t i = K (U x t i)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U x t i) +
        force x t i = scalarHsMul g (k + 2) (by simp) (J (a x t))
          (parameterSecondDerivativeHs g (k + 2) (P (fHigh x i) + U x t i)) + J (b x t i)) →
    (∀ x, aTop₁ x =ᵐ[timeMeasure T] (fun t => A (a x t))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := Fin n) g (A (a x t))‖ ≤ Ch x) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := Fin n) g (A (a x t))‖ ≤ Cl x) →
    (∀ x, (Ch x : ℝ) < 1) → (∀ x, (Cl x : ℝ) < 1) →
    (∀ x, (ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : Fin n => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
        (F := fun _ : Fin n => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)) 2 (fun _ : Fin n => J)).compLpL
      2 (timeMeasure T) (forceSelected x) = force x) →
    (∀ x t, t ∈ Icc 0 T →
      ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : Fin n => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))
        (F := fun _ : Fin n => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) 2 (fun _ : Fin n => K) (Wselected x t) = W x t) →
    let Vselected := fun x => maximalRegularityDuhamelVectorField hT 0 (forceSelected x)
    (∀ x, ContinuousOn (Wselected x) (Icc 0 T)) ∧
    (∀ x, Wselected x =ᵐ[timeMeasure T]
      fun t => ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : Fin n => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))
        (F := fun _ : Fin n => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)) 2 (fun _ : Fin n => P) (Vselected x t)) ∧
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 3 : ℕ) : ℝ) (Vselected x t i) +
        forceSelected x t i = scalarHsMul g (k + 3) (by simp) (a x t)
          (parameterSecondDerivativeHs g (k + 3) (fHigh x i + Vselected x t i)) + b x t i) ∧
    Tendsto forceSelected l (𝓝 (forceSelected x₀)) ∧
    Tendsto Vselected l (𝓝 (Vselected x₀)) ∧
    TendstoUniformlyOn Wselected (Wselected x₀) l (Icc 0 T) := by
  intro J A P K R L K₀ P₀ J₀ Aphys U hcoeff hf hgood haPhysical hWU hPDE
    haTop₁ hCh hCl hChlt hCllt hSelected hWSelected Vselected
  obtain ⟨forceNext, Vnext, Wnext, hforceNext, hVforceNext, hWnext, hWproject,
      hWV, hhigh, hforceNextlim, hVnextlim, hWnextlim⟩ :=
    reference_exists_tendsto_forcing_successor g k hT x₀ σ hσ fref f fHigh force W hW
      a b aTop₁ Ch Cl hforce hfHigh ha hb hWlim haTop₁lim diffusion drift hdiffusion hS
      alpha reaction hcoeff hf hgood haPhysical hWU hPDE haTop₁ hCh hCl hChlt hCllt
  let JV := ContinuousLinearMap.piLpMap (𝕜 := ℝ)
        (E := fun _ : Fin n => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
        (F := fun _ : Fin n => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)) 2 (fun _ : Fin n => J)
  have hJV : Function.Injective JV := by
    intro u v huv
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    exact congrArg (fun z => z i) huv
  have heqF (x : X) : forceNext x = forceSelected x := by
    apply compLpL_injective_of_injective JV hJV
    exact (hforceNext x).trans (hSelected x).symm
  have heqV (x : X) : Vnext x = Vselected x := by
    rw [hVforceNext x, heqF x]
  have heqW (x : X) : EqOn (Wnext x) (Wselected x) (Icc 0 T) := by
    intro t ht
    have hp := (hWproject x t ht).trans (hWSelected x t ht).symm
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    exact congrArg (fun z => z i) hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hWnext x).congr (heqW x).symm
  · intro x
    filter_upwards [hWV x, ae_restrict_mem measurableSet_Icc] with t ht htt
    rw [← heqW x htt, ← heqV x]
    exact ht
  · simpa only [heqF, heqV] using hhigh
  · simpa only [funext heqF] using hforceNextlim
  · simpa only [funext heqV] using hVnextlim
  · exact (hWnextlim.congr (Eventually.of_forall heqW)).congr_right (heqW x₀)

end DifferentialGeometry.Analysis.Parabolic

end


noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev QuasiLinear MaximalRegularity
open AddCircle

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

private theorem reference_exists_sobolev_successor_coefficients_timeShift
    {X : Type*} [TopologicalSpace X] {n : ℕ} {D : Set X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {T : ℝ} (hT : 0 < T) (σ : X → ℝ) (hσ : ContinuousOn σ D)
    (fref : CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (f₀ : X → CircleHsPi g (Fin n) (((2 : ℕ) : ℝ) + 2))
    (H : X → CircleHsPi g (Fin n) (((k + 3 : ℕ) : ℝ) + 2))
    (hHcont : ContinuousOn H D)
    (diffusion : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (drift : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hdiffusion : ContDiffOn ℝ ∞ diffusion S)
    (hdrift : ContDiffOn ℝ ∞ drift S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin n) 1)
    (F₂ : X → timeL2 (CircleHsPi g (Fin n) ((2 : ℕ) : ℝ)) T)
    (W₂ : X → ℝ → CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1))
    (W₃ : X → ℝ → CircleHsPi g (Fin n) ((3 : ℕ) : ℝ))
    (a₂ : X → timeL2 (TensorHs g 0 0 ((2 : ℕ) : ℝ)) T)
    (b₂ : X → timeL2 (CircleHsPi g (Fin n) ((2 : ℕ) : ℝ)) T)
    (aTop₁ : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (force : X → timeL2 (CircleHsPi g (Fin n) ((k + 2 : ℕ) : ℝ)) T)
    (W : X → ℝ → CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ))
    (hforceCont : ContinuousOn force D)
    (hW : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (hWlim : ∀ x₀ ∈ D, TendstoUniformlyOn W (W x₀) (𝓝[D] x₀) (Icc 0 T)) :
    let K₀ := circleHsPiInclusion g (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P₀ := (circleFirstJet (ι := Fin n) g).comp K₀
    let J₀ := (circleFirstJet (ι := Fin n) g).comp (circleHsPiCongr g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let A₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ))
    let E₁ := tensorHsCongrL g 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    referenceCircleSymmetricCoefficientFacts g fref P₀ J₀ diffusion drift S δ ρ alpha reaction →
    (∀ x, circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2) (H x) = (f x).val) →
    (∀ x, circleHsPiInclusion g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2) (f₀ x) = (f x).val) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W₂ x t‖ ≤ ρ) →
    (∀ x t, t ∈ Icc 0 T → circleHsPiInclusion g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((3 : ℕ) : ℝ)) (W₃ x t) = W₂ x t) →
    (∀ x, (fun t => A₂ (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (W₂ x t))) →
    (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ x t))
      =ᵐ[timeMeasure T] (fun t => reaction (f x) (σ x + t) (W₂ x t))) →
    (∀ x, aTop₁ x =ᵐ[timeMeasure T] fun t => E₁ (alpha (f x) (σ x + t) (W₂ x t))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := Fin n) g (aTop₁ x t)‖ ≤ (1 / 4 : ℝ)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := Fin n) g (aTop₁ x t)‖ ≤ (1 / 4 : ℝ)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
        scalarHsMul g 2 (by norm_num) (a₂ x t)
          (parameterSecondDerivativeHs g 2
            (f₀ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + b₂ x t i) →
    (∀ x, (circleHsPiInclusion g (Fin n)
      (by exact_mod_cast (show 2 ≤ k + 2 by omega) :
        ((2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (force x) = F₂ x) →
    (∀ x, W x =ᵐ[timeMeasure T] fun t => circleHsPiInclusion g (Fin n)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
        (maximalRegularityDuhamelVectorField hT 0 (force x) t)) →
    (∀ x t, t ∈ Icc 0 T → circleHsPiInclusion g (Fin n)
      (by exact_mod_cast (show 3 ≤ k + 3 by omega) :
        ((3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)) (W x t) = W₃ x t) →
    ∃ (a : X → timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
      (b : X → timeL2 (CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ)) T),
      let U := fun x => maximalRegularityDuhamelVectorField hT 0 (force x)
      let L := circleHsPiInclusion g (Fin n)
        (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
          ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
      let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
      let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
          ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
      let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
      let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
          ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
      let Aphys := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
          (1 : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
      (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ) ∧
      (∀ x, (fun t => Aphys (a x t)) =ᵐ[timeMeasure T]
        fun t => alpha (f x) (σ x + t) (L (W x t))) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i, W x t i = K (U x t i)) ∧
      (∀ x, aTop₁ x =ᵐ[timeMeasure T] fun t => A (a x t)) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T,
        ‖parameterPrincipalOperatorHsPi (ι := Fin n) g (A (a x t))‖ ≤ (1 / 4 : ℝ≥0)) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T,
        ‖parameterPrincipalOperatorH0Pi (ι := Fin n) g (A (a x t))‖ ≤ (1 / 4 : ℝ≥0)) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U x t i) +
          force x t i = scalarHsMul g (k + 2) (by simp) (J (a x t))
            (parameterSecondDerivativeHs g (k + 2) (P (H x i) + U x t i)) + J (b x t i)) ∧
      ∀ x₀ ∈ D, Tendsto (fun x => (a x, b x)) (𝓝[D] x₀) (𝓝 (a x₀, b x₀)) := by
  classical
  intro K₀ P₀ J₀ A₂ E₁ hcoeff hbaseH hbase₀ htime hW₃₂ ha₂ hb₂ haTop₁
    hCh₁ hCl₁ hPDE₂ hforce₂ hWU hWW₃
  let U := fun x => maximalRegularityDuhamelVectorField hT 0 (force x)
  let L := circleHsPiInclusion g (Fin n)
    (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
  let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
      ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
  let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
      ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  have hLW (x : X) (t : ℝ) (ht : t ∈ Icc 0 T) : L (W x t) = W₂ x t := by
    rw [← hW₃₂ x t ht, ← hWW₃ x t ht]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hgood (x : X) : -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧
      ∀ t ∈ Icc 0 T, ‖L (W x t)‖ ≤ ρ := by
    refine ⟨(htime x).1, (htime x).2.1, ?_⟩
    intro t ht
    rw [hLW x t ht]
    exact (htime x).2.2 t ht
  have habase (x : X) : (fun t => A₂ (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (L (W x t))) := by
    filter_upwards [ha₂ x, ae_restrict_mem measurableSet_Icc] with t ht htt
    rw [hLW x t htt]
    exact ht
  have hbbase (x : X) :
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ x t))
        =ᵐ[timeMeasure T] (fun t => reaction (f x) (σ x + t) (L (W x t))) := by
    filter_upwards [hb₂ x, ae_restrict_mem measurableSet_Icc] with t ht htt
    rw [hLW x t htt]
    exact ht
  obtain ⟨a, b, ha₂proj, hb₂proj, haPhysical, _, hablim⟩ :=
    reference_exists_selected_coefficient_family_nat
      (X := X) (n := n) (T := T) g k hT σ fref f H force W hW
      diffusion drift hdiffusion hdrift hS alpha reaction
      (fun x t => a₂ x t) (fun x t => b₂ x t)
      (fun x => (Lp.memLp (a₂ x)).aestronglyMeasurable)
      (fun x => (Lp.memLp (b₂ x)).aestronglyMeasurable)
      hcoeff (hbaseH) hWU hgood habase hbbase
  have hWUi (x : X) : ∀ᵐ t ∂timeMeasure T, ∀ i,
      W x t i = K (U x t i) := by
    filter_upwards [hWU x] with t ht
    intro i
    exact congrArg (fun z => z i) ht
  let Aphys := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
      (1 : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  have hE₁A (v : TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) : E₁ (Aphys v) = A v := by
    have h := tensorHsCongrL_incl (g := g) (r := 0) (s := 0)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (rfl : ((k + 3 : ℕ) : ℝ) = ((k + 3 : ℕ) : ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        (1 : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
        ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    simpa only [E₁, Aphys, A, ContinuousLinearMap.comp_apply,
      tensorHsCongrL_refl, ContinuousLinearMap.id_apply] using congrArg (fun L => L v) h
  have haTop (x : X) : aTop₁ x =ᵐ[timeMeasure T] fun t => A (a x t) := by
    filter_upwards [haTop₁ x, haPhysical x, ae_restrict_mem measurableSet_Icc]
      with t hat hpt htt
    change Aphys (a x t) = alpha (f x) (σ x + t) (L (W x t)) at hpt
    rw [hLW x t htt] at hpt
    rw [hat, ← hpt]
    exact hE₁A (a x t)
  have hCh (x : X) : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := Fin n) g (A (a x t))‖ ≤ (1 / 4 : ℝ≥0) := by
    filter_upwards [haTop x, hCh₁ x] with t ht hct
    rw [← ht]
    exact_mod_cast hct
  have hCl (x : X) : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := Fin n) g (A (a x t))‖ ≤ (1 / 4 : ℝ≥0) := by
    filter_upwards [haTop x, hCl₁ x] with t ht hct
    rw [← ht]
    exact_mod_cast hct
  have hPDE (x : X) : ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ) (U x t i) +
        force x t i = scalarHsMul g (k + 2) (by simp) (J (a x t))
          (parameterSecondDerivativeHs g (k + 2) (P (H x i) + U x t i)) + J (b x t i) := by
    exact duhamel_parabolic_equation_of_common_baseline g k hT (f x).val
      (H x) (f₀ x) (force x) (F₂ x) (fun t => a x t) (fun t => b x t)
      (fun t => a₂ x t) (fun t => b₂ x t)
      (hbaseH x) (hbase₀ x) (hforce₂ x) (ha₂proj x) (hb₂proj x) (hPDE₂ x)
  refine ⟨a, b, hgood, haPhysical, hWUi, haTop, hCh, hCl, hPDE, ?_⟩
  intro x₀ hx₀
  exact hablim (𝓝[D] x₀) x₀ (hσ x₀ hx₀) (hHcont x₀ hx₀)
    (hforceCont x₀ hx₀) (hWlim x₀ hx₀)

private theorem reference_exists_continuousOn_sobolev_forcing_successor_timeShift
    {X : Type*} [TopologicalSpace X] {n : ℕ} {D : Set X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {T : ℝ} (hT : 0 < T) (σ : X → ℝ) (hσ : ContinuousOn σ D)
    (fref : CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (f₀ : X → CircleHsPi g (Fin n) (((2 : ℕ) : ℝ) + 2))
    (H : X → CircleHsPi g (Fin n) (((k + 3 : ℕ) : ℝ) + 2))
    (hHcont : ContinuousOn H D)
    (diffusion : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (drift : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hdiffusion : ContDiffOn ℝ ∞ diffusion S)
    (hdrift : ContDiffOn ℝ ∞ drift S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin n) 1)
    (F₂ : X → timeL2 (CircleHsPi g (Fin n) ((2 : ℕ) : ℝ)) T)
    (W₂ : X → ℝ → CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1))
    (W₃ : X → ℝ → CircleHsPi g (Fin n) ((3 : ℕ) : ℝ))
    (a₂ : X → timeL2 (TensorHs g 0 0 ((2 : ℕ) : ℝ)) T)
    (b₂ : X → timeL2 (CircleHsPi g (Fin n) ((2 : ℕ) : ℝ)) T)
    (aTop₁ : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (haTop₁cont : ContinuousOn aTop₁ D)
    (force : X → timeL2 (CircleHsPi g (Fin n) ((k + 2 : ℕ) : ℝ)) T)
    (W : X → ℝ → CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ))
    (hforceCont : ContinuousOn force D)
    (hW : ∀ x, ContinuousOn (W x) (Icc 0 T))
    (hWlim : ∀ x₀ ∈ D, TendstoUniformlyOn W (W x₀) (𝓝[D] x₀) (Icc 0 T)) :
    let K₀ := circleHsPiInclusion g (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P₀ := (circleFirstJet (ι := Fin n) g).comp K₀
    let J₀ := (circleFirstJet (ι := Fin n) g).comp (circleHsPiCongr g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let A₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ))
    let E₁ := tensorHsCongrL g 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    referenceCircleSymmetricCoefficientFacts g fref P₀ J₀ diffusion drift S δ ρ alpha reaction →
    (∀ x, circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2) (H x) = (f x).val) →
    (∀ x, circleHsPiInclusion g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2) (f₀ x) = (f x).val) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W₂ x t‖ ≤ ρ) →
    (∀ x t, t ∈ Icc 0 T → circleHsPiInclusion g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((3 : ℕ) : ℝ)) (W₃ x t) = W₂ x t) →
    (∀ x, (fun t => A₂ (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (W₂ x t))) →
    (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ x t))
      =ᵐ[timeMeasure T] (fun t => reaction (f x) (σ x + t) (W₂ x t))) →
    (∀ x, aTop₁ x =ᵐ[timeMeasure T] fun t => E₁ (alpha (f x) (σ x + t) (W₂ x t))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := Fin n) g (aTop₁ x t)‖ ≤ (1 / 4 : ℝ)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := Fin n) g (aTop₁ x t)‖ ≤ (1 / 4 : ℝ)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
        scalarHsMul g 2 (by norm_num) (a₂ x t)
          (parameterSecondDerivativeHs g 2
            (f₀ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + b₂ x t i) →
    (∀ x, (circleHsPiInclusion g (Fin n)
      (by exact_mod_cast (show 2 ≤ k + 2 by omega) :
        ((2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) (force x) = F₂ x) →
    (∀ x, W x =ᵐ[timeMeasure T] fun t => circleHsPiInclusion g (Fin n)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
        (maximalRegularityDuhamelVectorField hT 0 (force x) t)) →
    (∀ x t, t ∈ Icc 0 T → circleHsPiInclusion g (Fin n)
      (by exact_mod_cast (show 3 ≤ k + 3 by omega) :
        ((3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)) (W x t) = W₃ x t) →
    ∃ (forceNext : X → timeL2 (CircleHsPi g (Fin n) ((k + 1 + 2 : ℕ) : ℝ)) T)
      (Wnext : X → ℝ → CircleHsPi g (Fin n) ((k + 1 + 3 : ℕ) : ℝ)),
      (∀ x, (circleHsPiInclusion g (Fin n)
        (by exact_mod_cast (show 2 ≤ k + 1 + 2 by omega) :
          ((2 : ℕ) : ℝ) ≤ ((k + 1 + 2 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) (forceNext x) = F₂ x) ∧
      (∀ x, ContinuousOn (Wnext x) (Icc 0 T)) ∧
      (∀ x, Wnext x =ᵐ[timeMeasure T] fun t => circleHsPiInclusion g (Fin n)
        (by push_cast; linarith : ((k + 1 + 3 : ℕ) : ℝ) ≤ ((k + 1 + 2 : ℕ) : ℝ) + 2)
          (maximalRegularityDuhamelVectorField hT 0 (forceNext x) t)) ∧
      (∀ x t, t ∈ Icc 0 T → circleHsPiInclusion g (Fin n)
        (by exact_mod_cast (show 3 ≤ k + 1 + 3 by omega) :
          ((3 : ℕ) : ℝ) ≤ ((k + 1 + 3 : ℕ) : ℝ)) (Wnext x t) = W₃ x t) ∧
      ContinuousOn forceNext D ∧
      ∀ x₀ ∈ D, TendstoUniformlyOn Wnext (Wnext x₀) (𝓝[D] x₀) (Icc 0 T) := by
  classical
  intro K₀ P₀ J₀ A₂ E₁ hcoeff hbaseH hbase₀ htime hW₃₂ ha₂ hb₂ haTop₁
    hCh₁ hCl₁ hPDE₂ hforce₂ hWU hWW₃
  let U := fun x => maximalRegularityDuhamelVectorField hT 0 (force x)
  let L := circleHsPiInclusion g (Fin n)
    (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((k + 3 : ℕ) : ℝ))
  let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
      ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
  let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
      ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  obtain ⟨a, b, hgood, haPhysical, hWUi, haTop, hCh, hCl, hPDE, hAB⟩ :=
    reference_exists_sobolev_successor_coefficients_timeShift g k hT σ hσ fref f f₀ H
      hHcont diffusion drift hdiffusion hdrift hS alpha reaction F₂ W₂ W₃ a₂ b₂ aTop₁
      force W hforceCont hW hWlim hcoeff hbaseH hbase₀ htime hW₃₂ ha₂ hb₂ haTop₁
      hCh₁ hCl₁ hPDE₂ hforce₂ hWU hWW₃
  have hWp (x : X) : TendstoUniformlyOn W (W x) (pure x) (Icc 0 T) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    simp only [Filter.eventually_pure]
    intro t ht
    simpa only [dist_self] using hε
  have hex (x : X) := reference_exists_tendsto_forcing_successor g k hT x
    σ (tendsto_pure_nhds σ x) fref f H force W hW a b aTop₁
    (fun _ => (1 / 4 : ℝ≥0)) (fun _ => (1 / 4 : ℝ≥0))
    (tendsto_pure_nhds force x) (tendsto_pure_nhds H x)
    (tendsto_pure_nhds a x) (tendsto_pure_nhds b x) (hWp x)
    (tendsto_pure_nhds aTop₁ x) diffusion drift hdiffusion hS alpha reaction
    hcoeff (hbaseH) hgood haPhysical hWUi hPDE haTop hCh hCl
    (fun _ => by norm_num) (fun _ => by norm_num)
  choose forceFamily vFamily wFamily hforceFamily hvFamily hwFamily hprojectFamily
    hpinFamily _ _ _ _ using hex
  let Fn := fun x => forceFamily x x
  let Wn := fun x => wFamily x x
  have hFn (x : X) : (scalarSobolevPiInclusion (ι := Fin n) g
      (Nat.cast_le.mpr (by omega : k + 2 ≤ k + 3) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))).compLpL
      2 (timeMeasure T) (Fn x) = force x := hforceFamily x x
  have hWn (x : X) : ∀ t ∈ Icc 0 T,
      scalarSobolevPiInclusion (ι := Fin n) g
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2) (Wn x t) = W x t :=
    hprojectFamily x x
  have hWnCont (x : X) : ContinuousOn (Wn x) (Icc 0 T) := hwFamily x x
  have hWnPin (x : X) : Wn x =ᵐ[timeMeasure T] fun t =>
      scalarSobolevPiInclusion (ι := Fin n) g
      (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
        (maximalRegularityDuhamelVectorField hT 0 (Fn x) t) := by
    simpa only [Fn, Wn, scalarSobolevPiInclusion, hvFamily x x] using hpinFamily x x
  have haLim (x₀ : X) (hx₀ : x₀ ∈ D) : Tendsto a (𝓝[D] x₀) (𝓝 (a x₀)) :=
    (hAB x₀ hx₀).fst_nhds
  have hbLim (x₀ : X) (hx₀ : x₀ ∈ D) : Tendsto b (𝓝[D] x₀) (𝓝 (b x₀)) :=
    (hAB x₀ hx₀).snd_nhds
  have hlimits (x₀ : X) (hx₀ : x₀ ∈ D) := reference_selected_forcing_successor
    (X := X) (n := n) (l := 𝓝[D] x₀) (T := T)
    g k hT x₀ σ (hσ x₀ hx₀) fref f H force W Fn Wn hW a b aTop₁
    (fun _ => (1 / 4 : ℝ≥0)) (fun _ => (1 / 4 : ℝ≥0))
    (hforceCont x₀ hx₀) (hHcont x₀ hx₀)
    (haLim x₀ hx₀) (hbLim x₀ hx₀)
    (hWlim x₀ hx₀) (haTop₁cont x₀ hx₀) diffusion drift hdiffusion hS alpha reaction
    hcoeff (hbaseH) hgood haPhysical hWUi hPDE haTop hCh hCl
    (fun _ => by norm_num) (fun _ => by norm_num) hFn hWn
  let E := circleHsPiInclusion g (Fin n)
    (by push_cast; linarith : ((k + 1 + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
  let Wnext := fun x t => E (Wn x t)
  refine ⟨Fn, Wnext, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    let Q := circleHsPiInclusion g (Fin n)
      (by exact_mod_cast (show 2 ≤ k + 1 + 2 by omega) :
        ((2 : ℕ) : ℝ) ≤ ((k + 1 + 2 : ℕ) : ℝ))
    let R := circleHsPiInclusion g (Fin n)
      (by exact_mod_cast (show 2 ≤ k + 2 by omega) :
        ((2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    let JV := scalarSobolevPiInclusion (ι := Fin n) g
      (Nat.cast_le.mpr (by omega : k + 2 ≤ k + 3) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    have hJae := JV.coeFn_compLpL (p := 2) (μ := timeMeasure T) (Fn x)
    rw [hFn x] at hJae
    have hRae := R.coeFn_compLpL (p := 2) (μ := timeMeasure T) (force x)
    rw [hforce₂ x] at hRae
    apply Lp.ext
    filter_upwards [Q.coeFn_compLpL (Fn x), hJae, hRae] with t hqt hjt hrt
    rw [hqt, hrt, hjt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  · intro x
    exact E.continuous.comp_continuousOn (hWnCont x)
  · intro x
    filter_upwards [hWnPin x] with t ht
    change E (Wn x t) = _
    rw [ht]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  · intro x t ht
    rw [← hWW₃ x t ht, ← hWn x t ht]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  · intro x₀ hx₀
    exact (hlimits x₀ hx₀).2.2.2.1
  · intro x₀ hx₀
    exact E.uniformContinuous.comp_tendstoUniformlyOn (hlimits x₀ hx₀).2.2.2.2.2

end DifferentialGeometry.Analysis.Parabolic

end


noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev QuasiLinear MaximalRegularity
open AddCircle

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace

private theorem reference_exists_continuousOn_sobolev_forcing_family_timeShift
    {X : Type*} [TopologicalSpace X] {n : ℕ} {D : Set X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (σ : X → ℝ) (hσ : ContinuousOn σ D)
    (fref : CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (initial : ∀ k : ℕ, X → CircleHsPi g (Fin n) (((k + 2 : ℕ) : ℝ) + 2))
    (hinitial : ∀ k, ContinuousOn (initial k) D)
    (diffusion : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (drift : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hdiffusion : ContDiffOn ℝ ∞ diffusion S)
    (hdrift : ContDiffOn ℝ ∞ drift S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin n) 1)
    (F₂ : X → timeL2 (CircleHsPi g (Fin n) ((2 : ℕ) : ℝ)) T)
    (hF₂ : ContinuousOn F₂ D)
    (W₂ : X → ℝ → CircleHsPi g (Fin n) (((1 : ℕ) : ℝ) + 1))
    (W₃ : X → ℝ → CircleHsPi g (Fin n) ((3 : ℕ) : ℝ))
    (hW₃ : ∀ x, ContinuousOn (W₃ x) (Icc 0 T))
    (hW₃lim : ∀ x₀ ∈ D, TendstoUniformlyOn W₃ (W₃ x₀) (𝓝[D] x₀) (Icc 0 T))
    (a₂ : X → timeL2 (TensorHs g 0 0 ((2 : ℕ) : ℝ)) T)
    (b₂ : X → timeL2 (CircleHsPi g (Fin n) ((2 : ℕ) : ℝ)) T)
    (aTop₁ : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (haTop₁cont : ContinuousOn aTop₁ D) :
    let K₀ := circleHsPiInclusion g (Fin n)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P₀ := (circleFirstJet (ι := Fin n) g).comp K₀
    let J₀ := (circleFirstJet (ι := Fin n) g).comp (circleHsPiCongr g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let A₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ))
    let E₁ := tensorHsCongrL g 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    referenceCircleSymmetricCoefficientFacts g fref P₀ J₀ diffusion drift S δ ρ alpha reaction →
    (∀ k x, circleHsPiInclusion g (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ) + 2) (initial k x) = (f x).val) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W₂ x t‖ ≤ ρ) →
    (∀ x t, t ∈ Icc 0 T → circleHsPiInclusion g (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((3 : ℕ) : ℝ)) (W₃ x t) = W₂ x t) →
    (∀ x, W₃ x =ᵐ[timeMeasure T] fun t => circleHsPiInclusion g (Fin n)
      (by norm_num : ((3 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ) + 2)
        (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t)) →
    (∀ x, (fun t => A₂ (a₂ x t)) =ᵐ[timeMeasure T]
      (fun t => alpha (f x) (σ x + t) (W₂ x t))) →
    (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ x t))
      =ᵐ[timeMeasure T] (fun t => reaction (f x) (σ x + t) (W₂ x t))) →
    (∀ x, aTop₁ x =ᵐ[timeMeasure T] fun t => E₁ (alpha (f x) (σ x + t) (W₂ x t))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := Fin n) g (aTop₁ x t)‖ ≤ (1 / 4 : ℝ)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := Fin n) g (aTop₁ x t)‖ ≤ (1 / 4 : ℝ)) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
        scalarHsMul g 2 (by norm_num) (a₂ x t)
          (parameterSecondDerivativeHs g 2
            (initial 0 x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + b₂ x t i) →
    ∀ k : ℕ, ∃ (force : X → timeL2 (CircleHsPi g (Fin n) ((k + 2 : ℕ) : ℝ)) T)
      (W : X → ℝ → CircleHsPi g (Fin n) ((k + 3 : ℕ) : ℝ)),
      (∀ x, (circleHsPiInclusion g (Fin n)
        (by exact_mod_cast (show 2 ≤ k + 2 by omega) :
          ((2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) (force x) = F₂ x) ∧
      (∀ x, ContinuousOn (W x) (Icc 0 T)) ∧
      (∀ x, W x =ᵐ[timeMeasure T] fun t => circleHsPiInclusion g (Fin n)
        (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
          (maximalRegularityDuhamelVectorField hT 0 (force x) t)) ∧
      (∀ x t, t ∈ Icc 0 T → circleHsPiInclusion g (Fin n)
        (by exact_mod_cast (show 3 ≤ k + 3 by omega) :
          ((3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)) (W x t) = W₃ x t) ∧
      ContinuousOn force D ∧
      ∀ x₀ ∈ D, TendstoUniformlyOn W (W x₀) (𝓝[D] x₀) (Icc 0 T) := by
  classical
  intro K₀ P₀ J₀ A₂ E₁ hcoeff hbase htime hW₃₂ hW₃ae ha₂ hb₂ haTop₁ hCh₁ hCl₁ hPDE₂ k
  induction k with
  | zero =>
    refine ⟨F₂, W₃, ?_, hW₃, hW₃ae, ?_, hF₂, hW₃lim⟩
    · intro x
      apply Lp.ext
      filter_upwards [(circleHsPiInclusion g (Fin n)
        (by norm_num : ((2 : ℕ) : ℝ) ≤ ((0 + 2 : ℕ) : ℝ))).coeFn_compLpL
          (p := 2) (μ := timeMeasure T) (F₂ x)] with t ht
      rw [ht]
      apply PiLp.ext
      intro i
      exact tensorHsInclusion_refl_apply _
    · intro x t ht
      apply PiLp.ext
      intro i
      exact tensorHsInclusion_refl_apply _
  | succ k hk =>
    obtain ⟨force, W, hforce₂, hW, hWU, hWW₃, hforceCont, hWlim⟩ := hk
    exact reference_exists_continuousOn_sobolev_forcing_successor_timeShift
      g k hT σ hσ fref f (initial 0) (initial (k + 1)) (hinitial (k + 1))
      diffusion drift hdiffusion hdrift hS alpha reaction F₂ W₂ W₃ a₂ b₂
      aTop₁ haTop₁cont force W hforceCont hW hWlim
      hcoeff (hbase (k + 1)) (hbase 0) htime hW₃₂ ha₂ hb₂ haTop₁
      hCh₁ hCl₁ hPDE₂ hforce₂ hWU hWW₃

end DifferentialGeometry.Analysis.Parabolic

end
