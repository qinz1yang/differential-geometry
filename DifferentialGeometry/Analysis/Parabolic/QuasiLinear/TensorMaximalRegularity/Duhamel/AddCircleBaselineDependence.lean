import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedBaseline
import DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpOperators

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def parameterDerivativeBaselineCoefficientL
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)) →L[ℝ]
      TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
  let D := parameterDerivativeHs g 1
  let Q := K.comp (parameterSecondDerivativeHs g 2)
  let m := scalarHsMul g 1 (by norm_num)
  ContinuousLinearMap.flip
    ((ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι =>
        ((D.comp Q).precomp _).comp (m.comp J) +
          ((J.comp Q).precomp _).comp (m.comp D)))

theorem tendsto_parameterDerivativeBaselineForcingLp
    {Ω X ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (f0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a : X → Lp (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) p μ)
    (a0 : Lp (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) p μ)
    (b : X → Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) p μ)
    (b0 : Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) p μ)
    (hf : Tendsto f l (𝓝 f0)) (ha : Tendsto a l (𝓝 a0)) (hb : Tendsto b l (𝓝 b0)) :
    Tendsto (fun x => parameterDerivativeBaselineForcingLp g (f x) (a x) (b x)) l
      (𝓝 (parameterDerivativeBaselineForcingLp g f0 a0 b0)) := by
  let A := parameterDerivativeBaselineCoefficientL (ι := ι) g
  let D := ContinuousLinearMap.piLpMap 2 (fun _ : ι => parameterDerivativeHs g 1)
  have heq (f' : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
      (a' : Lp (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) p μ)
      (b' : Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) p μ) :
      parameterDerivativeBaselineForcingLp g f' a' b' =
        A.compLpL₂ p μ f' a' + D.compLpL p μ b' := by
    apply Lp.ext
    filter_upwards [parameterDerivativeBaselineForcingLp_ae g f' a' b',
      Lp.coeFn_add (A.compLpL₂ p μ f' a') (D.compLpL p μ b'),
      (A f').coeFn_compLp a', D.coeFn_compLpL b'] with t ht hadd hA hD
    change A.compLpL₂ p μ f' a' t = A f' (a' t) at hA
    rw [ht, hadd, Pi.add_apply, hA, hD]
    apply PiLp.ext
    intro i
    rfl
  have hA := ((A.compLpL₂ p μ).continuous₂.tendsto _).comp (hf.prodMk_nhds ha)
  have hD := (D.compLpL p μ).continuous.tendsto b0 |>.comp hb
  have h := hA.add hD
  change Tendsto (fun x => A.compLpL₂ p μ (f x) (a x) + D.compLpL p μ (b x)) l
    (𝓝 (A.compLpL₂ p μ f0 a0 + D.compLpL p μ b0)) at h
  simpa only [heq] using h

end AddCircle

end
