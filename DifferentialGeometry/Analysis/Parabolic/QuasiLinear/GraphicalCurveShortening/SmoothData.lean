import DifferentialGeometry.Geometry.Metric.AddCircle
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.LocalExistence
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.ExponentCongruence
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
namespace DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.L2
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem graph_initial_derivative_eval
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : ι → C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯)
    (i : ι) (x : AddCircle (1 : ℝ)) :
    let f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) :=
      WithLp.toLp 2 (fun j => ccTensorToHs g 0 (((1 : ℕ) : ℝ) + 2) (scalarCc g (F j)))
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    scalarH1ToContinuous g
      (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
        (AddCircle.parameterDerivativeHsPi g 1 (J f₀) i)) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (F i) x (AddCircle.parameterTangent x) := by
  intro f₀ J
  have hf₀ : J f₀ = WithLp.toLp 2 (fun j =>
      ccTensorToHs g 0 (((1 : ℕ) : ℝ) + 1) (scalarCc g (F j))) := by
    apply PiLp.ext
    intro j
    exact tensorHsInclusion_ccTensorToHs g 0 (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) (scalarCc g (F j))
  rw [hf₀, AddCircle.parameterDerivativeHsPi_apply_ccTensorToHs]
  have hc {a b : ℝ} (hab : a = b) (S : SmoothCcTensor g 0 0) :
      tensorHsCongrL g 0 0 hab (ccTensorToHs g 0 a S) = ccTensorToHs g 0 b S := by
    cases hab
    rfl
  change scalarH1ToContinuous g
    (tensorHsCongrL g 0 0 _ (ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (AddCircle.parameterDerivativeCcTensor g (scalarCc g (F i))))) x = _
  rw [hc, scalarH1ToContinuous_apply_ccTensorToHs,
    AddCircle.scalar0_parameterDerivativeCcTensor, scalar0_scalarCc]


private theorem mfderiv_coordinate_apply
    {ι : Type*} [Fintype ι]
    (F : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, EuclideanSpace ℝ ι), EuclideanSpace ℝ ι⟯)
    (i : ι) (x : AddCircle (1 : ℝ)) (v : TangentSpace 𝓘(ℝ, ℝ) x) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => F z i) x v =
      (show EuclideanSpace ℝ ι from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ ι) F x v).ofLp i := by
  let L : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι => ℝ) i
  have hL : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ ι) 𝓘(ℝ, ℝ) L :=
    (L.contDiff (n := ∞)).contMDiff.mdifferentiable (by decide)
  have h := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, EuclideanSpace ℝ ι))
    (I'' := 𝓘(ℝ, ℝ)) (f := F) (g := L) x
    (hL (F x)) (F.contMDiff.mdifferentiableAt (by decide))
  rw [mfderiv_eq_fderiv, L.fderiv] at h
  exact congrArg (fun A => A v) h


private theorem exists_graphical_curve_shortening_coordinates
    {ι : Type*} [Fintype ι]
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, EuclideanSpace ℝ ι), EuclideanSpace ℝ ι⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ f : ℝ → ℝ → ι → ℝ,
      (∀ x, f 0 x = (F₀ (x : AddCircle (1 : ℝ))).ofLp) ∧
      (∀ t, Function.Periodic (f t) 1) ∧
      (∀ x, ContinuousOn (fun t => f t x) (Icc 0 T)) ∧
      ∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x,
        HasDerivAt (fun s => f s x)
          (graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f t) x)) •
            deriv (deriv (f t)) x) t := by
  let g := AddCircle.graphMetric F₀
  let φ : ι → C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ := fun i =>
    ⟨fun z => F₀ z i,
      ((PiLp.proj 2 (fun _ : ι => ℝ) i).contDiff.contMDiff).comp F₀.contMDiff⟩
  let f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) :=
    WithLp.toLp 2 (fun i => ccTensorToHs g 0 (((1 : ℕ) : ℝ) + 2) (scalarCc g (φ i)))
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
  let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
  let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  have hslope (x : AddCircle (1 : ℝ)) :
      WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀) i)) x) =
      (show EuclideanSpace ℝ ι from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ ι) F₀ x (AddCircle.parameterTangent x)) := by
    apply PiLp.ext
    intro i
    exact (graph_initial_derivative_eval g φ i x).trans
      (mfderiv_coordinate_apply F₀ i x _)
  have hg (x : AddCircle (1 : ℝ)) : AddCircle.metricCoefficient g x =
      1 + ‖WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀) i)) x)‖ ^ 2 := by
    rw [hslope]
    exact congrArg (fun a => a x) (AddCircle.metricCoefficient_graphMetric F₀)
  obtain ⟨T, hT, u, htrace, hinit, hperiod, hpde⟩ :=
    exists_graphical_curve_shortening_sobolev_solution_of_metric_coefficient g f₀ hg
  let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u.toFun t))
    (x : AddCircle (1 : ℝ))
  refine ⟨T, hT, f, ?_, hperiod, ?_, hpde⟩
  · intro x
    have hi : f 0 x = scalarH1PiToContinuous g (C (K f₀)) (x : AddCircle (1 : ℝ)) := hinit x
    rw [hi]
    funext i
    change scalarH1ToContinuous g
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
        (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
          (ccTensorToHs g 0 (((1 : ℕ) : ℝ) + 2) (scalarCc g (φ i))))) _ = _
    rw [tensorHsInclusion_ccTensorToHs, tensorHsInclusion_ccTensorToHs,
      scalarH1ToContinuous_apply_ccTensorToHs, scalar0_scalarCc]
    rfl
  · intro x
    let L := (ContinuousMap.evalCLM ℝ (x : AddCircle (1 : ℝ))).comp
      ((scalarH1PiToContinuous g).comp C)
    exact L.continuous.comp_continuousOn (continuousOn_const.add u.continuousOn_toFun)

private theorem deriv_toLp
    {ι : Type*} [Finite ι] (f : ℝ → ι → ℝ) :
    deriv (fun x => (WithLp.toLp 2 (f x) : EuclideanSpace ℝ ι)) =
      fun x => WithLp.toLp 2 (deriv f x) := by
  let := Fintype.ofFinite ι
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  funext x
  change (fderiv ℝ (e ∘ f) x) 1 = e ((fderiv ℝ f x) 1)
  rw [e.comp_fderiv]
  rfl

private theorem hasDerivAt_graphical_curve_shortening_toLp
    {ι : Type*} [Fintype ι] (f : ℝ → ℝ → ι → ℝ) {t : ℝ}
    (hf : ContDiff ℝ 2 (f t))
    (ht : ∀ x, HasDerivAt (fun s => f s x)
      (graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f t) x)) •
        deriv (deriv (f t)) x) t) :
    let F : ℝ → ℝ → EuclideanSpace ℝ ι := fun s x => WithLp.toLp 2 (f s x)
    ContDiff ℝ 2 (F t) ∧ ∀ x,
      HasDerivAt (fun s => F s x)
        (graphDiffusionCoefficient (deriv (F t) x) •
          deriv (deriv (F t)) x) t := by
  intro F
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  have hfirst : deriv (F t) = fun x => WithLp.toLp 2 (deriv (f t) x) :=
    deriv_toLp (f t)
  have hsecond : deriv (deriv (F t)) =
      fun x => WithLp.toLp 2 (deriv (deriv (f t)) x) := by
    rw [hfirst]
    exact deriv_toLp (deriv (f t))
  refine ⟨e.contDiff.comp hf, ?_⟩
  intro x
  rw [hsecond, hfirst]
  have h := (PiLp.hasFDerivAt_toLp 2 (f t x)).comp_hasDerivAt t (ht x)
  convert h using 1 <;> rfl


theorem exists_graphical_curve_shortening_ae_of_smooth
    {ι : Type*} [Fintype ι]
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, EuclideanSpace ℝ ι), EuclideanSpace ℝ ι⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ F : ℝ → ℝ → EuclideanSpace ℝ ι,
      (∀ x, F 0 x = F₀ (x : AddCircle (1 : ℝ))) ∧
      (∀ t, Function.Periodic (F t) 1) ∧
      (∀ x, ContinuousOn (fun t => F t x) (Icc 0 T)) ∧
      ∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (F t) ∧ ∀ x,
        HasDerivAt (fun s => F s x)
          (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) t := by
  obtain ⟨T, hT, f, hinit, hperiod, hcont, hpde⟩ :=
    exists_graphical_curve_shortening_coordinates F₀
  let F : ℝ → ℝ → EuclideanSpace ℝ ι := fun t x => WithLp.toLp 2 (f t x)
  refine ⟨T, hT, F, ?_, ?_, ?_, ?_⟩
  · intro x
    change WithLp.toLp 2 (f 0 x) = F₀ (x : AddCircle (1 : ℝ))
    rw [hinit]
  · intro t x
    change WithLp.toLp 2 (f t (x + 1)) = WithLp.toLp 2 (f t x)
    rw [hperiod t x]
  · intro x
    exact (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp_continuousOn (hcont x)
  · filter_upwards [hpde] with t ht
    exact hasDerivAt_graphical_curve_shortening_toLp f ht.1 ht.2

end DifferentialGeometry.Analysis.Parabolic
