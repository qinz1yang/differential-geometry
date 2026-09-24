import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Uniqueness
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleFiniteRegularity
import DifferentialGeometry.Geometry.Metric.AddCircle
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Regularity
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.ExponentCongruence
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet

noncomputable section
open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
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


private theorem hasDerivWithinAt_of_integral_equation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {T : ℝ} (f q : ℝ → X)
    (hq : ContinuousOn q (Icc 0 T))
    (hint : ∀ t ∈ Icc 0 T, IntervalIntegrable q volume 0 t ∧
      f t = f 0 + ∫ s in 0..t, q s) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt f (q t) (Icc 0 T) t := by
  intro t ht
  let _ : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have hm : StronglyMeasurableAtFilter q (𝓝[Icc 0 T] t) volume :=
    ⟨Icc 0 T, self_mem_nhdsWithin, hq.aestronglyMeasurable measurableSet_Icc⟩
  have hd : HasDerivWithinAt (fun z => f 0 + ∫ s in 0..z, q s) (q t) (Icc 0 T) t :=
    (intervalIntegral.integral_hasDerivWithinAt_right (hint t ht).1 hm (hq t ht)).const_add _
  exact hd.congr (fun s hs => (hint s hs).2) (hint t ht).2


private theorem hasDerivWithinAt_of_joint_integral_equation
    {X Y : Type*} [TopologicalSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {T : ℝ} (f q : ℝ → X → Y) (f₀ : X → Y)
    (hinit : ∀ x, f 0 x = f₀ x)
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hint : ∀ x t, t ∈ Icc 0 T → IntervalIntegrable (fun s => q s x) volume 0 t ∧
      f t x = f₀ x + ∫ s in 0..t, q s x) :
    ∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun s => f s x) (q t x) (Icc 0 T) t := by
  intro t ht x
  have hslice : ContinuousOn (fun s => q s x) (Icc 0 T) :=
    hq.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hs => ⟨hs, mem_univ _⟩)
  apply hasDerivWithinAt_of_integral_equation (fun s => f s x) (fun s => q s x) hslice _ t ht
  intro s hs
  obtain ⟨hi, heq⟩ := hint x s hs
  refine ⟨hi, ?_⟩
  rw [hinit]
  exact heq

private theorem integral_eq_of_timeH1_ae_derivative
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {T : ℝ} (hT : 0 < T) (u : timeH1 X T) (L : X →L[ℝ] Y) (v : X)
    (q : ℝ → Y)
    (hq : ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (fun s => L (v + u.toFun s)) (q t) t) :
    ∀ t ∈ Icc 0 T, IntervalIntegrable q volume 0 t ∧
      L (v + u.toFun t) = L (v + u.toFun 0) + ∫ s in 0..t, q s := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo 0 T := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hrep : q =ᵐ[timeMeasure T] fun s => L (u.deriv s) := by
    filter_upwards [hq, u.ae_hasDerivWithinAt_toFun, hmem] with t hqt hut ht
    exact hqt.unique (L.hasFDerivAt.comp_hasDerivAt t
      ((hut.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).const_add v))
  intro t ht
  have hd := u.intervalIntegrable_deriv (show 0 ∈ Icc 0 T from ⟨le_rfl, hT.le⟩) ht
  have hsub : uIoc 0 t ⊆ Icc 0 T := by
    rw [uIoc_of_le ht.1]
    exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2)
  have hae : q =ᵐ[volume.restrict (uIoc 0 t)] fun s => L (u.deriv s) :=
    hrep.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hi : IntervalIntegrable (fun s => L (u.deriv s)) volume 0 t :=
    ⟨L.integrable_comp hd.1, L.integrable_comp hd.2⟩
  refine ⟨hi.congr_ae hae.symm, ?_⟩
  rw [intervalIntegral.integral_congr_ae (ae_imp_of_ae_restrict hae),
    L.intervalIntegral_comp_comm hd]
  have hu := u.toFun_sub_toFun (show 0 ∈ Icc 0 T from ⟨le_rfl, hT.le⟩) ht
  rw [← hu, map_sub, map_add, map_add]
  abel


private theorem continuousOn_iteratedDeriv_of_circle_h3_representative
    {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (u : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (W : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    {s : Set X} (hW : ContinuousOn W s)
    (n : ℕ) (hn : n ≤ 2) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    (∀ t ∈ s, K (W t) = u t) →
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u t))
      (x : AddCircle (1 : ℝ))
    ContinuousOn (fun p : X × ℝ => iteratedDeriv n (f p.1) p.2) (s ×ˢ univ) := by
  intro K C hWu f
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have h : (n : ℝ) ≤ 2 := by exact_mod_cast hn
          norm_num only [Nat.cast_one]
          linarith : (n : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
  have hhigh : ContinuousOn (fun t => P (f₀ + W t)) s :=
    P.continuous.comp_continuousOn (continuousOn_const.add hW)
  have hlow : ∀ t ∈ s,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1)) (P (f₀ + W t)) =
        C (K f₀ + u t) := by
    intro t ht
    rw [← hWu t ht, ← map_add]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact (AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
    g n (fun t => C (K f₀ + u t)) (fun t => P (f₀ + W t)) hhigh hlow).2

private theorem graphical_rhs_continuousOn_of_circle_h3_representative
    {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (u : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (W : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    {s : Set X} (hW : ContinuousOn W s) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    (∀ t ∈ s, K (W t) = u t) →
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u t))
      (x : AddCircle (1 : ℝ))
    ContinuousOn (fun p : X × ℝ => deriv (f p.1) p.2) (s ×ˢ univ) ∧
    ContinuousOn (fun p : X × ℝ => deriv (deriv (f p.1)) p.2) (s ×ˢ univ) ∧
    ContinuousOn (fun p : X × ℝ =>
      graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f p.1) p.2)) •
        deriv (deriv (f p.1)) p.2) (s ×ˢ univ) := by
  intro K C hWu f
  have hfirst : ContinuousOn (fun p : X × ℝ => deriv (f p.1) p.2) (s ×ˢ univ) := by
    simpa only [iteratedDeriv_one] using
      continuousOn_iteratedDeriv_of_circle_h3_representative g f₀ u W hW 1 (by norm_num) hWu
  have hsecond : ContinuousOn (fun p : X × ℝ => deriv (deriv (f p.1)) p.2) (s ×ˢ univ) := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      continuousOn_iteratedDeriv_of_circle_h3_representative g f₀ u W hW 2 (by norm_num) hWu
  refine ⟨hfirst, hsecond, ?_⟩
  have hslope : ContinuousOn
      (fun p : X × ℝ => (WithLp.toLp 2 (deriv (f p.1) p.2) : EuclideanSpace ℝ ι))
      (s ×ˢ univ) :=
    (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp_continuousOn hfirst
  exact (contDiff_graphDiffusionCoefficient.continuous.comp_continuousOn hslope).smul hsecond


private theorem exists_graphical_curve_shortening_coordinates
    {ι : Type*} [Fintype ι]
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, EuclideanSpace ℝ ι), EuclideanSpace ℝ ι⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ f : ℝ → ℝ → ι → ℝ,
      (∀ x, f 0 x = (F₀ (x : AddCircle (1 : ℝ))).ofLp) ∧
      (∀ t, Function.Periodic (f t) 1) ∧
      ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ) ∧
      (∀ x t, t ∈ Icc 0 T →
        IntervalIntegrable (fun s =>
          graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f s) x)) •
            deriv (deriv (f s)) x) volume 0 t ∧
        f t x = f 0 x + ∫ s in 0..t,
          graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f s) x)) •
            deriv (deriv (f s)) x) ∧
      (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t)) ∧
      (ContinuousOn (fun p : ℝ × ℝ => deriv (f p.1) p.2) (Icc 0 T ×ˢ univ) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f p.1)) p.2) (Icc 0 T ×ˢ univ) ∧
        ContinuousOn (fun p : ℝ × ℝ =>
          graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f p.1) p.2)) •
            deriv (deriv (f p.1)) p.2) (Icc 0 T ×ˢ univ)) ∧
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
  let f₄ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)) :=
    WithLp.toLp 2 (fun i => ccTensorToHs g 0 (((2 : ℕ) : ℝ) + 2) (scalarCc g (φ i)))
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))
  have hP : P f₄ = f₀ := by
    apply PiLp.ext
    intro i
    exact tensorHsInclusion_ccTensorToHs g 0
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2) (scalarCc g (φ i))
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
  have hg₄ (x : AddCircle (1 : ℝ)) : AddCircle.metricCoefficient g x =
      1 + ‖WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J (P f₄)) i)) x)‖ ^ 2 := by
    rw [hP]
    exact hg x
  obtain ⟨T, hT, u, force, FH, W, hu, htrace, hFH, hW, hWlow, hWfield,
      hinit, hperiod, hC2, hpdeTime⟩ :=
    exists_graphical_curve_shortening_with_continuous_h3_representative_of_metric_coefficient
      g f₄ hg₄
  change (∀ x : ℝ, scalarH1PiToContinuous g (C (K (P f₄) + u.toFun 0))
      (x : AddCircle (1 : ℝ)) = scalarH1PiToContinuous g (C (K (P f₄)))
        (x : AddCircle (1 : ℝ))) at hinit
  change (∀ t, Function.Periodic (fun x : ℝ => scalarH1PiToContinuous g
    (C (K (P f₄) + u.toFun t)) (x : AddCircle (1 : ℝ))) 1) at hperiod
  rw [hP] at hinit hperiod hC2 hpdeTime
  have hpde : ∀ᵐ t ∂timeMeasure T,
      ContDiff ℝ 2 (fun x : ℝ => scalarH1PiToContinuous g
        (C (K f₀ + u.toFun t)) (x : AddCircle (1 : ℝ))) ∧ ∀ x : ℝ,
      HasDerivAt (fun s => scalarH1PiToContinuous g (C (K f₀ + u.toFun s))
        (x : AddCircle (1 : ℝ)))
        (graphDiffusionCoefficient (WithLp.toLp 2 (deriv (fun x : ℝ =>
          scalarH1PiToContinuous g (C (K f₀ + u.toFun t)) (x : AddCircle (1 : ℝ))) x)) •
          deriv (deriv (fun x : ℝ => scalarH1PiToContinuous g
            (C (K f₀ + u.toFun t)) (x : AddCircle (1 : ℝ)))) x) t := by
    filter_upwards [hpdeTime, ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht htmem
    exact ⟨hC2 t htmem, ht⟩
  let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u.toFun t))
    (x : AddCircle (1 : ℝ))
  have hjets := graphical_rhs_continuousOn_of_circle_h3_representative
    g f₀ u.toFun W hW hWlow
  refine ⟨T, hT, f, ?_, hperiod, ?_, ?_, hC2, hjets, hpde⟩
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
  · have hstate := ((scalarH1PiToContinuous g).comp C).continuous.comp_continuousOn
      ((continuousOn_const (c := K f₀)).add u.continuousOn_toFun)
    exact (hstate.comp continuousOn_fst (fun _ h => h.1)).eval
      ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd).continuousOn
  · intro x
    let L := (ContinuousMap.evalCLM ℝ (x : AddCircle (1 : ℝ))).comp
      ((scalarH1PiToContinuous g).comp C)
    exact integral_eq_of_timeH1_ae_derivative hT u L (K f₀) _
      (hpde.mono fun t ht => ht.2 x)

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


private theorem exists_graphical_curve_shortening_integral_with_continuous_derivatives
    {ι : Type*} [Fintype ι]
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, EuclideanSpace ℝ ι), EuclideanSpace ℝ ι⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ F : ℝ → ℝ → EuclideanSpace ℝ ι,
      (∀ x, F 0 x = F₀ (x : AddCircle (1 : ℝ))) ∧
      (∀ t, Function.Periodic (F t) 1) ∧
      ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ univ) ∧
      (∀ x t, t ∈ Icc 0 T →
        IntervalIntegrable (fun s =>
          graphDiffusionCoefficient (deriv (F s) x) • deriv (deriv (F s)) x) volume 0 t ∧
        F t x = F₀ (x : AddCircle (1 : ℝ)) + ∫ s in 0..t,
          graphDiffusionCoefficient (deriv (F s) x) • deriv (deriv (F s)) x) ∧
      (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (F t)) ∧
      (ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2) (Icc 0 T ×ˢ univ) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (F p.1)) p.2) (Icc 0 T ×ˢ univ) ∧
        ContinuousOn (fun p : ℝ × ℝ =>
          graphDiffusionCoefficient (deriv (F p.1) p.2) •
            deriv (deriv (F p.1)) p.2) (Icc 0 T ×ˢ univ)) ∧
      ∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (F t) ∧ ∀ x,
        HasDerivAt (fun s => F s x)
          (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) t := by
  obtain ⟨T, hT, f, hinit, hperiod, hcont, hint, hC2, hjets, hpde⟩ :=
    exists_graphical_curve_shortening_coordinates F₀
  let F : ℝ → ℝ → EuclideanSpace ℝ ι := fun t x => WithLp.toLp 2 (f t x)
  refine ⟨T, hT, F, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change WithLp.toLp 2 (f 0 x) = F₀ (x : AddCircle (1 : ℝ))
    rw [hinit]
  · intro t x
    change WithLp.toLp 2 (f t (x + 1)) = WithLp.toLp 2 (f t x)
    rw [hperiod t x]
  · exact (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp_continuousOn hcont
  · intro x t ht
    let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap
    let q := fun s => graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f s) x)) •
      deriv (deriv (f s)) x
    have hrhs : (fun s => graphDiffusionCoefficient (deriv (F s) x) •
        deriv (deriv (F s)) x) = fun s => L (q s) := by
      funext s
      have hfirst : deriv (F s) = fun y => WithLp.toLp 2 (deriv (f s) y) :=
        deriv_toLp (f s)
      have hsecond : deriv (deriv (F s)) =
          fun y => WithLp.toLp 2 (deriv (deriv (f s)) y) := by
        rw [hfirst]
        exact deriv_toLp (deriv (f s))
      rw [hsecond, hfirst]
      rfl
    obtain ⟨hi, heq⟩ := hint x t ht
    rw [hrhs]
    refine ⟨⟨L.integrable_comp hi.1, L.integrable_comp hi.2⟩, ?_⟩
    rw [L.intervalIntegral_comp_comm hi]
    change L (f t x) = F₀ (x : AddCircle (1 : ℝ)) + L (∫ s in 0..t, q s)
    rw [heq, map_add, hinit]
    rfl
  · intro t ht
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.contDiff.comp (hC2 t ht)
  · let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
    have hfirst (t : ℝ) : deriv (F t) = fun x => WithLp.toLp 2 (deriv (f t) x) :=
      deriv_toLp (f t)
    have hsecond (t : ℝ) : deriv (deriv (F t)) =
        fun x => WithLp.toLp 2 (deriv (deriv (f t)) x) := by
      rw [hfirst]
      exact deriv_toLp (deriv (f t))
    refine ⟨?_, ?_, ?_⟩
    · apply (e.continuous.comp_continuousOn hjets.1).congr
      intro p hp
      exact congrFun (hfirst p.1) p.2
    · apply (e.continuous.comp_continuousOn hjets.2.1).congr
      intro p hp
      exact congrFun (hsecond p.1) p.2
    · apply (e.continuous.comp_continuousOn hjets.2.2).congr
      intro p hp
      dsimp only [Function.comp_apply]
      rw [hsecond, hfirst]
      rfl
  · filter_upwards [hpde] with t ht
    exact hasDerivAt_graphical_curve_shortening_toLp f ht.1 ht.2


theorem exists_graphical_curve_shortening_classical_of_smooth
    {ι : Type*} [Fintype ι]
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, EuclideanSpace ℝ ι), EuclideanSpace ℝ ι⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ F : ℝ → ℝ → EuclideanSpace ℝ ι,
      (∀ x, F 0 x = F₀ (x : AddCircle (1 : ℝ))) ∧
      (∀ t, Function.Periodic (F t) 1) ∧
      ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ univ) ∧
      (∀ x t, t ∈ Icc 0 T →
        IntervalIntegrable (fun s =>
          graphDiffusionCoefficient (deriv (F s) x) • deriv (deriv (F s)) x) volume 0 t ∧
        F t x = F₀ (x : AddCircle (1 : ℝ)) + ∫ s in 0..t,
          graphDiffusionCoefficient (deriv (F s) x) • deriv (deriv (F s)) x) ∧
      (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (F t)) ∧
      (ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2) (Icc 0 T ×ˢ univ) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (F p.1)) p.2) (Icc 0 T ×ˢ univ) ∧
        ContinuousOn (fun p : ℝ × ℝ =>
          graphDiffusionCoefficient (deriv (F p.1) p.2) •
            deriv (deriv (F p.1)) p.2) (Icc 0 T ×ˢ univ)) ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun s => F s x)
        (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) (Icc 0 T) t) ∧
      ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => F s x)
        (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) t := by
  obtain ⟨T, hT, F, hinit, hperiod, hcont, hint, hC2, hjets, _⟩ :=
    exists_graphical_curve_shortening_integral_with_continuous_derivatives F₀
  have hwithin : ∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun s => F s x)
      (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) (Icc 0 T) t :=
    hasDerivWithinAt_of_joint_integral_equation F
      (fun t x => graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x)
      (fun x => F₀ (x : AddCircle (1 : ℝ))) hinit hjets.2.2 hint
  refine ⟨T, hT, F, hinit, hperiod, hcont, hint, hC2, hjets, hwithin, ?_⟩
  intro t ht x
  exact (hwithin t ⟨ht.1.le, ht.2.le⟩ x).hasDerivAt (Icc_mem_nhds ht.1 ht.2)


theorem exists_unique_graphical_curve_shortening_classical_of_smooth
    {ι : Type*} [Fintype ι]
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, EuclideanSpace ℝ ι), EuclideanSpace ℝ ι⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ F : ℝ → ℝ → EuclideanSpace ℝ ι,
      (∀ x, F 0 x = F₀ (x : AddCircle (1 : ℝ))) ∧
      (∀ t, Function.Periodic (F t) 1) ∧
      ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ univ) ∧
      (∀ x t, t ∈ Icc 0 T →
        IntervalIntegrable (fun s =>
          graphDiffusionCoefficient (deriv (F s) x) • deriv (deriv (F s)) x) volume 0 t ∧
        F t x = F₀ (x : AddCircle (1 : ℝ)) + ∫ s in 0..t,
          graphDiffusionCoefficient (deriv (F s) x) • deriv (deriv (F s)) x) ∧
      (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (F t)) ∧
      (ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2) (Icc 0 T ×ˢ univ) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (F p.1)) p.2) (Icc 0 T ×ˢ univ) ∧
        ContinuousOn (fun p : ℝ × ℝ =>
          graphDiffusionCoefficient (deriv (F p.1) p.2) •
            deriv (deriv (F p.1)) p.2) (Icc 0 T ×ˢ univ)) ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun s => F s x)
        (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) (Icc 0 T) t) ∧
      (∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => F s x)
        (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) t) ∧
      ∀ G : ℝ → ℝ → EuclideanSpace ℝ ι,
        (∀ t ∈ Icc 0 T, Function.Periodic (G t) 1) →
        ContinuousOn (Function.uncurry G) (Icc 0 T ×ˢ Icc 0 1) →
        (∀ t ∈ Ioo 0 T, ContDiff ℝ 2 (G t)) →
        ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (G p.1)) p.2) (Icc 0 T ×ˢ Icc 0 1) →
        (∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => G s x)
          (graphDiffusionCoefficient (deriv (G t) x) • deriv (deriv (G t)) x) t) →
        (∀ x, G 0 x = F₀ (x : AddCircle (1 : ℝ))) →
        ∀ t ∈ Icc 0 T, ∀ x, G t x = F t x := by
  obtain ⟨T, hT, F, hinit, hperiod, hcont, hint, hC2, hjets, hwithin, hpde⟩ :=
    exists_graphical_curve_shortening_classical_of_smooth F₀
  refine ⟨T, hT, F, hinit, hperiod, hcont, hint, hC2, hjets, hwithin, hpde, ?_⟩
  intro G hGper hGcont hGspace hGsecond hGpde hGinit
  have hsame := graphical_curve_shortening_unique F G hT.le
    (fun t _ => hperiod t) hGper
    (hcont.mono (prod_mono Subset.rfl (subset_univ _))) hGcont
    (fun t ht => hC2 t ⟨ht.1.le, ht.2.le⟩) hGspace hpde hGpde
    (hjets.1.mono (prod_mono Subset.rfl (subset_univ _))) hGsecond
    (fun x => (hinit x).trans (hGinit x).symm)
  exact fun t ht x => (hsame t ht x).symm


theorem exists_graphical_curve_shortening_integral_with_contDiff_two_slices_of_smooth
    {ι : Type*} [Fintype ι]
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, EuclideanSpace ℝ ι), EuclideanSpace ℝ ι⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ F : ℝ → ℝ → EuclideanSpace ℝ ι,
      (∀ x, F 0 x = F₀ (x : AddCircle (1 : ℝ))) ∧
      (∀ t, Function.Periodic (F t) 1) ∧
      ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ univ) ∧
      (∀ x t, t ∈ Icc 0 T →
        IntervalIntegrable (fun s =>
          graphDiffusionCoefficient (deriv (F s) x) • deriv (deriv (F s)) x) volume 0 t ∧
        F t x = F₀ (x : AddCircle (1 : ℝ)) + ∫ s in 0..t,
          graphDiffusionCoefficient (deriv (F s) x) • deriv (deriv (F s)) x) ∧
      (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (F t)) ∧
      ∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (F t) ∧ ∀ x,
        HasDerivAt (fun s => F s x)
          (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) t := by
  obtain ⟨T, hT, F, hinit, hperiod, hcont, hint, hC2, _, _, hpde⟩ :=
    exists_graphical_curve_shortening_classical_of_smooth F₀
  refine ⟨T, hT, F, hinit, hperiod, hcont, hint, hC2, ?_⟩
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo 0 T := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem] with t ht
  exact ⟨hC2 t ⟨ht.1.le, ht.2.le⟩, hpde t ht⟩


theorem exists_graphical_curve_shortening_integral_of_smooth
    {ι : Type*} [Fintype ι]
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, EuclideanSpace ℝ ι), EuclideanSpace ℝ ι⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ F : ℝ → ℝ → EuclideanSpace ℝ ι,
      (∀ x, F 0 x = F₀ (x : AddCircle (1 : ℝ))) ∧
      (∀ t, Function.Periodic (F t) 1) ∧
      ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ univ) ∧
      (∀ x t, t ∈ Icc 0 T →
        IntervalIntegrable (fun s =>
          graphDiffusionCoefficient (deriv (F s) x) • deriv (deriv (F s)) x) volume 0 t ∧
        F t x = F₀ (x : AddCircle (1 : ℝ)) + ∫ s in 0..t,
          graphDiffusionCoefficient (deriv (F s) x) • deriv (deriv (F s)) x) ∧
      ∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (F t) ∧ ∀ x,
        HasDerivAt (fun s => F s x)
          (graphDiffusionCoefficient (deriv (F t) x) • deriv (deriv (F t)) x) t := by
  obtain ⟨T, hT, F, hinit, hperiod, hcont, hint, _, hpde⟩ :=
    exists_graphical_curve_shortening_integral_with_contDiff_two_slices_of_smooth F₀
  exact ⟨T, hT, F, hinit, hperiod, hcont, hint, hpde⟩


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
  obtain ⟨T, hT, F, hinit, hperiod, hcont, _, hpde⟩ :=
    exists_graphical_curve_shortening_integral_of_smooth F₀
  refine ⟨T, hT, F, hinit, hperiod, ?_, hpde⟩
  intro x
  exact hcont.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht, mem_univ _⟩)

end DifferentialGeometry.Analysis.Parabolic
