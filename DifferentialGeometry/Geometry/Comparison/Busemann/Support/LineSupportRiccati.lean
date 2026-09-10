import DifferentialGeometry.Geometry.Comparison.Busemann.Support.DistanceEikonal
import DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.CoordinateFormula
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Analysis.Elliptic.Lichnerowicz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set MeasureTheory
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Local

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
private theorem gradient_germ (g : SmoothRiemannianMetric I M)
    {f F : M → ℝ} {x : M} (h : F =ᶠ[𝓝 x] f) :
    gradientFun (I := I) g F x = gradientFun (I := I) g f x := by
  unfold gradientFun mvfderiv
  rw [h.mfderiv_eq, h.eq_of_nhds]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
private theorem hessian_norm_germ (g : SmoothRiemannianMetric I M)
    {f F : M → ℝ} {x : M} (h : F =ᶠ[𝓝 x] f) :
    chartHessFrobeniusSq (I := I) g F x = chartHessFrobeniusSq (I := I) g f x := by
  have hB := hessFun_congr (I := I) g h
  have hc (i j : Fin (Module.finrank ℝ E)) :
      chartHessianTensor (I := I) g x F i j x = chartHessianTensor (I := I) g x f i j x := by
    rw [← hessFun_basis_apply (I := I) g F x i j,
      ← hessFun_basis_apply (I := I) g f x i j, hB]
  simp only [chartHessFrobeniusSq_def, hc]

omit [NeZero (Module.finrank ℝ E)] in
private theorem laplacian_germ (g : SmoothRiemannianMetric I M)
    {f F : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F)
    {x : M} (hx : x ∈ U) (h : F =ᶠ[𝓝 x] f) :
    ΔG (I := I) g ⟨F, hF⟩ =ᶠ[𝓝 x]
      laplacian (I := I) (LeviCivita (I := I) g) g f := by
  filter_upwards [hU.mem_nhds hx, h.eventuallyEq_nhds] with y hy heq
  rw [← laplacian_levi_eq (I := I) g hF]
  exact laplacian_congr_of_eventuallyEq (I := I) _ g hF.contMDiffAt
    ((hf y hy).contMDiffAt (hU.mem_nhds hy)) heq

omit [NeZero (Module.finrank ℝ E)] in
private theorem laplacian_smooth_at_on (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (laplacian (I := I) (LeviCivita (I := I) g) g f) x := by
  obtain ⟨F, hF, hFf⟩ := DifferentialGeometry.exists_smooth_germ (I := I) hU hx hf
  exact (Δ_g_contMDiff (I := I) g ⟨F, hF⟩).contMDiffAt.congr_of_eventuallyEq
    (laplacian_germ g hU hf hF hx hFf).symm

private theorem hessian_norm_continuous_at_on (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U) :
    ContinuousAt (fun y => chartHessFrobeniusSq (I := I) g f y) x := by
  obtain ⟨F, hF, hFf⟩ := DifferentialGeometry.exists_smooth_germ (I := I) hU hx hf
  apply (DifferentialGeometry.Analysis.Laplacian.chartHessFrobeniusSq_continuous
    (I := I) g hF).continuousAt.congr
  filter_upwards [hFf.eventuallyEq_nhds] with y hy
  exact hessian_norm_germ g hy

private theorem hessian_norm_nonneg_on (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U) :
    0 ≤ chartHessFrobeniusSq (I := I) g f x := by
  obtain ⟨F, hF, hFf⟩ := DifferentialGeometry.exists_smooth_germ (I := I) hU hx hf
  rw [← hessian_norm_germ g hFf]
  exact chartHessFrobeniusSq_nonneg (I := I) g hF x

theorem bochner_eikonal_on (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hunit : ∀ y ∈ U, g.inner y (gradientFun (I := I) g f y)
      (gradientFun (I := I) g f y) = 1) {x : M} (hx : x ∈ U) :
    chartHessFrobeniusSq (I := I) g f x +
      ricciTensor (I := I) g x (gradientFun (I := I) g f x) (gradientFun (I := I) g f x) +
      g.inner x (gradientFun (I := I) g f x)
        (gradientFun (I := I) g (laplacian (I := I) (LeviCivita (I := I) g) g f) x) = 0 := by
  obtain ⟨F, hF, hFf⟩ := DifferentialGeometry.exists_smooth_germ (I := I) hU hx hf
  have hnorm : normGradSqFun (I := I) g F =ᶠ[𝓝 x] fun _ : M => (1 : ℝ) := by
    filter_upwards [hU.mem_nhds hx, hFf.eventuallyEq_nhds] with y hy heq
    change g.inner y (gradientFun (I := I) g F y) (gradientFun (I := I) g F y) = 1
    rw [gradient_germ g heq]
    exact hunit y hy
  have hnormSmooth := normGradSqFun_contMDiff (I := I) g hF
  have hzero : ΔG (I := I) g ⟨normGradSqFun (I := I) g F, hnormSmooth⟩ x = 0 := by
    rw [← laplacian_levi_eq (I := I) g hnormSmooth,
      laplacian_congr_of_eventuallyEq (I := I) _ g hnormSmooth.contMDiffAt
        contMDiffAt_const hnorm, laplacian_const]
  have h := bochner_pointwise_half_grad_normSq_of_boundaryless (I := I) g hF x
  change (1 / 2 : ℝ) * ΔG (I := I) g ⟨normGradSqFun (I := I) g F, hnormSmooth⟩ x =
    chartHessFrobeniusSq (I := I) g F x +
      ricciTensor (I := I) g x (gradientFun (I := I) g F x) (gradientFun (I := I) g F x) +
      g.inner x (gradientFun (I := I) g F x)
        (gradientFun (I := I) g (ΔG (I := I) g ⟨F, hF⟩) x) at h
  rw [hzero, mul_zero, gradient_germ g hFf, hessian_norm_germ g hFf,
    gradient_germ g (laplacian_germ g hU hf hF hx hFf)] at h
  exact h.symm

end Local

section Line

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem hasDerivAt_lineDistanceSupport_laplacian
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s R : ℝ) (hR : s < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    HasDerivAt
      (fun t => laplacian (I := I) (LeviCivita (I := I) g) g (lineDistanceSupport eta R) (eta t))
      (-chartHessFrobeniusSq (I := I) g (lineDistanceSupport eta R) (eta s) -
        ricciTensor (I := I) g (eta s) (curveVelocity (I := I) eta s)
          (curveVelocity (I := I) eta s)) s := by
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  let f := lineDistanceSupport eta R
  let m := laplacian (I := I) (LeviCivita (I := I) g) g f
  obtain ⟨U, hU, hx, hf, hunit⟩ := exists_open_lineDistanceSupport_eikonal (I := I)
    g hEnorm p u hu hiso s R hR
  have hm : MDifferentiableAt I 𝓘(ℝ, ℝ) m (eta s) :=
    (laplacian_smooth_at_on g hU hf hx).mdifferentiableAt (by simp)
  have heta : MDifferentiableAt 𝓘(ℝ, ℝ) I eta s :=
    (intrinsicGeodesic_contMDiff (I := I) g hEnorm p u).contMDiffAt.mdifferentiableAt (by simp)
  have hder := hasDerivAt_comp_mfderiv_along I m eta s hm heta
  change HasDerivAt (fun t => m (eta t))
    (mfderiv I 𝓘(ℝ, ℝ) m (eta s) (curveVelocity (I := I) eta s)) s at hder
  have hb := bochner_eikonal_on g hU hf hunit hx
  have hgrad := gradient_lineDistanceSupport_on_line (I := I) g hEnorm p u hu hiso s R hR
  dsimp only at hgrad
  rw [hgrad] at hb
  have hinner : g.inner (eta s) (curveVelocity (I := I) eta s)
      (gradientFun (I := I) g m (eta s)) =
        mfderiv I 𝓘(ℝ, ℝ) m (eta s) (curveVelocity (I := I) eta s) :=
    inner_gradFun_right (I := I) g m (eta s) (curveVelocity (I := I) eta s)
  change chartHessFrobeniusSq (I := I) g f (eta s) +
    ricciTensor (I := I) g (eta s) (curveVelocity (I := I) eta s) (curveVelocity (I := I) eta s) +
    g.inner (eta s) (curveVelocity (I := I) eta s) (gradientFun (I := I) g m (eta s)) = 0 at hb
  rw [hinner] at hb
  have heq : @Eq ℝ (mfderiv I 𝓘(ℝ, ℝ) m (eta s) (curveVelocity (I := I) eta s))
      (-chartHessFrobeniusSq (I := I) g f (eta s) -
        ricciTensor (I := I) g (eta s) (curveVelocity (I := I) eta s)
          (curveVelocity (I := I) eta s)) := by
    have h := eq_neg_of_add_eq_zero_right hb
    simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using h
  rw [heq] at hder
  exact hder

theorem continuousOn_lineDistanceSupport_hessianNorm
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (R : ℝ) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    ContinuousOn (fun s => chartHessFrobeniusSq (I := I) g
      (lineDistanceSupport eta R) (eta s)) (Iio R) := by
  intro eta s hs
  obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
    g hEnorm p u hu hiso s R hs
  exact ((hessian_norm_continuous_at_on g hU hf hx).comp
    hiso.continuous.continuousAt).continuousWithinAt

theorem lineDistanceSupport_hessianNorm_nonneg
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s R : ℝ) (hR : s < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    0 ≤ chartHessFrobeniusSq (I := I) g (lineDistanceSupport eta R) (eta s) := by
  obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
    g hEnorm p u hu hiso s R hR
  exact hessian_norm_nonneg_on g hU hf hx

theorem integral_lineDistanceSupport_hessianNorm_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (a b R : ℝ) (hab : a ≤ b) (hbR : b < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    (∫ s in a..b, chartHessFrobeniusSq (I := I) g (lineDistanceSupport eta R) (eta s)) ≤
      laplacian (I := I) (LeviCivita (I := I) g) g (lineDistanceSupport eta R) (eta a) -
      laplacian (I := I) (LeviCivita (I := I) g) g (lineDistanceSupport eta R) (eta b) := by
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  let m := fun s => laplacian (I := I) (LeviCivita (I := I) g) g
    (lineDistanceSupport eta R) (eta s)
  let N := fun s => chartHessFrobeniusSq (I := I) g (lineDistanceSupport eta R) (eta s)
  let Q := fun s => ricciTensor (I := I) g (eta s) (curveVelocity (I := I) eta s)
    (curveVelocity (I := I) eta s)
  have hd (s : ℝ) (hs : s < R) : HasDerivAt m (-N s - Q s) s :=
    hasDerivAt_lineDistanceSupport_laplacian (I := I) g hEnorm p u hu hiso s R hs
  have hc : ContinuousOn (fun s => -m s) (Icc a b) := by
    intro s hs
    exact (hd s (hs.2.trans_lt hbR)).neg.continuousAt.continuousWithinAt
  have hint : IntegrableOn N (Icc a b) :=
    ((continuousOn_lineDistanceSupport_hessianNorm (I := I) g hEnorm p u hu hiso R).mono
      (fun _ hs => hs.2.trans_lt hbR)).integrableOn_Icc
  have hle := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
    (g := fun s => -m s) (g' := fun s => N s + Q s) (φ := N) hab hc
    (fun s hs => by
      simpa only [hasDerivWithinAt_iff_isLittleO, Pi.neg_apply, neg_sub, neg_neg,
        sub_neg_eq_add, add_comm, smul_eq_mul] using
        (hd s (hs.2.trans hbR)).neg.hasDerivWithinAt (s := Ioi s))
    hint (fun s _ => le_add_of_nonneg_right (hRic (eta s) (curveVelocity (I := I) eta s)))
  change (∫ s in a..b, N s) ≤ m a - m b
  simpa only [neg_sub_neg] using hle

end Line

end DifferentialGeometry.Geometry.Topology

end
