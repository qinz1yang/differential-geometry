import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFlowRegularity
import DifferentialGeometry.Geometry.Comparison.Variation.Field.Smoothness
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.ChainRule
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Local

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem chartRepAt_diff_of_smooth_total
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M))) (t : ℝ) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
  have hsplit := Bundle.contMDiffAt_totalSpace.mp (hV t)
  have hnbd : ∀ᶠ s in 𝓝 t,
      γ s ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    hsplit.1.continuousAt.preimage_mem_nhds
      ((Trivialization.open_baseSet _).mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  have heq : chartRepAt (I := I) γ V t =ᶠ[𝓝 t]
      (fun s => (trivializationAt E (TangentSpace I) (γ t)
        (TotalSpace.mk' E (γ s) (V s))).2) := by
    filter_upwards [hnbd] with s hs
    change (trivializationAt E (TangentSpace I) (γ t)).linearMapAt ℝ (γ s) (V s) = _
    rw [Trivialization.coe_linearMapAt_of_mem _ hs]
  exact (contMDiffAt_iff_contDiffAt.mp hsplit.2).differentiableAt
    (by simp) |>.congr_of_eventuallyEq heq

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem edistOf_le_of_metric_preserving
    (g : SmoothRiemannianMetric I M) (f : M → M) (hf : ContMDiff I I ∞ f)
    (hmetric : ∀ x v w, g.inner (f x) (mfderiv I I f x v) (mfderiv I I f x w) =
      g.inner x v w) (x y : M) :
    riemannianEDistOf (I := I) g (f x) (f y) ≤ riemannianEDistOf (I := I) g x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  have hmap : ContMDiff (𝓡∂ 1) I 1 (γ.map hf.continuous) := by
    change ContMDiff (𝓡∂ 1) I 1 (f ∘ γ)
    exact (hf.of_le (by simp)).comp hγ
  refine iInf_le_of_le (γ.map hf.continuous) (iInf_le_of_le hmap ?_)
  apply le_of_eq
  apply lintegral_congr
  intro t
  have hderiv : mfderiv (𝓡∂ 1) I (γ.map hf.continuous) t 1 =
      mfderiv I I f (γ t) (mfderiv (𝓡∂ 1) I γ t 1) := by
    change mfderiv (𝓡∂ 1) I (f ∘ γ) t 1 = _
    exact mfderiv_comp_apply t (hf.mdifferentiable (by simp) (γ t))
      (hγ.mdifferentiable one_ne_zero t) 1
  change ENNReal.ofReal (Real.sqrt (g.inner (f (γ t))
    (mfderiv (𝓡∂ 1) I (γ.map hf.continuous) t 1)
    (mfderiv (𝓡∂ 1) I (γ.map hf.continuous) t 1))) = _
  rw [hderiv, hmetric]

end Local

variable [NeZero (Module.finrank ℝ E)]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem affine_flow_differential_data
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p : M) (v : TangentSpace I p) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (TotalSpace.mk' E (affineGradientFlow (I := I) g hEnorm b p t)
        (mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p v) :
          TangentBundle I M)) ∧
    ∀ t : ℝ, covDerivAlong (I := I) g (affineGradientFlow (I := I) g hEnorm b p)
      (fun s => mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x s) p v) t = 0 := by
  let c := intrinsicGeodesic (I := I) g hEnorm p v
  let f : ℝ → ℝ → M := fun s t => affineGradientFlow (I := I) g hEnorm b (c s) t
  have hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c := intrinsicGeodesic_contMDiff (I := I) g hEnorm p v
  have hc0 : c 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hcv : @Eq E (mfderiv 𝓘(ℝ, ℝ) I c 0 1) v :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v
  have hs (t : ℝ) := affineGradientFlow_slice_contMDiff (I := I) g hEnorm hb hunit hH t
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : ℝ × ℝ => f z.1 z.2) :=
    (affineGradientFlow_contMDiff (I := I) g hEnorm hb hunit hH).comp
      (contMDiff_snd.prodMk (hc.comp contMDiff_fst))
  have hvar (t : ℝ) : @Eq E (mfderiv 𝓘(ℝ, ℝ) I (fun s => f s t) 0 1)
      (mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p v) := by
    have hd := mfderiv_comp_apply 0 ((hs t).mdifferentiable (by simp) (c 0))
      (hc.mdifferentiable (by simp) 0) (1 : ℝ)
    change mfderiv 𝓘(ℝ, ℝ) I (fun s => f s t) 0 1 =
      mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) (c 0)
        (mfderiv 𝓘(ℝ, ℝ) I c 0 1) at hd
    rw [hcv] at hd
    erw [hc0] at hd
    exact hd
  constructor
  · have hfield := varField_smooth (I := I) f hf
    have hmap :
        (fun t => (TotalSpace.mk' E (f 0 t)
          (mfderiv 𝓘(ℝ, ℝ) I (fun s => f s t) 0 1) : TangentBundle I M)) =
        (fun t => (TotalSpace.mk' E (affineGradientFlow (I := I) g hEnorm b p t)
          (mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p v) :
            TangentBundle I M)) := by
      funext t
      erw [hvar t]
      dsimp only [f]
      rw [hc0]
    exact hmap ▸ hfield
  · intro t
    have hcomm := commute_ds_dt_intrinsic (I := I) g f
      (hf.of_le (WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤))) t
    have hvel (s : ℝ) : @Eq E (mfderiv 𝓘(ℝ, ℝ) I (fun u => f s u) t 1)
        (gradientFun (I := I) g b (f s t)) :=
      affineGradientFlow_velocity (I := I) g hEnorm hb hunit hH (c s) t
    have hγeq : (fun r => f 0 r) = affineGradientFlow (I := I) g hEnorm b p := by
      funext r
      dsimp only [f]
      rw [hc0]
    have hleft := congrArg
      (fun V : ℝ → E => covDerivAlong (I := I) g (fun s => f s t) V 0)
      (funext hvel)
    have hright := congrArg₂
      (fun (γ : ℝ → M) (V : ℝ → E) => covDerivAlong (I := I) g γ V t)
      hγeq (funext hvar)
    have hzero : covDerivAlong (I := I) g (fun s => f s t)
        (fun s => gradientFun (I := I) g b (f s t)) 0 = 0 :=
      (covDerivAlong_restrict_eq_leviCivita (I := I) g (fun s => f s t)
        (fun x => gradientFun (I := I) g b x) 0 ((hs t).comp hc)
        (gradientFun_mdiffAt (I := I) g hb _)).trans
        (cov_gradient_eq_zero_of_hessian_eq_zero (I := I) g hb hH _ _)
    exact hright.symm.trans (hcomm.symm.trans (hleft.trans hzero))

theorem affineGradientFlow_differential_parallel
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p : M) (v : TangentSpace I p) (t : ℝ) :
    covDerivAlong (I := I) g (affineGradientFlow (I := I) g hEnorm b p)
      (fun s => mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x s) p v) t = 0 :=
  (affine_flow_differential_data (I := I) g hEnorm hb hunit hH p v).2 t

theorem affineGradientFlow_preserves_metric
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p : M) (v w : TangentSpace I p) (t : ℝ) :
    g.inner (affineGradientFlow (I := I) g hEnorm b p t)
      (mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p v)
      (mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p w) =
      g.inner p v w := by
  let γ := affineGradientFlow (I := I) g hEnorm b p
  let V : ∀ t, TangentSpace I (γ t) :=
    fun t => mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p v
  let W : ∀ t, TangentSpace I (γ t) :=
    fun t => mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p w
  obtain ⟨hVsm, hVpar⟩ := affine_flow_differential_data (I := I) g hEnorm hb hunit hH p v
  obtain ⟨hWsm, hWpar⟩ := affine_flow_differential_data (I := I) g hEnorm hb hunit hH p w
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm p (gradientFun (I := I) g b p)
  have hd (s : ℝ) : HasDerivAt (fun r => g.inner (γ r) (V r) (W r)) 0 s := by
    have hh := metric_compat_hasDerivAt_inner (I := I) (by simp : (1 : ℕ∞ω) ≤ ∞)
      g γ V W s hγ
      (chartRepAt_diff_of_smooth_total (I := I) γ V hVsm s)
      (chartRepAt_diff_of_smooth_total (I := I) γ W hWsm s)
    simpa only [V, W, γ, hVpar, hWpar, map_zero, zero_apply,
      zero_add] using hh
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  change g.inner (γ t) (V t) (W t) = _
  rw [hconst]
  change g.inner (affineGradientFlow (I := I) g hEnorm b p 0)
    (mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x 0) p v)
    (mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x 0) p w) = _
  have hflow0 : (fun x => affineGradientFlow (I := I) g hEnorm b x 0) = id :=
    funext (affineGradientFlow_zero (I := I) g hEnorm b)
  erw [hflow0, mfderiv_id]
  exact congrArg (fun q => g.inner q v w) (affineGradientFlow_zero (I := I) g hEnorm b p)

theorem affineGradientFlow_isometry
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (t : ℝ) :
    Isometry (fun p => affineGradientFlow (I := I) g hEnorm b p t) := by
  have hle (s : ℝ) (x y : M) :
      riemannianEDistOf (I := I) g (affineGradientFlow (I := I) g hEnorm b x s)
        (affineGradientFlow (I := I) g hEnorm b y s) ≤ riemannianEDistOf (I := I) g x y :=
    edistOf_le_of_metric_preserving (I := I) g
      (fun p => affineGradientFlow (I := I) g hEnorm b p s)
      (affineGradientFlow_slice_contMDiff (I := I) g hEnorm hb hunit hH s)
      (fun p v w => affineGradientFlow_preserves_metric (I := I) g hEnorm hb hunit hH p v w s)
      x y
  have hinv (x : M) : affineGradientFlow (I := I) g hEnorm b
      (affineGradientFlow (I := I) g hEnorm b x t) (-t) = x := by
    rw [← affineGradientFlow_add (I := I) g hEnorm hb hunit hH,
      neg_add_cancel, affineGradientFlow_zero]
  intro x y
  have hback := hle (-t) (affineGradientFlow (I := I) g hEnorm b x t)
    (affineGradientFlow (I := I) g hEnorm b y t)
  rw [hinv, hinv] at hback
  have heq := le_antisymm (hle t x y) hback
  have hd (p q : M) : riemannianEDistOf (I := I) g p q = edist p q :=
    (riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm p q).trans
      (IsRiemannianManifold.out (I := I) p q).symm
  simpa only [hd] using heq

def affineGradientFlowIsometryEquiv
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (t : ℝ) : M ≃ᵢ M where
  toEquiv := (affineGradientFlowDiffeomorph (I := I) g hEnorm hb hunit hH t).toEquiv
  isometry_toFun := affineGradientFlow_isometry (I := I) g hEnorm hb hunit hH t

end DifferentialGeometry.Geometry.Topology

end
