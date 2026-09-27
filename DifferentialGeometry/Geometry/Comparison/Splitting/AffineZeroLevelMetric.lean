import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFunctionProduct
import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFlowIsometry
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.Construction.Existence

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [T2Space M] in
private theorem immersionPullInner_pos
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < localPullInner (I := I) (J := J) g f x v v := by
  rw [localPullInner_apply]
  apply g.pos (f x)
  intro hz
  exact hv (hinj x (hz.trans (map_zero _).symm))

private def immersionPullbackMetric
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : ContMDiff I J ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    SmoothRiemannianMetric I M where
  inner x := localPullInner (I := I) (J := J) g f x
  symm x v w := by
    rw [localPullInner_apply, localPullInner_apply]
    exact g.symm (f x) _ _
  pos := immersionPullInner_pos (I := I) (J := J) g f hinj
  isVonNBounded x := by
    change Bornology.IsVonNBounded ℝ
      {v : E | localPullInner (I := I) (J := J) g f x v v < 1}
    exact posDef_isVonNBounded (E := E) (localPullInner (I := I) (J := J) g f x)
      (immersionPullInner_pos (I := I) (J := J) g f hinj x)
  contMDiff := by
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (φ := fun x => localPullInner (I := I) (J := J) g f x)
    intro Y
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun _ : M => ℝ)
      (φ := fun x => localPullInner (I := I) (J := J) g f x (Y x))
    intro W
    have hY : ContMDiff I (J.prod 𝓘(ℝ, F)) ∞
        (fun x : M => TotalSpace.mk' F (E := TangentSpace J) (f x)
          (mfderiv I J f x (Y x))) :=
      (hf.contMDiff_tangentMap (le_refl _)).comp Y.contMDiff
    have hW : ContMDiff I (J.prod 𝓘(ℝ, F)) ∞
        (fun x : M => TotalSpace.mk' F (E := TangentSpace J) (f x)
          (mfderiv I J f x (W x))) :=
      (hf.contMDiff_tangentMap (le_refl _)).comp W.contMDiff
    have hg : ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
        (fun x : M => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
          (E := fun y : N => TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ)
          (f x) (g.inner (f x))) := g.contMDiff.comp hf
    have ht : ContMDiff I (J.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ (E := Bundle.Trivial N ℝ) (f x)
          (g.inner (f x) (mfderiv I J f x (Y x)) (mfderiv I J f x (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun y : N => TangentSpace J y)
        (E₂ := fun y : N => TangentSpace J y) (E₃ := fun _ : N => ℝ)
        (b := f) (ψ := fun x => g.inner (f x))
        (v := fun x => mfderiv I J f x (Y x))
        (w := fun x => mfderiv I J f x (W x)) hg hY hW
    have hs : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => g.inner (f x) (mfderiv I J f x (Y x))
          (mfderiv I J f x (W x))) := by
      intro x
      have hx := ht x
      rw [contMDiffAt_totalSpace] at hx
      exact hx.2
    have hp : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => localPullInner (I := I) (J := J) g f x (Y x) (W x)) := by
      simpa only [localPullInner_apply] using hs
    intro x
    rw [contMDiffAt_section]
    refine hp.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl

end Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
  {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
  (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
  (hH : ∀ p, hessFun (I := I) g b p = 0)

def affineZeroLevelMetric (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
    SmoothRiemannianMetric 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
      {q : M // b q = 0} := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
  exact immersionPullbackMetric g (Subtype.val : {q : M // b q = 0} → M)
    (affineZeroLevel_inclusion_contMDiff (I := I) g hEnorm hb hunit hH p₀)
    (affineZeroLevel_inclusion_mfderiv_injective (I := I) g hEnorm hb hunit hH p₀)

theorem affineZeroLevelMetric_inner (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
    ∀ (p : {q : M // b q = 0})
      (v w : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p),
      (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).inner p v w =
        g.inner p.1
          (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v)
          (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p w) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
  exact fun p v w => localPullInner_apply g Subtype.val p v w

theorem affineZeroLevel_inclusion_orthogonal_gradient (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ∀ (p : {q : M // b q = 0})
      (v : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p),
      g.inner p.1 (gradientFun (I := I) g b p.1)
        (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v) = 0 := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ∀ (p : {q : M // b q = 0})
    (v : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p),
    g.inner p.1 (gradientFun (I := I) g b p.1)
      (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v) = 0
  intro p v
  rw [inner_gradientFun]
  exact affineZeroLevel_inclusion_mvfderiv_eq_zero (I := I) g hEnorm hb hunit hH p₀ p v

include hb hunit hH in
theorem affineGradientFlow_preserves_differential
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    mvfderiv (I := I) b (affineGradientFlow (I := I) g hEnorm b p t)
      (mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p v) =
        mvfderiv (I := I) b p v := by
  have h := mvfderiv_comp_apply p
    (hb.mdifferentiable (by simp) (affineGradientFlow (I := I) g hEnorm b p t))
    ((affineGradientFlow_slice_contMDiff (I := I) g hEnorm hb hunit hH t).mdifferentiable
      (by simp) p) v
  have heq : b ∘ (fun x => affineGradientFlow (I := I) g hEnorm b x t) =
      fun x => b x + t :=
    funext (fun x => affineFunction_flow_eq_add (I := I) g hEnorm hb hunit hH x t)
  rw [heq, mvfderiv_fun_add (hb.mdifferentiable (by simp) p) mdifferentiableAt_const,
    mvfderiv_const, add_zero] at h
  exact h.symm

theorem affineZeroLevel_flow_orthogonal_gradient (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ∀ (p : {q : M // b q = 0})
      (v : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p) (t : ℝ),
      g.inner (affineGradientFlow (I := I) g hEnorm b p.1 t)
        (gradientFun (I := I) g b (affineGradientFlow (I := I) g hEnorm b p.1 t))
        (mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p.1
          (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v)) = 0 := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ∀ (p : {q : M // b q = 0})
    (v : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p) (t : ℝ),
    g.inner (affineGradientFlow (I := I) g hEnorm b p.1 t)
      (gradientFun (I := I) g b (affineGradientFlow (I := I) g hEnorm b p.1 t))
      (mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p.1
        (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v)) = 0
  intro p v t
  rw [inner_gradientFun,
    affineGradientFlow_preserves_differential (I := I) g hEnorm hb hunit hH]
  exact affineZeroLevel_inclusion_mvfderiv_eq_zero (I := I) g hEnorm hb hunit hH p₀ p v

theorem affineFunctionZeroLevelDiffeomorph_mfderiv (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ∀ (p : {q : M // b q = 0})
      (v : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p) (t a : ℝ),
      mfderiv (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ)) I
        (affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀) (p, t) (v, a) =
      mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p.1
        (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v) +
        a • gradientFun (I := I) g b (affineGradientFlow (I := I) g hEnorm b p.1 t) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ∀ (p : {q : M // b q = 0})
    (v : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p) (t a : ℝ),
    mfderiv (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ)) I
      (affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀) (p, t) (v, a) =
    mfderiv I I (fun x => affineGradientFlow (I := I) g hEnorm b x t) p.1
      (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v) +
      a • gradientFun (I := I) g b (affineGradientFlow (I := I) g hEnorm b p.1 t)
  intro p v t a
  let Φ := affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀
  have h := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
    (Φ.contMDiff.mdifferentiable (by simp) (p, t))
    (v := (v, a))
  have hs := mfderiv_comp_apply p
    ((affineGradientFlow_slice_contMDiff (I := I) g hEnorm hb hunit hH t).mdifferentiable
      (by simp) p.1)
    ((affineZeroLevel_inclusion_contMDiff (I := I) g hEnorm hb hunit hH p₀).mdifferentiable
      (by simp) p) v
  have ht : mfderiv 𝓘(ℝ, ℝ) I (affineGradientFlow (I := I) g hEnorm b p.1) t a =
      a • gradientFun (I := I) g b (affineGradientFlow (I := I) g hEnorm b p.1 t) := by
    rw [(affineGradientFlow_isMIntegralCurve (I := I) g hEnorm hb hunit hH p.1 t).mfderiv]
    rfl
  exact h.trans (congrArg₂ (fun u w => u + w) hs ht)

theorem affineFunctionZeroLevelDiffeomorph_preserves_product_metric
    (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
    ∀ (p : {q : M // b q = 0})
      (v w : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p) (t a c : ℝ),
      g.inner (affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀ (p, t))
        (mfderiv (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ)) I
          (affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀) (p, t) (v, a))
        (mfderiv (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ)) I
          (affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀) (p, t) (w, c)) =
        (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).inner p v w + a * c := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
  change ∀ (p : {q : M // b q = 0})
    (v w : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p) (t a c : ℝ),
    g.inner (affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀ (p, t))
      (mfderiv (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ)) I
        (affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀) (p, t) (v, a))
      (mfderiv (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ)) I
        (affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀) (p, t) (w, c)) =
      (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).inner p v w + a * c
  intro p v w t a c
  erw [affineFunctionZeroLevelDiffeomorph_mfderiv (I := I) g hEnorm hb hunit hH p₀ p v t a,
    affineFunctionZeroLevelDiffeomorph_mfderiv (I := I) g hEnorm hb hunit hH p₀ p w t c]
  let q := affineGradientFlow (I := I) g hEnorm b p.1 t
  let V : TangentSpace I q := mfderiv I I
    (fun x => affineGradientFlow (I := I) g hEnorm b x t) p.1
    (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v)
  let W : TangentSpace I q := mfderiv I I
    (fun x => affineGradientFlow (I := I) g hEnorm b x t) p.1
    (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p w)
  let n : TangentSpace I q := gradientFun (I := I) g b q
  have hnV : g.inner q n V = 0 :=
    affineZeroLevel_flow_orthogonal_gradient (I := I) g hEnorm hb hunit hH p₀ p v t
  have hnW : g.inner q n W = 0 :=
    affineZeroLevel_flow_orthogonal_gradient (I := I) g hEnorm hb hunit hH p₀ p w t
  have hVn : g.inner q V n = 0 := (g.symm q V n).trans hnV
  have hnn : g.inner q n n = 1 := hunit q
  have hVW : g.inner q V W =
      (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).inner p v w :=
    (affineGradientFlow_preserves_metric (I := I) g hEnorm hb hunit hH p.1 _ _ t).trans
      (affineZeroLevelMetric_inner (I := I) g hEnorm hb hunit hH p₀ p v w).symm
  change g.inner q (V + a • n) (W + c • n) = _
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
    hVn, hnW, hnn, hVW, mul_zero, mul_one, zero_add, add_zero]
  ring

end DifferentialGeometry.Geometry.Topology

end
