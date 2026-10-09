import DifferentialGeometry.Geometry.Comparison.Splitting.AffineZeroLevelMetric
import DifferentialGeometry.Geometry.Metric.Completeness

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Topology ContDiff Manifold ENNReal
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Distance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

private theorem edistOf_le_of_differential_contracting
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hmetric : ∀ x v, h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v) ≤
      g.inner x v v) (x y : M) :
    riemannianEDistOf (I := J) h (f x) (f y) ≤ riemannianEDistOf (I := I) g x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  have hmap : ContMDiff (𝓡∂ 1) J 1 (γ.map hf.continuous) := by
    change ContMDiff (𝓡∂ 1) J 1 (f ∘ γ)
    exact (hf.of_le (by simp)).comp hγ
  refine iInf_le_of_le (γ.map hf.continuous) (iInf_le_of_le hmap ?_)
  apply lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  have hd : mfderiv (𝓡∂ 1) J (γ.map hf.continuous) t 1 =
      mfderiv I J f (γ t) (mfderiv (𝓡∂ 1) I γ t 1) := by
    change mfderiv (𝓡∂ 1) J (f ∘ γ) t 1 = _
    exact mfderiv_comp_apply t (hf.mdifferentiable (by simp) (γ t))
      (hγ.mdifferentiable one_ne_zero t) 1
  change h.inner (f (γ t)) (mfderiv (𝓡∂ 1) J (γ.map hf.continuous) t 1)
    (mfderiv (𝓡∂ 1) J (γ.map hf.continuous) t 1) ≤ _
  rw [hd]
  exact hmetric (γ t) _

end Distance

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

theorem affineZeroLevelRetraction_metric_decomposition (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
    ∀ (x : M) (v : TangentSpace I x),
      (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).inner
        (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x)
        (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
          (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) x v)
        (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
          (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) x v) +
        (mvfderiv (I := I) b x v) ^ 2 = g.inner x v v := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
  change ∀ (x : M) (v : TangentSpace I x),
    (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).inner
      (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x)
      (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
        (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) x v)
      (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
        (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) x v) +
      (mvfderiv (I := I) b x v) ^ 2 = g.inner x v v
  intro x v
  let K := affineFunctionKernel (I := I) b p₀.1
  let Φ := affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀
  let r := affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH
  let z := Φ.symm x
  let Z := mfderiv I (𝓘(ℝ, K).prod 𝓘(ℝ, ℝ)) Φ.symm x v
  have hZ : Z = (mfderiv I 𝓘(ℝ, K) r x v, mvfderiv (I := I) b x v) := by
    change (mfderiv I (𝓘(ℝ, K).prod 𝓘(ℝ, ℝ)) (fun y => (r y, b y)) x) v = _
    rw [mfderiv_prodMk
      ((affineZeroLevelRetraction_contMDiff (I := I) g hEnorm hb hunit hH p₀).mdifferentiable
        (by simp) x) (hb.mdifferentiable (by simp) x)]
    rfl
  have hback := mfderiv_comp_apply x
    (Φ.contMDiff.mdifferentiable (by simp) z) (Φ.symm.contMDiff.mdifferentiable (by simp) x) v
  have hid : (Φ : {q : M // b q = 0} × ℝ → M) ∘ Φ.symm = id :=
    funext Φ.apply_symm_apply
  rw [hid, mfderiv_id] at hback
  have hm := affineFunctionZeroLevelDiffeomorph_preserves_product_metric
    (I := I) g hEnorm hb hunit hH p₀ z.1 Z.1 Z.1 z.2 Z.2 Z.2
  have hpair : (Z.1, Z.2) = Z := rfl
  rw [hpair] at hm
  have heval : g.inner (Φ z)
      (mfderiv (𝓘(ℝ, K).prod 𝓘(ℝ, ℝ)) I Φ z Z)
      (mfderiv (𝓘(ℝ, K).prod 𝓘(ℝ, ℝ)) I Φ z Z) = g.inner x v v := by
    rw [← hback]
    exact congrArg (fun q => g.inner q v v) (Φ.apply_symm_apply x)
  have hout := hm.symm.trans heval
  rw [hZ] at hout
  simpa only [z, Φ, r, K, sq] using! hout

theorem affineZeroLevelRetraction_metric_le (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
    ∀ (x : M) (v : TangentSpace I x),
      (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).inner
        (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x)
        (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
          (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) x v)
        (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
          (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) x v) ≤ g.inner x v v := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
  change ∀ (x : M) (v : TangentSpace I x),
    (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).inner
      (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x)
      (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
        (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) x v)
      (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
        (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) x v) ≤ g.inner x v v
  intro x v
  have h := affineZeroLevelRetraction_metric_decomposition (I := I) g hEnorm hb hunit hH p₀ x v
  nlinarith [sq_nonneg (mvfderiv (I := I) b x v)]

theorem affineZeroLevelMetric_edist_eq (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
    ∀ p q : {q : M // b q = 0},
      riemannianEDistOf (I := 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1))
        (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀) p q = edist p.1 q.1 := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
  change ∀ p q : {q : M // b q = 0},
    riemannianEDistOf (I := 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1))
      (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀) p q = edist p.1 q.1
  intro p q
  let h := affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀
  have hambient : riemannianEDistOf (I := I) g p.1 q.1 = edist p.1 q.1 :=
    (riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm p.1 q.1).trans
      (IsRiemannianManifold.out (I := I) p.1 q.1).symm
  rw [← hambient]
  apply le_antisymm
  · have hc := edistOf_le_of_differential_contracting g h
      (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH)
      (affineZeroLevelRetraction_contMDiff (I := I) g hEnorm hb hunit hH p₀)
      (affineZeroLevelRetraction_metric_le (I := I) g hEnorm hb hunit hH p₀) p.1 q.1
    simpa only [affineZeroLevelRetraction_inclusion] using hc
  · exact edistOf_le_of_differential_contracting h g Subtype.val
      (affineZeroLevel_inclusion_contMDiff (I := I) g hEnorm hb hunit hH p₀)
      (fun x v => (affineZeroLevelMetric_inner (I := I) g hEnorm hb hunit hH p₀ x v v).symm.le)
      p q

theorem affineZeroLevelMetric_isRiemannianManifold (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
    let _ : RiemannianBundle
        (TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) : {q : M // b q = 0} → Type _) :=
      ⟨(affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).toRiemannianMetric⟩
    IsRiemannianManifold 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) {q : M // b q = 0} := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
  let _ : RiemannianBundle
      (TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) : {q : M // b q = 0} → Type _) :=
    ⟨(affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).toRiemannianMetric⟩
  change IsRiemannianManifold 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) {q : M // b q = 0}
  refine ⟨fun p q => ?_⟩
  exact (affineZeroLevelMetric_edist_eq (I := I) g hEnorm hb hunit hH p₀ p q).symm

theorem affineZeroLevelMetric_complete (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
    let _ : SigmaCompactSpace {q : M // b q = 0} :=
      (isClosed_eq hb.continuous continuous_const).sigmaCompactSpace
    RiemannianMetricComplete (I := 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1))
      (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
  let _ : SigmaCompactSpace {q : M // b q = 0} :=
    (isClosed_eq hb.continuous continuous_const).sigmaCompactSpace
  change RiemannianMetricComplete (I := 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1))
    (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀)
  let N := {q : M // b q = 0}
  let K := affineFunctionKernel (I := I) b p₀.1
  let h := affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀
  let _ : IsManifold 𝓘(ℝ, K) 1 N := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace 𝓘(ℝ, K) N
  let _ : T3Space N := inferInstance
  refine ⟨?_⟩
  let _ : RiemannianBundle (TangentSpace 𝓘(ℝ, K) : N → Type _) := ⟨h.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle K (TangentSpace 𝓘(ℝ, K) : N → Type _) :=
    ⟨⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let hEM : EMetricSpace N := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, K) N
  let _ : EMetricSpace N := hEM
  let _ : PseudoEMetricSpace N := hEM.toPseudoEMetricSpace
  let _ : UniformSpace N := hEM.toUniformSpace
  have hι : @Isometry N M hEM.toPseudoEMetricSpace inferInstance Subtype.val := by
    intro p q
    exact (affineZeroLevelMetric_edist_eq (I := I) g hEnorm hb hunit hH p₀ p q).symm
  have hclosed : IsClosed (Set.range (Subtype.val : N → M)) := by
    simpa only [N, Subtype.range_coe_subtype] using isClosed_eq hb.continuous continuous_const
  exact (completeSpace_iff_isComplete_range hι.isUniformInducing).2 hclosed.isComplete

end DifferentialGeometry.Geometry.Topology

end
