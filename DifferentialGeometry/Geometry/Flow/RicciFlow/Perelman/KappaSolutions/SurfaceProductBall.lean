import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Construction.CompactPerturbationCompleteness
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped _root_.Topology ContDiff Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

section Distance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem surfaceProductBall_edist_le_of_differential_contracting
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem surfaceProductBall_flat_edist (x y : ℝ) :
    riemannianEDistOf (I := 𝓘(ℝ, ℝ)) (flatModelMetric ℝ) x y = edist x y := by
  change Manifold.riemannianEDist 𝓘(ℝ, ℝ) x y = edist x y
  exact (IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)) x y).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem surfaceProduct_fst_edist_le
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hprod : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2)
    (p q : M × ℝ) :
    riemannianEDistOf (I := I) h p.1 q.1 ≤
      riemannianEDistOf (I := I.prod 𝓘(ℝ, ℝ)) gP p q := by
  apply surfaceProductBall_edist_le_of_differential_contracting
    gP h Prod.fst contMDiff_fst _ p q
  intro z v
  rw [mfderiv_fst]
  change h.inner z.1 v.1 v.1 ≤ gP.inner z v v
  rw [hprod]
  exact le_add_of_nonneg_right (mul_self_nonneg v.2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem surfaceProduct_snd_edist_le
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hprod : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2)
    (p q : M × ℝ) :
    edist p.2 q.2 ≤ riemannianEDistOf (I := I.prod 𝓘(ℝ, ℝ)) gP p q := by
  rw [← surfaceProductBall_flat_edist]
  apply surfaceProductBall_edist_le_of_differential_contracting
    gP (flatModelMetric ℝ) Prod.snd contMDiff_snd _ p q
  intro z v
  rw [mfderiv_snd]
  change v.2 * v.2 ≤ gP.inner z v v
  rw [hprod]
  have hnonneg : 0 ≤ h.inner z.1 v.1 v.1 := by
    by_cases hv : v.1 = 0
    · rw [hv]
      change 0 ≤ ((h.inner z.1 : E →L[ℝ] E →L[ℝ] ℝ) 0) 0
      simp
    · exact (h.pos z.1 v.1 hv).le
  exact le_add_of_nonneg_left hnonneg

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem surfaceProduct_ball_subset
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hprod : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2)
    (y : M) (r : ℝ) (hr : 0 < r) :
    {p : M × ℝ | riemannianEDistOf (I := I.prod 𝓘(ℝ, ℝ)) gP (y, 0) p <
        ENNReal.ofReal r} ⊆
      {z : M | riemannianEDistOf (I := I) h y z < ENNReal.ofReal r} ×ˢ
        Set.Ioo (-r) r := by
  intro p hp
  refine ⟨lt_of_le_of_lt (surfaceProduct_fst_edist_le h gP hprod (y, 0) p) hp, ?_⟩
  have hline : edist (0 : ℝ) p.2 < ENNReal.ofReal r :=
    lt_of_le_of_lt (surfaceProduct_snd_edist_le h gP hprod (y, 0) p) hp
  rw [edist_dist, dist_zero_left, Real.norm_eq_abs] at hline
  exact abs_lt.mp ((ENNReal.ofReal_lt_ofReal_iff hr).mp hline)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
