import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private def warpedInner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → ℝ)
    (x : M × N) : TangentSpace (I.prod J) x →L[ℝ]
      TangentSpace (I.prod J) x →L[ℝ] ℝ :=
  localPullInner g Prod.fst x + f x.1 ^ 2 • localPullInner h Prod.snd x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N] in
private theorem warpedInner_apply
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → ℝ)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    warpedInner g h f x v w =
      g.inner x.1 v.1 w.1 + f x.1 ^ 2 * h.inner x.2 v.2 w.2 := by
  simp only [warpedInner, add_apply, smul_apply, smul_eq_mul, localPullInner_apply,
    mfderiv_fst, mfderiv_snd]
  rfl

private theorem warpedInner_eq_product_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → ℝ)
    (hf : ∀ x, 0 < f x) (x : M × N) :
    warpedInner g h f x =
      (g.prod (scaleMetric (f x.1 ^ 2) (sq_pos_of_pos (hf x.1)) h)).inner x := by
  ext v w
  rw [warpedInner_apply, SmoothRiemannianMetric.prod_inner]
  rfl

def SmoothRiemannianMetric.warpedProduct
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x) :
    SmoothRiemannianMetric (I.prod J) (M × N) where
  inner := warpedInner g h f
  symm x := by
    rw [warpedInner_eq_product_inner g h f hpos x]
    exact (g.prod (scaleMetric (f x.1 ^ 2) (sq_pos_of_pos (hpos x.1)) h)).symm x
  pos x := by
    rw [warpedInner_eq_product_inner g h f hpos x]
    exact (g.prod (scaleMetric (f x.1 ^ 2) (sq_pos_of_pos (hpos x.1)) h)).pos x
  isVonNBounded x := by
    simp only [warpedInner_eq_product_inner g h f hpos x]
    exact (g.prod (scaleMetric (f x.1 ^ 2) (sq_pos_of_pos (hpos x.1)) h)).isVonNBounded x
  contMDiff :=
    (contMDiff_localPullInner g Prod.fst contMDiff_fst).add_section
      (((hf.comp contMDiff_fst).pow 2).smul_section
        (contMDiff_localPullInner h Prod.snd contMDiff_snd))

@[simp]
theorem SmoothRiemannianMetric.warpedProduct_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    (g.warpedProduct h f hf hpos).inner x v w =
      g.inner x.1 v.1 w.1 + f x.1 ^ 2 * h.inner x.2 v.2 w.2 :=
  warpedInner_apply g h f x v w

theorem SmoothRiemannianMetric.warpedProduct_const
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (c : ℝ) (hc : 0 < c) :
    g.warpedProduct h (fun _ => c) contMDiff_const (fun _ => hc) =
      g.prod (scaleMetric (c ^ 2) (sq_pos_of_pos hc) h) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [SmoothRiemannianMetric.warpedProduct_inner, SmoothRiemannianMetric.prod_inner]
  rfl

@[simp]
theorem SmoothRiemannianMetric.warpedProduct_one
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) :
    g.warpedProduct h (fun _ => 1) contMDiff_const (fun _ => zero_lt_one) =
      g.prod h := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [SmoothRiemannianMetric.warpedProduct_inner,
    SmoothRiemannianMetric.prod_inner, one_pow, one_mul]

end DifferentialGeometry
