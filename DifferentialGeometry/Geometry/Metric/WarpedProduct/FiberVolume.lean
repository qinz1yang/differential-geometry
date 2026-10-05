import DifferentialGeometry.Geometry.Metric.WarpedProduct
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
Scaling the two-dimensional fibre of an actual warped metric multiplies its volume by the
square of the scale, also after the same three-dimensional immersion pullback.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open Bundle Manifold MeasureTheory
open scoped Manifold ContDiff

variable {E F H G M N : Type*}
  [nE : NormedAddCommGroup E] [sE : NormedSpace ℝ E] [dE : FiniteDimensional ℝ E]
  [nF : NormedAddCommGroup F] [sF : NormedSpace ℝ F] [dF : FiniteDimensional ℝ F]
  [tH : TopologicalSpace H] [tG : TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [tM : TopologicalSpace M] [cM : ChartedSpace H M] [mM : IsManifold I ∞ M]
  [hM : T2Space M] [sM : SigmaCompactSpace M]
  [tN : TopologicalSpace N] [cN : ChartedSpace G N] [mN : IsManifold J ∞ N]
  [hN : T2Space N]

omit hM sM in
private theorem gram_det_conjugate (g h : SmoothRiemannianMetric I M)
    (p : M) {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (A : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (hinner : ∀ v w, h.inner x v w = g.inner x (A v) (A w)) :
    (Tensor.Coordinates.chartGramMatrix h p x).det =
      A.det ^ 2 * (Tensor.Coordinates.chartGramMatrix g p x).det := by
  classical
  let b := Tensor.Coordinates.chartBasisFamily (I := I) p hx
  have hmat (q : SmoothRiemannianMetric I M) :
      Tensor.Coordinates.chartGramMatrix q p x = LinearMap.toMatrix₂ b b (q.inner x).toBilinForm :=
    by
      ext i j
      simp only [Tensor.Coordinates.chartGramMatrix_apply, LinearMap.toMatrix₂_apply,
        ContinuousLinearMap.toBilinForm_apply, b, Tensor.Coordinates.chartBasisFamily_apply]
  have hb : (h.inner x).toBilinForm = (g.inner x).toBilinForm.compl₁₂ A A := by
    ext v w
    exact hinner v w
  rw [hmat h, hb, LinearMap.toMatrix₂_compl₁₂ b b b b,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, ← hmat g]
  ring

omit sM in
private theorem warped_pullback_density (hF : Module.finrank ℝ F = 2)
    (hE : Module.finrank ℝ E = 3) (h : SmoothRiemannianMetric J N)
    (w : ℝ → ℝ) (hw : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w)
    (hpos : ∀ r, 0 < w r) (f : M → ℝ × N)
    (hf : ContMDiff I (𝓘(ℝ, ℝ).prod J) ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv I (𝓘(ℝ, ℝ).prod J) f x))
    (a : ℝ) (ha : 0 < a) (p : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    chartDensity (I := I)
      (((euclideanMetric (E := ℝ)).warpedProduct h (fun r => a * w r)
        (contMDiff_const.mul hw) (fun r => mul_pos ha (hpos r))).pullback f hf himm) p x =
      a ^ 2 * chartDensity (I := I)
        (((euclideanMetric (E := ℝ)).warpedProduct h w hw hpos).pullback f hf himm) p x := by
  let L : TangentSpace I x →ₗ[ℝ] ℝ × F :=
    (mfderiv I (𝓘(ℝ, ℝ).prod J) f x).toLinearMap
  have hdim : Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace (𝓘(ℝ, ℝ).prod J) (f x)) := by
    change Module.finrank ℝ E = Module.finrank ℝ (ℝ × F)
    simp [Module.finrank_prod, hE, hF]
  let e := LinearEquiv.ofBijective L
    ⟨himm x, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (himm x)⟩
  let D : (ℝ × F) →ₗ[ℝ] ℝ × F :=
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap (a • (LinearMap.id : F →ₗ[ℝ] F))
  let A : TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
    e.symm.toLinearMap ∘ₗ D ∘ₗ e.toLinearMap
  have hdet : A.det = a ^ 2 := by
    have hedet : A.det = D.det := LinearMap.det_conj D e.symm
    apply hedet.trans
    change ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap
      (a • (LinearMap.id : F →ₗ[ℝ] F))).det = a ^ 2
    rw [LinearMap.det_prodMap, LinearMap.det_smul]
    simp [hF]
  have hLA (v : TangentSpace I x) : L (A v) = D (L v) := by
    change e (e.symm (D (e v))) = D (e v)
    exact e.apply_symm_apply _
  let q := ((euclideanMetric (E := ℝ)).warpedProduct h w hw hpos).pullback f hf himm
  let qa := ((euclideanMetric (E := ℝ)).warpedProduct h (fun r => a * w r)
    (contMDiff_const.mul hw) (fun r => mul_pos ha (hpos r))).pullback f hf himm
  have hinner : ∀ v z, qa.inner x v z = q.inner x (A v) (A z) := by
    intro v z
    simp only [qa, q, SmoothRiemannianMetric.pullback_inner,
      SmoothRiemannianMetric.warpedProduct_inner]
    let B₀ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := (euclideanMetric (E := ℝ)).inner (f x).1
    let B : F →L[ℝ] F →L[ℝ] ℝ := h.inner (f x).2
    change B₀ (L v).1 (L z).1 + (a * w (f x).1) ^ 2 * B (L v).2 (L z).2 =
      B₀ (L (A v)).1 (L (A z)).1 + w (f x).1 ^ 2 * B (L (A v)).2 (L (A z)).2
    rw [hLA, hLA]
    change _ = B₀ (L v).1 (L z).1 + w (f x).1 ^ 2 * B (a • (L v).2) (a • (L z).2)
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    ring
  have hd := gram_det_conjugate q qa p hx A hinner
  rw [hdet] at hd
  change Real.sqrt _ = a ^ 2 * Real.sqrt _
  rw [hd, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg a)]

theorem volume_warped_fiber_scale_pullback (hF : Module.finrank ℝ F = 2)
    (hE : Module.finrank ℝ E = 3) (h : SmoothRiemannianMetric J N)
    (w : ℝ → ℝ) (hw : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w)
    (hpos : ∀ r, 0 < w r) (f : M → ℝ × N)
    (hf : ContMDiff I (𝓘(ℝ, ℝ).prod J) ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv I (𝓘(ℝ, ℝ).prod J) f x))
    (a : ℝ) (ha : 0 < a) :
    riemannianVolumeMeasure I M
      (((euclideanMetric (E := ℝ)).warpedProduct h (fun r => a * w r)
        (contMDiff_const.mul hw) (fun r => mul_pos ha (hpos r))).pullback f hf himm) =
      ENNReal.ofReal (a ^ 2) • riemannianVolumeMeasure I M
        (((euclideanMetric (E := ℝ)).warpedProduct h w hw hpos).pullback f hf himm) := by
  let q := ((euclideanMetric (E := ℝ)).warpedProduct h w hw hpos).pullback f hf himm
  let qa := ((euclideanMetric (E := ℝ)).warpedProduct h (fun r => a * w r)
    (contMDiff_const.mul hw) (fun r => mul_pos ha (hpos r))).pullback f hf himm
  have hr : riemannianVolumeDensity q qa = fun x => a ^ 2 := by
    funext x
    rw [riemannianVolumeDensity_apply_of_mem_chart_source q qa x (mem_chart_source H x)]
    rw [warped_pullback_density hF hE h w hw hpos f hf himm a ha x
      (mem_chart_source H x)]
    exact mul_div_cancel_right₀ _ (ne_of_gt (chartDensity_pos q x (mem_chart_source H x)))
  change riemannianVolumeMeasure I M qa = _
  rw [riemannianVolumeMeasure_eq_withDensity q qa, hr, withDensity_const]

end DifferentialGeometry.Integral.Measure
