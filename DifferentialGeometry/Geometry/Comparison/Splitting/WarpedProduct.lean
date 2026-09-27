import DifferentialGeometry.Geometry.Curvature.WarpedProduct.RealFiber
import DifferentialGeometry.Geometry.Comparison.Hessian.Concavity
import DifferentialGeometry.Geometry.Metric.WarpedProduct.Symmetry
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in
theorem hessFun_nonpos_of_warpedProduct_real_mixed_nonneg
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (hnonneg : ∀ x : M, ∀ u : TangentSpace I x,
      0 ≤ metricRm04StandardAt
        (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos)
        (x, 0) (u, 0) (0, 1) (0, 1) (u, 0)) :
    ∀ x : M, ∀ u : TangentSpace I x, Geometry.Operator.hessFun g f x u u ≤ 0 := by
  intro x u
  have h := hnonneg x u
  rw [metricRm04StandardAt_warpedProduct_real_mixed] at h
  by_contra hn
  have hprod := mul_pos (hpos x) (lt_of_not_ge hn)
  nlinarith

set_option backward.isDefEq.respectTransparency false in
theorem eq_of_warpedProduct_real_mixed_nonneg_of_complete
    [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (hnonneg : ∀ x : M, ∀ u : TangentSpace I x,
      0 ≤ metricRm04StandardAt
        (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos)
        (x, 0) (u, 0) (0, 1) (0, 1) (u, 0)) (p q : M) : f p = f q := by
  exact Riemannian.eq_of_hessFun_nonpos_of_positive_of_complete g hcomplete hf
    (hessFun_nonpos_of_warpedProduct_real_mixed_nonneg g f hf hpos hnonneg) hpos p q

set_option backward.isDefEq.respectTransparency false in
theorem warpedProduct_real_eq_prod_of_mixed_nonneg_of_complete
    [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (hnonneg : ∀ x : M, ∀ u : TangentSpace I x,
      0 ≤ metricRm04StandardAt
        (g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos)
        (x, 0) (u, 0) (0, 1) (0, 1) (u, 0)) (p : M) :
    g.warpedProduct (euclideanMetric (E := ℝ)) f hf hpos =
      g.prod (scaleMetric (f p ^ 2) (sq_pos_of_pos (hpos p)) (euclideanMetric (E := ℝ))) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [SmoothRiemannianMetric.warpedProduct_inner, SmoothRiemannianMetric.prod_inner,
    scaleMetric_inner,
    eq_of_warpedProduct_real_mixed_nonneg_of_complete g hcomplete f hf hpos hnonneg x.1 p]

end DifferentialGeometry.Geometry.Curvature

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry

open Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

theorem SmoothRiemannianMetric.eq_prod_scaled_real_of_complete_nonnegative_curvature_symmetries
    (G : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hcomplete : RiemannianMetricComplete G)
    (hcurvature : ∀ x : M × ℝ, metricAlgebraicCurvatureTensorAt G x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ))
    (htranslate : ∀ c : ℝ,
      Diffeomorph.pullbackMetricCross G
        ((Diffeomorph.refl I M ∞).prodCongr (Topology.translateDiffeomorph c)) = G)
    (hreflect : Diffeomorph.pullbackMetricCross G
      ((Diffeomorph.refl I M ∞).prodCongr
        (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv.toDiffeomorph) = G)
    (p : M) :
    G = (G.sliceFst 0).prod
      (scaleMetric (G.inner (p, 0) (0, 1) (0, 1)) (G.vertical_inner_pos p 0)
        (euclideanMetric (E := ℝ))) := by
  let f : M → ℝ := fun x => Real.sqrt (G.inner (x, 0) (0, 1) (0, 1))
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := G.contMDiff_sqrt_vertical_inner 0
  have hpos : ∀ x, 0 < f x := fun x => G.sqrt_vertical_inner_pos x 0
  have hwarp : G = (G.sliceFst 0).warpedProduct (euclideanMetric (E := ℝ)) f hf hpos :=
    G.eq_warpedProduct_of_pullback_translation_reflection htranslate hreflect
  have hbase : RiemannianMetricComplete (G.sliceFst 0) :=
    RiemannianMetricComplete.sliceFst G 0 hcomplete
  have hnonneg : ∀ x : M, ∀ u : TangentSpace I x,
      0 ≤ metricRm04StandardAt
        ((G.sliceFst 0).warpedProduct (euclideanMetric (E := ℝ)) f hf hpos)
        (x, 0) (u, 0) (0, 1) (0, 1) (u, 0) := by
    intro x u
    rw [← hwarp]
    have h := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      G (x, 0)).mp (hcurvature (x, 0)) 1 (fun _ => 1)
      (fun _ => (u, 0)) (fun _ => (0, 1))
    simpa only [Fin.sum_univ_one, one_mul] using h
  have hprod := warpedProduct_real_eq_prod_of_mixed_nonneg_of_complete
    (G.sliceFst 0) hbase f hf hpos hnonneg p
  have hsq : f p ^ 2 = G.inner (p, 0) (0, 1) (0, 1) :=
    Real.sq_sqrt (G.vertical_inner_pos p 0).le
  have h := hwarp.trans hprod
  simpa only [hsq] using h

end DifferentialGeometry
