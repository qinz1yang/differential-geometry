import DifferentialGeometry.Geometry.Comparison.Variation.Curve.TangentVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.PhysicalLift
import Mathlib.Tactic.FieldSimp

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [I.Boundaryless] in
private theorem physical_unitTangent_contMDiff (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.physicalLift lambda x t, c.physicalField lambda (c.unitTangent g lambda) x t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  let γ := fun x => c.physicalLift lambda x t
  let X := fun x => mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x (1 : ℝ)
  let Φ := (Diffeomorph.refl I M ∞).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ lambda hlambda.ne').toContinuousLinearEquiv.toDiffeomorph
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ γ :=
    Φ.contMDiff.comp (c.coverLift_space_contMDiff hc t ht)
  have hX : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨γ x, X x⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) :=
    fun x => (hγ x).velocityLift (m := ∞) (by simp)
  have hs := (c.speed_contDiff_of_immersedOn g lambda hlambda hc hi t ht).inv
    (fun x => (c.speed_pos_of_immersedOn g lambda hlambda hi x t ht).ne')
  apply (hs.contMDiff.smul_bundle hX).congr
  intro x
  have heq := c.physicalLift_unitTangent g lambda hlambda.ne' hc t ht x
  dsimp only at heq
  rw [c.physicalLift_speed g lambda hlambda.ne' hc x t ht] at heq
  exact congrArg (fun W => (⟨γ x, W⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) heq.symm

omit [I.Boundaryless] in
private theorem physical_unitTangent_inner_self (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    (coverProductMetric (g t) 1 zero_lt_one).inner (c.physicalLift lambda x t)
      (c.physicalField lambda (c.unitTangent g lambda) x t)
      (c.physicalField lambda (c.unitTangent g lambda) x t) = 1 := by
  let γ := fun x => c.physicalLift lambda x t
  let G := coverProductMetric (g t) 1 zero_lt_one
  let X := mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x (1 : ℝ)
  have hv := c.speed_pos_of_immersedOn g lambda hlambda hi x t ht
  have hs : Real.sqrt (G.inner (γ x) X X) = c.speed g lambda x t :=
    c.physicalLift_speed g lambda hlambda.ne' hc x t ht
  have hn : G.inner (γ x) X X = c.speed g lambda x t ^ 2 := by
    rw [← hs, Real.sq_sqrt (metric_inner_self_nonneg G (γ x) X)]
  have heq := c.physicalLift_unitTangent g lambda hlambda.ne' hc t ht x
  dsimp only at heq
  rw [c.physicalLift_speed g lambda hlambda.ne' hc x t ht] at heq
  rw [← heq]
  change G.inner (γ x) ((c.speed g lambda x t)⁻¹ • X) ((c.speed g lambda x t)⁻¹ • X) = 1
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [hn]
  field_simp

private theorem physical_unitTangent_covariant_norm (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    let γ := fun x => c.physicalLift lambda x t;
    let G := coverProductMetric (g t) 1 zero_lt_one;
    let V := fun x => c.physicalField lambda (c.unitTangent g lambda) x t;
    Real.sqrt (G.inner (γ x) (covDerivAlong G γ V x) (covDerivAlong G γ V x)) =
      c.curvature g lambda x t * c.speed g lambda x t := by
  let γ := fun x => c.physicalLift lambda x t
  let G := coverProductMetric (g t) 1 zero_lt_one
  let V := fun x => c.physicalField lambda (c.unitTangent g lambda) x t
  have hv := c.speed_pos_of_immersedOn g lambda hlambda hi x t ht
  have hDs := c.physicalLift_Ds g lambda hlambda hc t ht (c.unitTangent g lambda)
    (c.cover_unitTangent_contMDiff g lambda hlambda hc hi t ht) x
  dsimp only at hDs
  rw [c.physicalLift_speed g lambda hlambda.ne' hc x t ht] at hDs
  have heq : covDerivAlong G γ V x =
      c.speed g lambda x t • c.physicalField lambda (c.curvatureVector g lambda) x t := by
    calc
      covDerivAlong G γ V x = c.speed g lambda x t •
          ((c.speed g lambda x t)⁻¹ • covDerivAlong G γ V x) := by
        rw [smul_smul, mul_inv_cancel₀ hv.ne', one_smul]
      _ = _ := congrArg (fun W => c.speed g lambda x t • W) hDs
  dsimp only
  change Real.sqrt (G.inner (γ x) (covDerivAlong G γ V x) (covDerivAlong G γ V x)) = _
  rw [heq]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hv.le,
    c.physicalField_normSq g lambda (c.curvatureVector g lambda) x t]
  exact mul_comm _ _

theorem integral_norm_deriv_normalize_physical_unitTangent_le (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ)
    {p q C K : ℝ} (hpq : p ≤ q) (hC : 0 < C) (hK : 0 ≤ K) :
    let γ := fun x => c.physicalLift lambda x t;
    let G := coverProductMetric (g t) 1 zero_lt_one;
    let V := fun x => c.physicalField lambda (c.unitTangent g lambda) x t;
    (∀ x ∈ Icc p q, γ x ∈ (chartAt (ModelProd H ℝ) β).source) →
    (∀ x ∈ Icc p q, ∀ W : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ x),
      Real.sqrt (G.inner (γ x) W W) ≤
        C * ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
          ℝ (γ x) W)‖) →
    (∀ x ∈ Icc p q, ∀ W : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ x),
      ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (γ x) W)‖ ≤ C * Real.sqrt (G.inner (γ x) W W)) →
    (∀ x ∈ Icc p q, ∀ u v : E × ℝ,
      ‖A (chartChristoffelContraction G β u v (chartCurve (I := I.prod 𝓘(ℝ, ℝ)) β γ x))‖ ≤
        K * ‖A u‖ * ‖A v‖) →
    (∫ x in p..q, ‖deriv (fun s => NormedSpace.normalize (A (chartRepAtBase β γ V s))) x‖) ≤
      C ^ 2 * c.arcTotalCurvature g lambda p q t + K * C * c.arcLength g lambda p q t := by
  dsimp only
  intro hβ hlower hupper hΓ
  let γ := fun x => c.physicalLift lambda x t
  let G := coverProductMetric (g t) 1 zero_lt_one
  let V := fun x => c.physicalField lambda (c.unitTangent g lambda) x t
  have hV := physical_unitTangent_contMDiff c g lambda hlambda hc hi t ht
  have h := DifferentialGeometry.Geometry.Riemannian.Variation.integral_norm_deriv_normalize_chartRepAtBase_le
    G A β hpq hC hK (fun x _ => (hV x).of_le (by simp)) hβ
    (fun x _ => physical_unitTangent_inner_self c g lambda hlambda hc hi t ht x) hlower hupper hΓ
  have hcov : (fun x => Real.sqrt (G.inner (γ x) (covDerivAlong G γ V x) (covDerivAlong G γ V x))) =
      fun x => c.curvature g lambda x t * c.speed g lambda x t :=
    funext (physical_unitTangent_covariant_norm c g lambda hlambda hc hi t ht)
  have hspeed : (fun x => Real.sqrt (G.inner (γ x)
      (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x (1 : ℝ)))) = fun x => c.speed g lambda x t :=
    funext (fun x => c.physicalLift_speed g lambda hlambda.ne' hc x t ht)
  rw [hcov, hspeed] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
