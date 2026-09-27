import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : CompleteSpace F := FiniteDimensional.complete ℝ F

theorem curvatureOperatorLowerBoundAt_iff_of_metricRm04StdAt_equiv
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M) (y : N) (e : TangentSpace I x ≃ₗ[ℝ] TangentSpace J y)
    (hmetric : ∀ u v : TangentSpace I x, g.inner x u v = h.inner y (e u) (e v))
    (hRm : ∀ u v w z : TangentSpace I x,
      metricRm04StandardAt g x u v w z = metricRm04StandardAt h y (e u) (e v) (e w) (e z))
    (K : ℝ) :
    curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) K ↔
      curvatureOperatorLowerBoundAt h y (metricAlgebraicCurvatureTensorAt h y) K := by
  have hquad (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
      algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt g x) c v w +
          K * algebraicCurvatureIdentityQuadraticEval g c v w =
        algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt h y) c
            (fun i => e (v i)) (fun i => e (w i)) +
          K * algebraicCurvatureIdentityQuadraticEval h c
            (fun i => e (v i)) (fun i => e (w i)) := by
    change (∑ i, ∑ j, c i * c j * metricRm04StandardAt g x (v i) (w i) (w j) (v j)) +
        K * (∑ i, ∑ j, c i * c j *
          (g.inner x (v i) (v j) * g.inner x (w i) (w j) -
            g.inner x (v i) (w j) * g.inner x (w i) (v j))) =
      (∑ i, ∑ j, c i * c j * metricRm04StandardAt h y (e (v i)) (e (w i)) (e (w j)) (e (v j))) +
        K * (∑ i, ∑ j, c i * c j *
          (h.inner y (e (v i)) (e (v j)) * h.inner y (e (w i)) (e (w j)) -
            h.inner y (e (v i)) (e (w j)) * h.inner y (e (w i)) (e (v j))))
    simp_rw [hRm, hmetric]
  constructor
  · intro hg n c v w
    have ht := hg n c (fun i => e.symm (v i)) (fun i => e.symm (w i))
    rw [hquad] at ht
    simpa only [LinearEquiv.apply_symm_apply] using ht
  · intro hh n c v w
    rw [hquad]
    exact hh n c (fun i => e (v i)) (fun i => e (w i))

theorem leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M) (y : N) (e : TangentSpace I x ≃ₗ[ℝ] TangentSpace J y)
    (hmetric : ∀ u v : TangentSpace I x, g.inner x u v = h.inner y (e u) (e v))
    (hRm : ∀ u v w z : TangentSpace I x,
      metricRm04StandardAt g x u v w z = metricRm04StandardAt h y (e u) (e v) (e w) (e z)) :
    leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) =
      leastCurvatureOperatorEigenvalueAt h y (metricAlgebraicCurvatureTensorAt h y) := by
  have hsets : {K : ℝ | curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) K} =
      {K : ℝ | curvatureOperatorLowerBoundAt h y (metricAlgebraicCurvatureTensorAt h y) K} := by
    ext K
    exact curvatureOperatorLowerBoundAt_iff_of_metricRm04StdAt_equiv g h x y e hmetric hRm K
  exact congrArg (fun s : Set ℝ => -sInf s) hsets

theorem leastCurvatureOperatorEigenvalueAt_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) :
    leastCurvatureOperatorEigenvalueAt (Diffeomorph.pullbackMetricCross g Φ) x
        (metricAlgebraicCurvatureTensorAt (Diffeomorph.pullbackMetricCross g Φ) x) =
      leastCurvatureOperatorEigenvalueAt g (Φ x) (metricAlgebraicCurvatureTensorAt g (Φ x)) := by
  let e := (Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : ℕ∞ω) ≠ 0) x).toLinearEquiv
  have he (v : TangentSpace I x) : e v = mfderiv I J Φ x v := by
    exact congrArg (fun D : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) => D v)
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) (by decide))
  apply leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv
    (Diffeomorph.pullbackMetricCross g Φ) g x (Φ x) e
  · intro u v
    simpa only [he] using Diffeomorph.pullbackMetricCross_inner g Φ x u v
  · intro u v w z
    simpa only [he] using metricRm04Standard_pullbackCross g Φ x u v w z

theorem leastCurvatureOperatorEigenvalueAt_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : Opens M) [SigmaCompactSpace U] (x : U) :
    leastCurvatureOperatorEigenvalueAt (g.restrictOpen U) x
        (metricAlgebraicCurvatureTensorAt (g.restrictOpen U) x) =
      leastCurvatureOperatorEigenvalueAt g (x : M) (metricAlgebraicCurvatureTensorAt g (x : M)) := by
  apply leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv
    (g.restrictOpen U) g x (x : M) (LinearEquiv.refl ℝ E)
  · intro u v
    rfl
  · intro u v w z
    change metricRm04StandardAt (g.restrictOpen U) x u v w z = metricRm04StandardAt g (x : M) u v w z
    simpa only [mfderiv_subtype_val_apply] using
      metricRm04StandardAt_restrictOpen g U x u v w z

theorem leastCurvatureOperatorEigenvalueAt_pullbackMetricOfInjectiveLocalDiffeomorph
    [SigmaCompactSpace M] (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) (x : M) :
    leastCurvatureOperatorEigenvalueAt (pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj) x
        (metricAlgebraicCurvatureTensorAt (pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj) x) =
      leastCurvatureOperatorEigenvalueAt g (f x) (metricAlgebraicCurvatureTensorAt g (f x)) := by
  let Φ := diffeomorphOntoImage f hf hinj
  have hrange : Set.range Φ = Set.univ := Φ.surjective.range_eq
  let : SigmaCompactSpace hf.image := isSigmaCompact_univ_iff.mp
    (hrange ▸ isSigmaCompact_range Φ.continuous)
  rw [pullbackMetricOfInjectiveLocalDiffeomorph,
    leastCurvatureOperatorEigenvalueAt_pullbackMetricCross,
    leastCurvatureOperatorEigenvalueAt_restrictOpen, diffeomorphOntoImage_apply]

end DifferentialGeometry.Geometry.Curvature
