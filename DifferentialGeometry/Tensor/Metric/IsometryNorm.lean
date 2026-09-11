import DifferentialGeometry.Tensor.Metric.LocalIsometry
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Tensor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

omit [T2Space N] in
theorem normSq0S_of_metric_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (Φ : M ≃ₘ⟮I, I⟯ N)
    (hmetric : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = h.inner (Φ y) (mfderiv I I (Φ : M → N) y v)
        (mfderiv I I (Φ : M → N) y w)) (r : ℕ) (x : M)
    (A : Tensor0SSpace (I := I) (M := M) r x)
    (B : Tensor0SSpace (I := I) (M := N) r (Φ x))
    (hAB : ∀ v : Fin r → TangentSpace I x,
      A v = B (fun i => mfderiv I I (Φ : M → N) x (v i))) :
    normSq0S g x r A = normSq0S h (Φ x) r B := by
  have hg : g = Diffeomorph.pullbackMetric h Φ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    exact hmetric y v w
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (Diffeomorph.pullbackMetric h Φ) x
  rw [hg]
  exact normSq0S_pullback_eval_of_orthonormal h Φ x r basis hON A B hAB

variable [CompleteSpace E]

theorem normSq0S_iterCov_of_metric_isometry_on_opens
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (Φ : U ≃ₘ⟮I, I⟯ V)
    (hmetric : ∀ (y : U) (v w : TangentSpace I y),
      g.inner (y : M) v w = h.inner (Φ y : N) (mfderiv I I (Φ : U → V) y v)
        (mfderiv I I (Φ : U → V) y w)) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r)
    (B : Tensor0SField (I := I) (M := N) ∞ r)
    (hAB : ∀ (y : U) (v : Fin r → TangentSpace I y),
      A (y : M) v = B (Φ y : N) (fun i => mfderiv I I (Φ : U → V) y (v i)))
    (k : ℕ) (x : U) :
    normSq0S g (x : M) (r + k) (iterCov g r A k (x : M)) =
      normSq0S h (Φ x : N) (r + k) (iterCov h r B k (Φ x : N)) := by
  have hn := normSq0S_of_metric_isometry (g.restrictOpen U) (h.restrictOpen V) Φ
    hmetric (r + k) x (iterCov g r A k (x : M)) (iterCov h r B k (Φ x : N))
    (iter_cov_of_metric_isometry_on_opens g h U V Φ hmetric A B hAB k x)
  exact (normSq0S_restrictOpen_apply g U (r + k) x (iterCov g r A k (x : M))).symm.trans
    (hn.trans (normSq0S_restrictOpen_apply h V (r + k) (Φ x) (iterCov h r B k (Φ x : N))))
end DifferentialGeometry.Geometry.Tensor
