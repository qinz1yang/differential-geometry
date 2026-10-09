import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormTensor
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Covariant
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Product

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def curvatureSlotEquiv : (k : ℕ) → Fin (4 + k) ≃ Fin (k + 4)
  | 0 => Equiv.refl _
  | k + 1 => frontExtendEquiv (curvatureSlotEquiv k)

private theorem curvCovDeriv_eq_iterCov_zero (g : SmoothRiemannianMetric I M) :
    curvCovDeriv g 0 = Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (curvatureSlotEquiv 0) (iterCov g 4 (metricRm04 g) 0) := by
  change metricRm04 g =
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (Equiv.refl _) (metricRm04 g)
  exact (Tensor0SField.domDomCongr_refl (∞ : WithTop ℕ∞) (metricRm04 g)).symm

private theorem curvCovDeriv_eq_iterCov_succ (g : SmoothRiemannianMetric I M) (k : ℕ)
    (ih : curvCovDeriv g k = Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (curvatureSlotEquiv k) (iterCov g 4 (metricRm04 g) k)) :
    curvCovDeriv g (k + 1) = Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (curvatureSlotEquiv (k + 1)) (iterCov g 4 (metricRm04 g) (k + 1)) := by
  calc
    curvCovDeriv g (k + 1) = curvCovDerivStep g k (curvCovDeriv g k) :=
      curvCovDeriv_succ g k
    _ = covStep g (k + 4) (curvCovDeriv g k) :=
      curvStep_eq_covStep g k (curvCovDeriv g k)
    _ = covStep g (k + 4) (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        (curvatureSlotEquiv k) (iterCov g 4 (metricRm04 g) k)) :=
      congrArg (covStep g (k + 4)) ih
    _ = Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        (frontExtendEquiv (curvatureSlotEquiv k))
        (covStep g (4 + k) (iterCov g 4 (metricRm04 g) k)) :=
      covStep_domDomCongr g (curvatureSlotEquiv k) (iterCov g 4 (metricRm04 g) k)
    _ = Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        (curvatureSlotEquiv (k + 1)) (iterCov g 4 (metricRm04 g) (k + 1)) :=
      congrArg (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        (frontExtendEquiv (curvatureSlotEquiv k)))
        (iterCov_succ g 4 (metricRm04 g) k).symm

private theorem curvCovDeriv_eq_iterCov (g : SmoothRiemannianMetric I M) (k : ℕ) :
    curvCovDeriv g k = Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (curvatureSlotEquiv k) (iterCov g 4 (metricRm04 g) k) := by
  induction k with
  | zero => exact curvCovDeriv_eq_iterCov_zero g
  | succ k ih => exact curvCovDeriv_eq_iterCov_succ g k ih

/-- The raw curvature derivative norm and the bundled Cheeger--Gromov norm
measure the same tensor, with the same metric at the same point. Their slot
arities differ only by the permutation extended at each derivative step. -/
theorem curvatureDerivativeNorm_eq_curvDerivNorm
    (g : SmoothRiemannianMetric I M) (k : ℕ) (x : M) :
    curvatureDerivativeNorm g k x = curvDerivNorm k g x := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis g x
  have hinv : MetricInverseInBasis g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  unfold curvatureDerivativeNorm tensor0SFiberNorm curvDerivNorm curvDerivNormSq
  rw [iteratedMetricCovariantDerivative_rm04_eq, iteratedCurvatureTensor_eq_iterCov,
    curvCovDeriv_eq_iterCov, Tensor0SField.domDomCongr_apply]
  exact congrArg Real.sqrt
    (normSq0S_domDomCongr g x basis hinv (curvatureSlotEquiv k)
      (iterCov g 4 (metricRm04 g) k x)).symm

end DifferentialGeometry.Geometry.Curvature
