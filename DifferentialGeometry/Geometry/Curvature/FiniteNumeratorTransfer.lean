import DifferentialGeometry.Geometry.Curvature.RiemannPerturbation
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Metric
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric

/-!
# Native finite metric differences and the smooth perturbation sub-tier

The difference tensor is defined for every finite metric order. For smooth metrics its
raw covariant norms equal the existing perturbation norms, without a comparison premise.
-/

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def finiteMetricDifference {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (G : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  ((continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ).symm.toContinuousLinearMap.comp
    (g.inner x - G.inner x)).uncurryLeft

theorem finiteMetricDifference_apply {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (G : SmoothRiemannianMetric I M) (x : M) (slots : Fin 2 → TangentSpace I x) :
    finiteMetricDifference g G x slots =
      g.inner x (slots 0) (slots 1) - G.inner x (slots 0) (slots 1) := by
  rfl

variable [T2Space M]

omit [T2Space M] in
theorem finiteMetricDifference_smooth (g G : SmoothRiemannianMetric I M) (x : M) :
    finiteMetricDifference g G x = (metricTensorField g - metricTensorField G) x := by
  ext slots
  rw [finiteMetricDifference_apply]
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_apply,
    metricTensorField_apply]

theorem finiteMetricDifference_iterated (g G : SmoothRiemannianMetric I M) (k : ℕ) :
    iteratedMetricCovariantDerivative G 2 (finiteMetricDifference g G) k =
      fun x => iterCov G 2 (metricTensorField g - metricTensorField G) k x := by
  induction k with
  | zero => exact funext (finiteMetricDifference_smooth g G)
  | succ k ih =>
      funext x
      rw [iteratedMetricCovariantDerivative, ih, iterCov_succ, covStep_apply]
      rfl

theorem finiteMetricDifference_norm_eq (g G : SmoothRiemannianMetric I M)
    (k : ℕ) (x : M) :
    tensor0SFiberNorm G x (2 + k)
      (iteratedMetricCovariantDerivative G 2 (finiteMetricDifference g G) k x) =
      metricDerivNorm k g G G x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis G x
  have hinv : MetricInverseInBasis G x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal G basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  rw [metricDerivNorm_eq_iterCov g G G k basis hinv,
    tensor0SFiberNorm, finiteMetricDifference_iterated]

variable [I.Boundaryless]

theorem abs_numerator_sub_le_of_smooth_metric
    (g G : SmoothRiemannianMetric I M) (x : M) {ε K : ℝ} (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → tensor0SFiberNorm G x (2 + k)
      (iteratedMetricCovariantDerivative G 2 (finiteMetricDifference g G) k x) ≤ ε)
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (v w : TangentSpace I x) :
    |metricRm04StandardAt g x v w w v - metricRm04StandardAt G x v w w v| ≤
      ε * (360 + K) * G.inner x v v * G.inner x w w := by
  have hsmall' (k : ℕ) (hk : k ≤ 2) : metricDerivNorm k g G G x ≤ ε := by
    rw [← finiteMetricDifference_norm_eq]
    exact hsmall k hk
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall' 0 (by norm_num))
  have h := abs_metricRm04_sub_le_of_small_metric_derivatives g G x hε hsmall' v w w v
  apply h.trans
  have hR := hmodel v w w
  dsimp only at hR
  calc
    ε * (360 * Real.sqrt (G.inner x v v) * Real.sqrt (G.inner x w w) *
        Real.sqrt (G.inner x w w) +
        Real.sqrt (G.inner x (riemannOp (LeviCivita G) x v w w)
          (riemannOp (LeviCivita G) x v w w))) * Real.sqrt (G.inner x v v)
      ≤ ε * (360 * Real.sqrt (G.inner x v v) * Real.sqrt (G.inner x w w) *
        Real.sqrt (G.inner x w w) +
        K * Real.sqrt (G.inner x v v) * Real.sqrt (G.inner x w w) *
          Real.sqrt (G.inner x w w)) * Real.sqrt (G.inner x v v) := by
            gcongr
    _ = ε * (360 + K) * (Real.sqrt (G.inner x v v)) ^ 2 *
        (Real.sqrt (G.inner x w w)) ^ 2 := by ring
    _ = _ := by
      rw [Real.sq_sqrt (metric_inner_self_nonneg G x v),
        Real.sq_sqrt (metric_inner_self_nonneg G x w)]

end DifferentialGeometry.Geometry.Curvature
