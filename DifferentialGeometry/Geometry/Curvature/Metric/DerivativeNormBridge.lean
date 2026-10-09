import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNorm
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormCompatibility

/-!
# Bridge between the two curvature-derivative norms

Two towers of covariant derivatives of the `(0,4)` curvature tensor coexist:

* `iteratedCurvatureTensor g k : Tensor0SField (4 + k)` (`Geometry/Curvature/Metric/DerivativeNorm.lean`),
  behind `curvatureDerivativeNorm g k x`, used by the Collapse vocabulary;
* `CheegerGromovCompactness.curvCovDeriv g k : Tensor0SField (k + 4)`
  (`Geometry/Curvature/CurvatureOperator/Derivatives/Norm.lean`), behind `curvDerivNorm k g x`, used by the
  compactness and Shi interfaces.

Both are iterates of the total covariant derivative of the Levi-Civita connection starting from
`metricRm04 g`; only the arity is written `4 + k` in one tower and `k + 4` in the other. We compare
the *tensor fields* (heterogeneously, across `4 + k = k + 4`), not notation:

* `curvCovDeriv_heq_iteratedCurvatureTensor`: the two towers agree as sections;
* T1 `curvatureDerivativeNorm_eq_curvDerivNorm` (ported, `DerivativeNormCompatibility.lean`): the
  two norms agree pointwise;
* T2 `curvatureDerivativeNorm_scaleMetric_div`: `|∇^k Rm|_{c g} = |∇^k Rm|_g / (c · (√c)^k)`, transported
  from `curvDerivNorm_scaleMetric` (`…/Derivatives/Scaling.lean`).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
/-- One step of the `DerivativeNorm` tower is the compactness-side covariant step `covStep`. -/
theorem iteratedCurvatureTensor_succ_eq_covStep (g : SmoothRiemannianMetric I M) (k : ℕ) :
    iteratedCurvatureTensor g (k + 1) =
      CheegerGromovCompactness.covStep g (4 + k) (iteratedCurvatureTensor g k) := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [CheegerGromovCompactness.covStep_apply]
  rfl

omit [SigmaCompactSpace M] in
/-- `covStep` respects heterogeneous equality of sections across an arity equation. -/
theorem covStep_heq_of_heq (g : SmoothRiemannianMetric I M) {s s' : ℕ} (hs : s = s')
    {A : Tensor0SField (I := I) (M := M) (n := ∞) s}
    {B : Tensor0SField (I := I) (M := M) (n := ∞) s'} (hAB : HEq A B) :
    HEq (CheegerGromovCompactness.covStep g s A) (CheegerGromovCompactness.covStep g s' B) := by
  subst hs
  cases eq_of_heq hAB
  rfl

omit [SigmaCompactSpace M] in
/-- The two curvature-derivative towers agree as tensor fields (arities `k + 4` and `4 + k`). -/
theorem curvCovDeriv_heq_iteratedCurvatureTensor (g : SmoothRiemannianMetric I M) (k : ℕ) :
    HEq (CheegerGromovCompactness.curvCovDeriv g k) (iteratedCurvatureTensor g k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [CheegerGromovCompactness.curvCovDeriv_succ, CheegerGromovCompactness.curvStep_eq_covStep,
      iteratedCurvatureTensor_succ_eq_covStep]
    exact covStep_heq_of_heq g (Nat.add_comm k 4) ih

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
/-- The fibre norm square of heterogeneously equal sections agrees. -/
theorem normSq0S_apply_eq_of_heq (g : SmoothRiemannianMetric I M) (x : M) {s s' : ℕ}
    (hs : s = s') {A : Tensor0SField (I := I) (M := M) (n := ∞) s}
    {B : Tensor0SField (I := I) (M := M) (n := ∞) s'} (hAB : HEq A B) :
    normSq0S g x s (A x) = normSq0S g x s' (B x) := by
  subst hs
  cases eq_of_heq hAB
  rfl

omit [SigmaCompactSpace M] in
/-- Square form of T1. -/
theorem curvatureDerivativeNorm_sq_eq_curvDerivNormSq (g : SmoothRiemannianMetric I M) (k : ℕ)
    (x : M) :
    curvatureDerivativeNorm g k x ^ 2 = CheegerGromovCompactness.curvDerivNormSq k g x := by
  rw [curvatureDerivativeNorm_sq_eq_normSq0S, iteratedMetricCovariantDerivative_rm04_eq,
    CheegerGromovCompactness.curvDerivNormSq]
  exact normSq0S_apply_eq_of_heq g x (Nat.add_comm 4 k)
    (curvCovDeriv_heq_iteratedCurvatureTensor g k).symm

omit [SigmaCompactSpace M] in
/-- **T2.** Scaling of the Collapse-side curvature-derivative norm:
`|∇^k Rm|_{c g} = |∇^k Rm|_g / (c · (√c)^k)`. -/
theorem curvatureDerivativeNorm_scaleMetric_div (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (k : ℕ) (x : M) :
    curvatureDerivativeNorm (scaleMetric c hc g) k x =
      curvatureDerivativeNorm g k x / (c * Real.sqrt c ^ k) := by
  rw [curvatureDerivativeNorm_eq_curvDerivNorm, curvatureDerivativeNorm_eq_curvDerivNorm,
    CheegerGromovCompactness.curvDerivNorm_scaleMetric]

end DifferentialGeometry.Geometry.Curvature
