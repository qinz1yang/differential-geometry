import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Metric
import DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.TotalNabla0S
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity
import DifferentialGeometry.Geometry.Operator.CovariantTensor
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

def curvatureDerivativeNorm (g : SmoothRiemannianMetric I M) (k : ℕ) (x : M) : ℝ :=
  tensor0SFiberNorm g x (4 + k)
    (iteratedMetricCovariantDerivative g 4 (metricRm04At g) k x)

omit [T2Space M] [SigmaCompactSpace M] in
theorem curvatureDerivativeNorm_zero (g : SmoothRiemannianMetric I M) (x : M) :
    curvatureDerivativeNorm g 0 x = tensor04FiberNorm g x (metricRm04At g x) := rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem curvatureDerivativeNorm_nonneg (g : SmoothRiemannianMetric I M) (k : ℕ) (x : M) :
    0 ≤ curvatureDerivativeNorm g k x := Real.sqrt_nonneg _

omit [T2Space M] [SigmaCompactSpace M] in
theorem curvatureDerivativeNorm_sq_eq_normSq0S (g : SmoothRiemannianMetric I M) (k : ℕ) (x : M) :
    curvatureDerivativeNorm g k x ^ 2 = normSq0S g x (4 + k)
      (iteratedMetricCovariantDerivative g 4 (metricRm04At g) k x) :=
  tensor0SFiberNorm_sq_eq_normSq0S g x _ _

def iteratedCurvatureTensor (g : SmoothRiemannianMetric I M) :
    (k : ℕ) → Tensor0SField (I := I) (M := M) (n := ∞) (4 + k)
  | 0 => metricRm04 g
  | k + 1 => totalNabla0S (4 + k) (metricCov g) (iteratedCurvatureTensor g k)
      (totalNabla0S_regularity (4 + k) (metricCov g) (metricCov_smooth g)
        (iteratedCurvatureTensor g k))

omit [SigmaCompactSpace M] in
theorem iteratedMetricCovariantDerivative_rm04_eq (g : SmoothRiemannianMetric I M)
    (k : ℕ) (x : M) :
    iteratedMetricCovariantDerivative g 4 (metricRm04At g) k x = iteratedCurvatureTensor g k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change metricCovariantDerivative g (4 + k)
      (iteratedMetricCovariantDerivative g 4 (metricRm04At g) k) x = _
    have heq : iteratedMetricCovariantDerivative g 4 (metricRm04At g) k =
        fun y => iteratedCurvatureTensor g k y := by
      funext y
      exact ih y
    rw [heq]
    rfl

omit [SigmaCompactSpace M] in
theorem continuous_curvatureDerivativeNorm (g : SmoothRiemannianMetric I M) (k : ℕ) :
    Continuous (curvatureDerivativeNorm g k) := by
  have h := Real.continuous_sqrt.comp (normSq0S_cont g (iteratedCurvatureTensor g k))
  change Continuous (fun x => Real.sqrt (normSq0S g x (4 + k)
    (iteratedMetricCovariantDerivative g 4 (metricRm04At g) k x)))
  simpa only [Function.comp_def, iteratedMetricCovariantDerivative_rm04_eq] using h


omit [SigmaCompactSpace M] in
theorem exists_bound_curvatureDerivativeNorm_of_compactSpace [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, k ≤ K → ∀ x : M, curvatureDerivativeNorm g k x ≤ B := by
  classical
  have hbound : ∀ k : ℕ, ∃ C : ℝ, ∀ x : M, curvatureDerivativeNorm g k x ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image (continuous_curvatureDerivativeNorm g k).continuousOn
    exact ⟨C, fun x => hC (Set.mem_image_of_mem _ (Set.mem_univ x))⟩
  choose C hC using hbound
  refine ⟨∑ k ∈ Finset.range (K + 1), max 0 (C k), ?_, ?_⟩
  · exact Finset.sum_nonneg fun k _ => le_max_left _ _
  · intro k hk x
    exact (hC k x).trans ((le_max_right _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_left 0 (C j)) (Finset.mem_range.mpr (by omega))))

end DifferentialGeometry.Geometry.Curvature
