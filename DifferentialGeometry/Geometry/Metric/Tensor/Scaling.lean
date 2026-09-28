import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem sqrt_normSq0S_scaleMetric_sq (g : SmoothRiemannianMetric I M)
    (h : ℝ) (hh : 0 < h) (r : ℕ) (x : M) (A : Tensor0SSpace (I := I) r x) :
    Real.sqrt (normSq0S (scaleMetric (h ^ 2) (sq_pos_of_pos hh) g) x r A) =
      (h⁻¹) ^ r * Real.sqrt (normSq0S g x r A) := by
  rw [normSq0S_scale, ← inv_pow h 2]
  have hpow : ((h⁻¹) ^ 2) ^ r = ((h⁻¹) ^ r) ^ 2 := by ring
  rw [hpow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (inv_nonneg.mpr hh.le) r)]

variable [CompleteSpace E] [T2Space M]

private theorem covStep_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (r : ℕ) (A : Tensor0SField (I := I) (M := M) ∞ r) :
    covStep (scaleMetric c hc g) r A = covStep g r A := by
  apply DFunLike.ext
  intro x
  rw [covStep_apply, covStep_apply, lcConn_scaleMetric]

theorem iterCov_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (r : ℕ) (A : Tensor0SField (I := I) (M := M) ∞ r) (k : ℕ) :
    iterCov (scaleMetric c hc g) r A k = iterCov g r A k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterCov_succ, iterCov_succ, ih, covStep_scaleMetric]

theorem iterCov_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (r : ℕ) (A : Tensor0SField (I := I) (M := M) ∞ r) (k : ℕ) :
    iterCov g r (c • A) k = c • iterCov g r A k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterCov_succ, iterCov_succ, ih, covStep_smul]

theorem iterCov_metricRm04_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (k : ℕ) :
    iterCov (scaleMetric c hc g) 4 (metricRm04 (scaleMetric c hc g)) k =
      c • iterCov g 4 (metricRm04 g) k := by
  have hRm : metricRm04 (scaleMetric c hc g) = c • metricRm04 g := by
    apply DFunLike.ext
    intro x
    exact metricRm_scale c hc g x
  rw [hRm, iterCov_scaleMetric, iterCov_smul]

theorem sqrt_normSq0S_iterCov_metricRm04_scaleMetric_sq
    (g : SmoothRiemannianMetric I M) (h : ℝ) (hh : 0 < h) (k : ℕ) (x : M) :
    Real.sqrt (normSq0S (scaleMetric (h ^ 2) (sq_pos_of_pos hh) g) x (4 + k)
      (iterCov (scaleMetric (h ^ 2) (sq_pos_of_pos hh) g) 4
        (metricRm04 (scaleMetric (h ^ 2) (sq_pos_of_pos hh) g)) k x)) =
      (h⁻¹) ^ (2 + k) * Real.sqrt (normSq0S g x (4 + k) (iterCov g 4 (metricRm04 g) k x)) := by
  rw [iterCov_metricRm04_scaleMetric]
  change Real.sqrt (normSq0S (scaleMetric (h ^ 2) (sq_pos_of_pos hh) g) x (4 + k)
    (h ^ 2 • iterCov g 4 (metricRm04 g) k x)) = _
  rw [sqrt_normSq0S_scaleMetric_sq g h hh, sqrt_normSq0S_smul,
    abs_of_pos (sq_pos_of_pos hh)]
  have hfactor : (h⁻¹) ^ (4 + k) * h ^ 2 = (h⁻¹) ^ (2 + k) := by
    rw [pow_add, pow_add]
    field_simp
  rw [← mul_assoc, hfactor]

end DifferentialGeometry.Geometry.Tensor
