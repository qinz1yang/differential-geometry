import DifferentialGeometry.Tensor.Metric.ScaleNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Polar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Tensor
open scoped Manifold ContDiff InnerProductSpace ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Sphere2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def scaledPolarDiffeomorph (h : ℝ) (hh : 0 < h) :
    PartialDiffeomorph IC (𝓡 3) (Sphere2 × ℝ) E3 ∞ :=
  (euclideanPolarDiffeomorph (n := 2)).trans
    ((LinearEquiv.smulOfNeZero ℝ E3 h⁻¹ (inv_ne_zero hh.ne')).toContinuousLinearEquiv.toDiffeomorph.toPartialDiffeomorph)

@[simp] theorem scaledPolarDiffeomorph_apply (h : ℝ) (hh : 0 < h) (q : Sphere2 × ℝ) :
    scaledPolarDiffeomorph h hh q = (q.2 / h) • (q.1 : E3) := by
  change h⁻¹ • (q.2 • (q.1 : E3)) = _
  rw [smul_smul, div_eq_mul_inv, mul_comm]

@[simp] theorem scaledPolarDiffeomorph_source (h : ℝ) (hh : 0 < h) :
    (scaledPolarDiffeomorph h hh).source = {q | 0 < q.2} := by
  ext q
  change (0 < q.2 ∧ euclideanPolarMap q ∈ (Set.univ : Set E3)) ↔ 0 < q.2
  simp only [mem_univ, and_true]

@[simp] theorem scaledPolarDiffeomorph_target (h : ℝ) (hh : 0 < h) :
    (scaledPolarDiffeomorph h hh).target = {0}ᶜ := by
  ext x
  change (x ∈ (Set.univ : Set E3) ∧ (h⁻¹)⁻¹ • x ≠ 0) ↔ x ≠ 0
  simp only [mem_univ, inv_inv, smul_ne_zero_iff, true_and]
  exact and_iff_right hh.ne'

private theorem scaledPolarDiffeomorph_mfderiv (h : ℝ) (hh : 0 < h)
    (q : Sphere2 × ℝ) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (scaledPolarDiffeomorph h hh) q v =
      (v.2 / h) • (q.1 : E3) + (q.2 / h) • dIncl q.1 v.1 := by
  change mfderiv IC (𝓡 3) (h⁻¹ • euclideanPolarMap) q v = _
  rw [const_smul_mfderiv ((euclideanPolarMap_smooth (n := 2)).mdifferentiable (by decide) q)]
  change h⁻¹ • (mfderiv IC (𝓡 3) euclideanPolarMap q v) = _
  rw [euclideanPolarMap_mfderiv q v]
  have halg (a b : ℝ) (u z : E3) :
      h⁻¹ • (a • u + b • z) = (a / h) • u + (b / h) • z := by
    simp only [smul_add, smul_smul, div_eq_mul_inv, mul_comm]
  exact halg v.2 q.2 q.1 (dIncl q.1 v.1)

theorem scaleMetric_inner_polar (h : ℝ) (hh : 0 < h)
    {e : E3} (he : ‖e‖ = 1) {v w : E3} (hv : ⟪e, v⟫_ℝ = 0) (hw : ⟪e, w⟫_ℝ = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (s t : ℝ) :
    (scaleMetric (h ^ 2) (sq_pos_of_pos hh) metric).inner ((ρ / h) • e)
      ((s / h) • e + (ρ / h) • v) ((t / h) • e + (ρ / h) • w) =
      s * t + (h * warpingFunction (ρ / h)) ^ 2 * ⟪v, w⟫_ℝ := by
  rw [scaleMetric_inner (h ^ 2) (sq_pos_of_pos hh) metric ((ρ / h) • e)
    ((s / h) • e + (ρ / h) • v) ((t / h) • e + (ρ / h) • w),
    metric_inner_polar he hv hw (div_pos hρ hh)]
  field_simp

theorem scaleMetric_polar_pullback (h : ℝ) (hh : 0 < h)
    (q : Sphere2 × ℝ) (hq : 0 < q.2) (v w : TangentSpace IC q) :
    (scaleMetric (h ^ 2) (sq_pos_of_pos hh) metric).inner (scaledPolarDiffeomorph h hh q)
      (mfderiv IC (𝓡 3) (scaledPolarDiffeomorph h hh) q v)
      (mfderiv IC (𝓡 3) (scaledPolarDiffeomorph h hh) q w) =
      (h * warpingFunction (q.2 / h)) ^ 2 * (roundMetric (E := E3) (n := 2)).inner q.1 v.1 w.1 +
        v.2 * w.2 := by
  rw [scaledPolarDiffeomorph_mfderiv h hh q v,
    scaledPolarDiffeomorph_mfderiv h hh q w, scaledPolarDiffeomorph_apply h hh q,
    scaleMetric_inner_polar h hh (norm_eq_of_mem_sphere q.1)
      (dIncl_orth q.1 v.1) (dIncl_orth q.1 w.1) hq, roundMetric_inner q.1 v.1 w.1]
  ring

theorem riemannianEDistOf_scaleMetric (h : ℝ) (hh : 0 < h) (x y : E3) :
    riemannianEDistOf (scaleMetric (h ^ 2) (sq_pos_of_pos hh) metric) x y =
      ENNReal.ofReal h * riemannianEDistOf metric x y := by
  rw [edistOf_scale, Real.sqrt_sq hh.le]

theorem distance_scaleMetric (h : ℝ) (hh : 0 < h) (x y : E3) :
    (riemannianEDistOf (scaleMetric (h ^ 2) (sq_pos_of_pos hh) metric) x y).toReal =
      h * (riemannianEDistOf metric x y).toReal := by
  rw [riemannianEDistOf_scaleMetric h hh, ENNReal.toReal_mul, ENNReal.toReal_ofReal hh.le]

theorem distance_scaledPolarDiffeomorph (h : ℝ) (hh : 0 < h)
    (q : Sphere2 × ℝ) (hq : 0 < q.2) :
    (riemannianEDistOf (scaleMetric (h ^ 2) (sq_pos_of_pos hh) metric) 0
      (scaledPolarDiffeomorph h hh q)).toReal = q.2 := by
  rw [distance_scaleMetric h hh, distance_zero, scaledPolarDiffeomorph_apply,
    norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hq hh), norm_eq_of_mem_sphere, mul_one]
  field_simp

theorem metricScalarAt_scale (h : ℝ) (hh : 0 < h) (x : E3) :
    metricScalarAt (scaleMetric (h ^ 2) (sq_pos_of_pos hh) metric) x =
      (h⁻¹) ^ 2 * metricScalarAt metric x := by
  rw [DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric, inv_pow]

theorem norm_iterCov_metricRm04_scale (h : ℝ) (hh : 0 < h) (k : ℕ) (x : E3) :
    Real.sqrt (normSq0S (scaleMetric (h ^ 2) (sq_pos_of_pos hh) metric) x (4 + k)
      (iterCov (scaleMetric (h ^ 2) (sq_pos_of_pos hh) metric) 4
        (metricRm04 (scaleMetric (h ^ 2) (sq_pos_of_pos hh) metric)) k x)) =
      (h⁻¹) ^ (2 + k) * Real.sqrt
        (normSq0S metric x (4 + k) (iterCov metric 4 (metricRm04 metric) k x)) :=
  sqrt_normSq0S_iterCov_metricRm04_scaleMetric_sq metric h hh k x

end DifferentialGeometry.PDE.RicciFlow.StandardCap
