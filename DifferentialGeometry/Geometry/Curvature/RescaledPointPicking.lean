import DifferentialGeometry.Geometry.Curvature.ScalarPointPicking
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem exists_rescaled_scalar_point_selection
    {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
    [∀ n, IsManifold I ∞ (M n)] [∀ n, T2Space (M n)] [∀ n, PreconnectedSpace (M n)]
    (g : ∀ n, SmoothRiemannianMetric I (M n)) (p y : ∀ n, M n)
    (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) {D : ℝ} (hD : 0 ≤ D)
    (hcompact : ∀ n, IsCompact
      (riemannianClosedBallOf (scaleMetric (A n) (hA n) (g n)) (p n) (D + 1)))
    (hy : ∀ n, riemannianEDistOf (scaleMetric (A n) (hA n) (g n)) (p n) (y n) ≤ ENNReal.ofReal D)
    (hfy : ∀ n, 0 < metricScalarAt (g n) (y n))
    (hlim : Tendsto (fun n => metricScalarAt (g n) (y n) / A n) atTop atTop) :
    ∃ (x : ∀ n, M n) (r : ℕ → ℝ),
      (∀ n, 0 < r n ∧ r n < (D + 1)/Real.sqrt (A n) ∧
        riemannianEDistOf (g n) (p n) (x n) < ENNReal.ofReal ((D + 1)/Real.sqrt (A n)) ∧
        0 < metricScalarAt (g n) (x n)) ∧
      Tendsto (fun n => metricScalarAt (g n) (x n) / A n) atTop atTop ∧
      Tendsto (fun n => metricScalarAt (g n) (x n) * r n ^ 2) atTop atTop ∧
      (∀ n, IsCompact (riemannianClosedBallOf (g n) (x n) (r n))) ∧
      ∀ n z, z ∈ riemannianClosedBallOf (g n) (x n) (r n) →
        riemannianEDistOf (g n) (p n) z < ENNReal.ofReal ((D + 1)/Real.sqrt (A n)) ∧
          metricScalarAt (g n) z ≤ (16/9 : ℝ) * metricScalarAt (g n) (x n) := by
  let gn := fun n => scaleMetric (A n) (hA n) (g n)
  have hsc (n : ℕ) (z : M n) : metricScalarAt (gn n) z = metricScalarAt (g n) z / A n := by
    rw [metricScalarAt_scaleMetric,inv_mul_eq_div]
  have hpositive (n : ℕ) : 0 < metricScalarAt (gn n) (y n) := by rw [hsc]; exact div_pos (hfy n) (hA n)
  obtain ⟨x,r,hr,hQ,hQr,_,_,hcpt,hbound⟩ :=
    exists_scalar_point_selection_of_tendsto_atTop_on_compact_balls gn p y hD hcompact hy
      hpositive (by simpa only [hsc] using hlim)
  have hd (n : ℕ) (z : M n) :
      (riemannianEDistOf (gn n) (p n) z).toReal < D+1 →
        riemannianEDistOf (g n) (p n) z < ENNReal.ofReal ((D + 1)/Real.sqrt (A n)) := by
    intro hz
    have hz' : riemannianEDistOf (gn n) (p n) z < ENNReal.ofReal (D + 1) :=
      (ENNReal.lt_ofReal_iff_toReal_lt (riemannianEDistOf_ne_top (gn n) (p n) z)).mpr hz
    have hsqrt : 0 < Real.sqrt (A n) := Real.sqrt_pos.mpr (hA n)
    rw [show riemannianEDistOf (gn n) (p n) z =
      ENNReal.ofReal (Real.sqrt (A n))*riemannianEDistOf (g n) (p n) z from edistOf_scale _ _ _ _ _] at hz'
    apply (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr hsqrt) ENNReal.ofReal_ne_top).mp
    rw [← ENNReal.ofReal_mul hsqrt.le]
    have heq : Real.sqrt (A n)*((D + 1)/Real.sqrt (A n)) = D+1 := by field_simp
    rwa [heq]
  have hball (n : ℕ) : riemannianClosedBallOf (gn n) (x n) (r n) =
      riemannianClosedBallOf (g n) (x n) (r n / Real.sqrt (A n)) := by
    have hh := riemannianClosedBallOf_scaleMetric (A n) (hA n) (g n) (x n) (r n/Real.sqrt (A n))
    have heq : Real.sqrt (A n)*(r n/Real.sqrt (A n)) = r n := by field_simp [(Real.sqrt_pos.mpr (hA n)).ne']
    rwa [heq] at hh
  refine ⟨x,fun n => r n / Real.sqrt (A n),?_,?_,?_,?_,?_⟩
  · intro n
    have hsqrt := Real.sqrt_pos.mpr (hA n)
    refine ⟨div_pos (hr n).1 hsqrt,div_lt_div_of_pos_right (hr n).2.1 hsqrt,
      hd n (x n) (hr n).2.2.1,?_⟩
    have hpos := (hr n).2.2.2
    rw [hsc] at hpos
    exact (div_pos_iff_of_pos_right (hA n)).mp hpos
  · simpa only [hsc] using hQ
  · apply hQr.congr'
    refine Eventually.of_forall fun n => ?_
    change metricScalarAt (gn n) (x n) * r n^2 =
      metricScalarAt (g n) (x n) * (r n / Real.sqrt (A n))^2
    rw [hsc,div_pow,Real.sq_sqrt (hA n).le]
    ring
  · intro n
    rw [← hball]
    exact hcpt n
  · intro n z hz
    rw [← hball] at hz
    have hz' : (riemannianEDistOf (gn n) (x n) z).toReal ≤ r n :=
      ENNReal.toReal_le_of_le_ofReal (hr n).1.le hz
    have hb := hbound n z hz'
    refine ⟨hd n z hb.1,?_⟩
    simp only [hsc] at hb
    have hh := mul_le_mul_of_nonneg_right hb.2 (hA n).le
    simpa only [div_mul_cancel₀ _ (hA n).ne',mul_assoc] using hh

end DifferentialGeometry.Geometry.Curvature
