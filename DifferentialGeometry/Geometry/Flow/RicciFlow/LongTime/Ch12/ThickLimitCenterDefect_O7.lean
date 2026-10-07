import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitVolumeLimit_O5
import DifferentialGeometry.Geometry.Curvature.RicciUniformPerturbation
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

/-!
# CH12-O7 / C1, group C (static part): the Ricci defect is continuous at an Einstein metric

`defect_le_of_close_einstein_O7`: if `Ric_ref = -½ ref` at `q` and `h` is `ε`-close to `ref` in
`C²` at `q` (reference `ref`, `ε ≤ ½`), then the defect `sup |2 Ric_h + h|` over `h`-unit vectors is
at most `2882 ε`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.CheegerGromovCompactness
open Set Filter
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

variable {V : Type*} [TopologicalSpace V] [ChartedSpace ThreeSpace V]
  [IsManifold ThreeModel ∞ V] [T2Space V] [SigmaCompactSpace V]

theorem defect_le_of_close_einstein_O7 (h ref : SmoothRiemannianMetric ThreeModel V) (q : V)
    (hE : ∀ v w : TangentSpace ThreeModel q, ricciTensor ref q v w = -(1 / 2) * ref.inner q v w)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k h ref ref q ≤ ε) :
    sSup (defectSet_O5 h q) ≤ 2882 * ε := by
  have hne : (defectSet_O5 h q).Nonempty :=
    ⟨_, 0, 0, by simp, by simp, rfl⟩
  apply csSup_le hne
  rintro r ⟨v, w, hv, hw, rfl⟩
  have hrefv : ref.inner q v v ≤ 2 := by
    have h1 := metricDifference_abs_le h ref ref q v v
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at h1
    have h2 := mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num))
      (metric_inner_self_nonneg ref q v)
    have := (abs_le.mp (h1.trans h2)).1
    have h0 := metric_inner_self_nonneg ref q v
    nlinarith
  have hrefw : ref.inner q w w ≤ 2 := by
    have h1 := metricDifference_abs_le h ref ref q w w
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at h1
    have h2 := mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num))
      (metric_inner_self_nonneg ref q w)
    have := (abs_le.mp (h1.trans h2)).1
    have h0 := metric_inner_self_nonneg ref q w
    nlinarith
  have hsq : Real.sqrt (ref.inner q v v) * Real.sqrt (ref.inner q w w) ≤ 2 := by
    rw [← Real.sqrt_mul (metric_inner_self_nonneg _ _ _)]
    calc Real.sqrt (ref.inner q v v * ref.inner q w w) ≤ Real.sqrt 4 := by
          apply Real.sqrt_le_sqrt
          nlinarith [metric_inner_self_nonneg ref q v, metric_inner_self_nonneg ref q w]
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hS0 : 0 ≤ Real.sqrt (ref.inner q v v) * Real.sqrt (ref.inner q w w) := by positivity
  have hric := abs_ricci_difference_bound_of_small_metric_derivatives h ref q ε hε hsmall v w
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by simp
  rw [hdim] at hric
  have hmet := metricDifference_abs_le h ref ref q v w
  have hmet' : |h.inner q v w - ref.inner q v w| ≤
      ε * (Real.sqrt (ref.inner q v v) * Real.sqrt (ref.inner q w w)) := by
    rw [← mul_assoc]
    exact hmet.trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num)) (Real.sqrt_nonneg _))
  have hkey : 2 * ricciTensor h q v w + h.inner q v w =
      2 * (ricciTensor h q v w - ricciTensor ref q v w) + (h.inner q v w - ref.inner q v w) := by
    rw [hE]; ring
  rw [hkey]
  calc |2 * (ricciTensor h q v w - ricciTensor ref q v w) + (h.inner q v w - ref.inner q v w)|
      ≤ 2 * |ricciTensor h q v w - ricciTensor ref q v w| + |h.inner q v w - ref.inner q v w| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two]
    _ ≤ 2 * (240 * 3 * ε * Real.sqrt (ref.inner q v v) * Real.sqrt (ref.inner q w w)) +
        ε * (Real.sqrt (ref.inner q v v) * Real.sqrt (ref.inner q w w)) := by gcongr
    _ = (1441 * ε) * (Real.sqrt (ref.inner q v v) * Real.sqrt (ref.inner q w w)) := by ring
    _ ≤ (1441 * ε) * 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2882 * ε := by ring

end GC.LongTime.Ch12
