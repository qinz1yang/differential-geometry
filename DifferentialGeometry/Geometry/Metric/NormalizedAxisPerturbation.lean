import DifferentialGeometry.Geometry.Metric.LengthPerturbation
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Riemannian

namespace Poincare.Geometry.Metric

theorem normalized_axis_for_perturbed_metric
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g gRef : SmoothRiemannianMetric I M) (x : M) (δ : ℝ) (hδ : δ ≤ 1 / 2)
    (hmetric : metricDerivNorm 0 g gRef gRef x ≤ δ)
    (v : TangentSpace I x) (hv : gRef.inner x v v = 1) :
    let e := (Real.sqrt (g.inner x v v))⁻¹ • v
    g.inner x e e = 1 ∧
      (∀ z : TangentSpace I x,
        (g.inner x e z) • e = (g.inner x v z / g.inner x v v) • v) ∧
      Real.sqrt (gRef.inner x (e - v) (e - v)) ≤ 2 * δ := by
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hmetric
  let s := Real.sqrt (g.inner x v v)
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = g.inner x v v := Real.sq_sqrt (metric_inner_self_nonneg g x v)
  have hlen := sqrt_inner_comparison_of_metric_difference g gRef x δ (by linarith) hmetric v
  rw [hv, Real.sqrt_one, mul_one, mul_one] at hlen
  have hslo : 1 - δ ≤ s := by
    have h := (Real.le_sqrt (show 0 ≤ 1 - δ by linarith)
      (show 0 ≤ 1 - δ by linarith)).mpr (show (1 - δ) ^ 2 ≤ 1 - δ by nlinarith)
    exact h.trans hlen.1
  have hshi : s ≤ 1 + δ := by
    have h : Real.sqrt (1 + δ) ≤ 1 + δ :=
      (Real.sqrt_le_iff).mpr ⟨by linarith, by nlinarith⟩
    exact hlen.2.trans h
  have hs0 : 0 < s := by linarith
  have hsne := ne_of_gt hs0
  have hsdiff : |s - 1| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have hi : |s⁻¹ - 1| ≤ 2 * δ := by
    have he : s⁻¹ - 1 = (1 - s) / s := by field_simp
    rw [he, abs_div, abs_of_pos hs0, abs_sub_comm]
    apply (div_le_iff₀ hs0).mpr
    have hm := mul_le_mul_of_nonneg_left (show 1 / 2 ≤ s by linarith) hδ0
    nlinarith
  dsimp only
  constructor
  · rw [map_smul (g.inner x), smul_apply, map_smul]
    change s⁻¹ * (s⁻¹ * g.inner x v v) = 1
    rw [← hs2]
    field_simp
  constructor
  · intro z
    rw [map_smul (g.inner x), smul_apply, smul_smul]
    change (s⁻¹ * g.inner x v z * s⁻¹) • v = (g.inner x v z / g.inner x v v) • v
    congr 1
    rw [← hs2]
    field_simp
  · have he : s⁻¹ • v - v = (s⁻¹ - 1) • v := by rw [sub_smul, one_smul]
    rw [he, sqrt_inner_smul, hv, Real.sqrt_one, mul_one]
    exact hi

end Poincare.Geometry.Metric
