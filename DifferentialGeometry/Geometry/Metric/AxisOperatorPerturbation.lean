import DifferentialGeometry.Geometry.Metric.AxisProjectionPerturbation
import DifferentialGeometry.Geometry.Metric.LengthPerturbation

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Riemannian

namespace Poincare.Geometry.Metric

theorem axis_operator_error_for_perturbed_metric
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g gRef : SmoothRiemannianMetric I M) (x : M) (δ η κ : ℝ) (hδ : δ ≤ 1 / 2)
    (hmetric : metricDerivNorm 0 g gRef gRef x ≤ δ)
    (v : TangentSpace I x) (hv : gRef.inner x v v = 1)
    (A : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (herror : ∀ z : TangentSpace I x,
      let d := A z - κ • (z - (gRef.inner x v z) • v)
      Real.sqrt (gRef.inner x d d) ≤ η * Real.sqrt (gRef.inner x z z))
    (z : TangentSpace I x) :
    let d := A z - κ • (z - (g.inner x v z / g.inner x v v) • v)
    Real.sqrt (g.inner x d d) ≤
      4 * (η + 4 * |κ| * δ) * Real.sqrt (g.inner x z z) := by
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hmetric
  have hη0 : 0 ≤ η := by
    have h := herror v
    rw [hv, Real.sqrt_one, mul_one] at h
    exact (Real.sqrt_nonneg _).trans h
  let N (w : TangentSpace I x) := Real.sqrt (gRef.inner x w w)
  let N' (w : TangentSpace I x) := Real.sqrt (g.inner x w w)
  have hcompare (w : TangentSpace I x) : N' w ≤ 2 * N w ∧ N w ≤ 2 * N' w := by
    have h := sqrt_inner_comparison_of_metric_difference g gRef x δ (by linarith) hmetric w
    have hupper : Real.sqrt (1 + δ) ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
    have hlower : 1 / 2 ≤ Real.sqrt (1 - δ) := by
      apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
      nlinarith
    constructor
    · exact h.2.trans (mul_le_mul_of_nonneg_right hupper (Real.sqrt_nonneg _))
    · have hl := mul_le_mul_of_nonneg_right hlower (Real.sqrt_nonneg (gRef.inner x w w))
      change N w ≤ 2 * N' w
      have hlo : Real.sqrt (1 - δ) * N w ≤ N' w := h.1
      linarith
  let P := (g.inner x v z / g.inner x v v) • v - (gRef.inner x v z) • v
  let d₀ := A z - κ • (z - (gRef.inner x v z) • v)
  let d := A z - κ • (z - (g.inner x v z / g.inner x v v) • v)
  have hp : N P ≤ 4 * δ * N z := by
    have h := axis_projection_difference_bound g gRef x δ (by linarith) hmetric v hv z
    apply h.trans
    have hc : 2 * δ / (1 - δ) ≤ 4 * δ := by
      apply (div_le_iff₀ (show 0 < 1 - δ by linarith)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hδ hδ0]
    exact mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
  have heq : d = d₀ + κ • P := by dsimp only [d, d₀, P]; module
  have hd : N d ≤ (η + 4 * |κ| * δ) * N z := by
    rw [heq]
    have htri := sqrt_inner_add_le gRef x d₀ (κ • P)
    rw [sqrt_inner_smul] at htri
    have hh := mul_le_mul_of_nonneg_left hp (abs_nonneg κ)
    have he := herror z
    change N d₀ ≤ η * N z at he
    change N (d₀ + κ • P) ≤ N d₀ + |κ| * N P at htri
    calc
      _ ≤ N d₀ + |κ| * N P := htri
      _ ≤ η * N z + |κ| * (4 * δ * N z) := add_le_add he hh
      _ = _ := by ring
  change N' d ≤ 4 * (η + 4 * |κ| * δ) * N' z
  calc
    _ ≤ 2 * N d := (hcompare d).1
    _ ≤ 2 * ((η + 4 * |κ| * δ) * N z) := mul_le_mul_of_nonneg_left hd (by norm_num)
    _ ≤ 2 * ((η + 4 * |κ| * δ) * (2 * N' z)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcompare z).2 (by positivity)) (by norm_num)
    _ = _ := by ring

end Poincare.Geometry.Metric
