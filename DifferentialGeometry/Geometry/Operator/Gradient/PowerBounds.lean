import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem neg_two_mul_inner_gradient_pow_le
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {x : M}
    (w : TangentSpace I x) (p : ℕ) {a b ε δ : ℝ}
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) (hu0 : 0 ≤ u x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hgrad : g.inner x (gradientFun g u x) (gradientFun g u x) ≤ ε * u x)
    (hw : g.inner x w w ≤ a * b) :
    -2 * g.inner x (gradientFun g (fun y => u y ^ (p + 1)) x) w ≤
      δ * u x ^ (p + 1) * b + ((p + 1 : ℕ) : ℝ) ^ 2 / δ * ε * u x ^ p * a := by
  let c₀ := g.inner x (gradientFun g u x) w
  let c := g.inner x (gradientFun g (fun y => u y ^ (p + 1)) x) w
  let r : ℝ := ((p + 1 : ℕ) : ℝ) * u x ^ p
  let q₁ : ℝ := δ * u x ^ (p + 1) * b
  let q₂ : ℝ := ((p + 1 : ℕ) : ℝ) ^ 2 / δ * ε * u x ^ p * a
  have hsq₀ : c₀ ^ 2 ≤ (ε * u x) * (a * b) := by
    calc
      c₀ ^ 2 ≤ g.inner x (gradientFun g u x) (gradientFun g u x) * g.inner x w w :=
        DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
          g x (gradientFun g u x) w
      _ ≤ (ε * u x) * (a * b) :=
        mul_le_mul hgrad hw (metric_inner_self_nonneg g x w) (mul_nonneg hε hu0)
  have hc : c = r * c₀ := by
    dsimp only [c, r, c₀]
    rw [gradientFun_pow g p hu]
    simp only [map_smul, smul_apply, smul_eq_mul]
  have hsq : c ^ 2 ≤ q₁ * q₂ := by
    rw [hc]
    calc
      (r * c₀) ^ 2 = r ^ 2 * c₀ ^ 2 := by ring
      _ ≤ r ^ 2 * ((ε * u x) * (a * b)) :=
        mul_le_mul_of_nonneg_left hsq₀ (sq_nonneg r)
      _ = q₁ * q₂ := by
        dsimp only [r, q₁, q₂]
        rw [pow_succ]
        field_simp [hδ.ne']
        ring
  have hq₁ : 0 ≤ q₁ := by
    dsimp only [q₁]
    exact mul_nonneg (mul_nonneg hδ.le (pow_nonneg hu0 _)) hb
  have hq₂ : 0 ≤ q₂ := by
    dsimp only [q₂]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (div_nonneg (sq_nonneg _) hδ.le) hε) (pow_nonneg hu0 _)) ha
  have hhalf : q₁ * q₂ ≤ ((q₁ + q₂) / 2) ^ 2 := by
    nlinarith [sq_nonneg (q₁ - q₂)]
  have habs : |c| ≤ (q₁ + q₂) / 2 :=
    abs_le_of_sq_le_sq (hsq.trans hhalf) (by positivity)
  have hneg : -c ≤ (q₁ + q₂) / 2 := (neg_le_abs c).trans habs
  change -2 * c ≤ q₁ + q₂
  linarith

end DifferentialGeometry.Geometry.Operator
