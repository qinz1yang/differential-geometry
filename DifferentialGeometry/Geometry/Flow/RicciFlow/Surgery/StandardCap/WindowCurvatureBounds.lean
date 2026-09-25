import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRadius
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling

noncomputable section
open Set Manifold Function DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

theorem curvature_derivative_bound_near_window_anchor
    (g : SmoothRiemannianMetric ThreeModel M) {D R₀ R₁ R₂ q Q C d r B : ℝ}
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ ≤ R₂) (hR₂D : R₂ < D + 1)
    (hq : 0 < q) (hQ : 0 < Q) (hC : 0 < C) (hB : 0 ≤ B)
    (hscale : q ≤ C * Q) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ)
    (hinj : Injective Φ)
    (hmetric : ∀ x : standardCapWindow D, ‖x.val‖ ≤ R₂ → ∀ v : TangentSpace ThreeModel x,
      (1/4 : ℝ) * metric.inner x.val v v ≤
        (scaleMetric q hq g).inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
          (mfderiv ThreeModel ThreeModel Φ x v) ∧
      (scaleMetric q hq g).inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
        (mfderiv ThreeModel ThreeModel Φ x v) ≤ 4 * metric.inner x.val v v)
    (N : ℕ)
    (hjets : ∀ j ≤ N, ∀ x : standardCapWindow D, ‖x.val‖ ≤ R₂ →
      curvDerivNormSq j g (Φ x) ≤ q^(j+2) * B)
    (u : standardCapWindow D) (hu : ‖u.val‖ ≤ R₀) (huR : R₀ < R₁) (y : M)
    (hnear : riemannianEDistOf g (Φ u) y ≤ ENNReal.ofReal (d / Real.sqrt Q))
    (hinner : 2 * R₀ + d * Real.sqrt C < R₁ / 2)
    (houter : 2 * R₀ + (d+r) * Real.sqrt C ≤ R₂ / 2) :
    (∀ j ≤ N, curvDerivNormSq j (scaleMetric Q hQ g) y ≤ C ^ (j+2) * B) ∧
      ∀ z ∈ riemannianBallOf g y (r / Real.sqrt Q),
        ∀ j ≤ N, curvDerivNormSq j (scaleMetric Q hQ g) z ≤ C ^ (j+2) * B := by
  have hlower : ∀ x : standardCapWindow D, ‖x.val‖ ≤ R₂ → ∀ v : TangentSpace ThreeModel x,
      metric.inner x.val v v ≤ (2 : ℝ)^2 *
        (scaleMetric q hq g).inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
          (mfderiv ThreeModel ThreeModel Φ x v) := by
    intro x hx v
    have hb := (hmetric x hx v).1
    norm_num only [show (2:ℝ)^2=4 by norm_num]
    linarith
  have hupper : ∀ x : standardCapWindow D, ‖x.val‖ ≤ R₂ → ∀ v : TangentSpace ThreeModel x,
      (scaleMetric q hq g).inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
        (mfderiv ThreeModel ThreeModel Φ x v) ≤ (2 : ℝ)^2 * metric.inner x.val v v := by
    intro x hx v
    simpa only [show (2:ℝ)^2=4 by norm_num] using (hmetric x hx v).2
  obtain ⟨⟨v, hv, hvy⟩, hcapture⟩ :=
    window_exists_preimage_and_ball_subset_image_of_scaled_metric_bounds g hR₁ hR₁₂ hR₂D
      (by norm_num) (by norm_num) hq hQ hC hscale hd hr Φ hΦ hinj hlower hupper
      u hu huR y hnear hinner houter
  have hbound (x : standardCapWindow D) (hx : ‖x.val‖ ≤ R₂) (j : ℕ) (hj : j ≤ N) :
      curvDerivNormSq j (scaleMetric Q hQ g) (Φ x) ≤ C ^ (j+2) * B := by
    rw [curvDerivNormSq_scaleMetric]
    have hratio : Q⁻¹ * q ≤ C := by
      rw [inv_mul_eq_div]
      exact (div_le_iff₀ hQ).mpr (by nlinarith only [hscale])
    calc
      _ ≤ Q⁻¹^(j+2) * (q^(j+2)*B) :=
        mul_le_mul_of_nonneg_left (hjets j hj x hx) (by positivity)
      _ = (Q⁻¹*q)^(j+2)*B := by rw [mul_pow]; ring
      _ ≤ C ^ (j+2)*B := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hratio _) hB
  constructor
  · intro j hj
    rw [← hvy]
    exact hbound v (hv.trans hR₁₂) j hj
  · intro z hz j hj
    obtain ⟨v, hv, rfl⟩ := hcapture hz
    exact hbound v hv j hj

end DifferentialGeometry.PDE.RicciFlow.StandardCap
