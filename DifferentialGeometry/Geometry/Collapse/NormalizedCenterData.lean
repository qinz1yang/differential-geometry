import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormScaling

/-!
At each actual center, the chosen modified radius normalizes the original curvature-scale
buffer and every finite derivative order on one common tested-radius range.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def normalizedCenterMetric (g : SmoothRiemannianMetric I M) (ρ : ℝ) (hρ : 0 < ρ) :
    SmoothRiemannianMetric I M :=
  scaleMetric (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) g

theorem normalizedCenterMetric_ball (g : SmoothRiemannianMetric I M)
    {ρ : ℝ} (hρ : 0 < ρ) (p : M) (R : ℝ) :
    riemannianBallOf (normalizedCenterMetric g ρ hρ) p R = riemannianBallOf g p (R * ρ) := by
  have hs : Real.sqrt ((ρ ^ 2)⁻¹) = ρ⁻¹ := by
    rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hρ]
  have he : Real.sqrt ((ρ ^ 2)⁻¹) * (R * ρ) = R := by
    rw [hs]
    field_simp
  unfold normalizedCenterMetric
  simpa only [he] using
    riemannianBallOf_scaleMetric (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) g p (R * ρ)

section Curvature

variable [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M]

theorem normalizedCenterMetric_sectional_buffer (g : SmoothRiemannianMetric I M)
    (p : M) {α u ρ : ℝ} (hα : 0 < α) (hu : 0 < u) (hρ : 0 < ρ)
    (hρu : ρ ≤ 2 * u) (hscale : ENNReal.ofReal (α * u) ≤ curvatureRadius g p) :
    ∀ y ∈ riemannianBallOf (normalizedCenterMetric g ρ hρ) p (α / 4),
      SectionalBoundedBelowAt (normalizedCenterMetric g ρ hρ) y (-((α / 4) ^ 2)⁻¹) := by
  intro y hy
  rw [normalizedCenterMetric_ball] at hy
  have hstrict : α / 4 * ρ < α * u := by nlinarith
  have hlt : ENNReal.ofReal (α / 4 * ρ) < curvatureRadius g p :=
    ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hα hu)).mpr hstrict).trans_le hscale
  have hsec := sectionalBoundedBelowAt_of_lt_curvatureRadius g hlt hy
  unfold normalizedCenterMetric
  apply (sectionalBoundedBelowAt_scaleMetric_iff _).mpr
  have he : -((α / 4) ^ 2)⁻¹ * (ρ ^ 2)⁻¹ = -((α / 4 * ρ) ^ 2)⁻¹ := by
    rw [mul_pow, mul_inv]
    ring
  rwa [he]

theorem normalizedCenterMetric_derivative (g : SmoothRiemannianMetric I M)
    {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) (x : M) :
    curvatureDerivativeNorm (normalizedCenterMetric g ρ hρ) k x =
      ρ ^ (k + 2) * curvatureDerivativeNorm g k x := by
  unfold normalizedCenterMetric
  simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hρ] using
    curvatureDerivativeNorm_scaleMetric_inv g (ρ ^ 2) (sq_pos_of_pos hρ) k x

theorem normalizedCenterMetric_derivative_bounds (g : SmoothRiemannianMetric I M)
    (p : M) (K : ℕ) (A : ℝ → ℝ) {α u ρ : ℝ}
    (hu : 0 < u) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u)
    (hA : ∀ C, 0 < C → 0 ≤ A C)
    (hcurv : ∀ C, 0 < C → C < α → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf g p (C * u),
        curvatureDerivativeNorm g k y ≤ A C * (u ^ (k + 2))⁻¹) :
    ∀ R, 0 < R → 2 * R + 2 < α → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g ρ hρ) p R,
        curvatureDerivativeNorm (normalizedCenterMetric g ρ hρ) k y ≤
          (2 : ℝ) ^ (K + 2) * A (2 * R + 2) := by
  intro R hR hRα k hk y hy
  rw [normalizedCenterMetric_ball] at hy
  have hC : 0 < 2 * R + 2 := by linarith
  have hbound := hcurv (2 * R + 2) hC hRα k hk y
    (riemannianBallOf_mono g p (by nlinarith : R * ρ ≤ (2 * R + 2) * u) hy)
  rw [normalizedCenterMetric_derivative]
  have hratio : 0 ≤ ρ / u := (div_pos hρ hu).le
  have hratio2 : ρ / u ≤ 2 := (div_le_iff₀ hu).mpr hρu
  have hpower : (ρ / u) ^ (k + 2) ≤ (2 : ℝ) ^ (K + 2) :=
    (pow_le_pow_left₀ hratio hratio2 _).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  calc
    _ ≤ ρ ^ (k + 2) * (A (2 * R + 2) * (u ^ (k + 2))⁻¹) :=
      mul_le_mul_of_nonneg_left hbound (pow_nonneg hρ.le _)
    _ = (ρ / u) ^ (k + 2) * A (2 * R + 2) := by rw [div_pow, div_eq_mul_inv]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpower (hA _ hC)

theorem normalizedCenterMetric_common_test_range (g : SmoothRiemannianMetric I M)
    (p : M) (K : ℕ) (A : ℝ → ℝ) {α u ρ B : ℝ}
    (hu : 0 < u) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u)
    (hA : ∀ C, 0 < C → 0 ≤ A C) (hα : 2 * B + 2 < α)
    (hcurv : ∀ C, 0 < C → C < α → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf g p (C * u),
        curvatureDerivativeNorm g k y ≤ A C * (u ^ (k + 2))⁻¹) :
    ∀ R, 0 < R → R < B → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g ρ hρ) p R,
        curvatureDerivativeNorm (normalizedCenterMetric g ρ hρ) k y ≤
          (2 : ℝ) ^ (K + 2) * A (2 * R + 2) := by
  intro R hR hRB
  exact normalizedCenterMetric_derivative_bounds g p K A hu hρ hρu hA hcurv R hR (by linarith)

end Curvature

end DifferentialGeometry.Geometry.Collapse
