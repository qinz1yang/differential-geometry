import DifferentialGeometry.Geometry.Curvature.Metric.Sectional
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalIdentity
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalPerturbationUpper
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness

section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private theorem riemannOp_bound_of_sectionalCurvature_eq_neg
    (G : SmoothRiemannianMetric I M) (x : M) {κ : ℝ} (hκ : 0 < κ)
    (hsec : ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      sectionalCurvature G x u v = -κ) (u v w : TangentSpace I x) :
    Real.sqrt (G.inner x (riemannOp (LeviCivita G) x u v w)
      (riemannOp (LeviCivita G) x u v w)) ≤
      (2 * κ) * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
        Real.sqrt (G.inner x w w) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by decide)
  have hR : riemannOp (LeviCivita G) x u v w =
      (-κ) • (G.inner x v w • u - G.inner x u w • v) := by
    apply riemannOp_of_rm G x (-κ) _ u v w
    apply metricRm_of_sec G x (-κ)
    exact metricRm04StandardAt_eq_of_sectionalCurvature_eq G (-κ) x hsec
  have htri := sqrt_inner_add_le G x (G.inner x v w • u) (-(G.inner x u w) • v)
  rw [sqrt_inner_smul, sqrt_inner_smul, abs_neg] at htri
  simp only [neg_smul, ← sub_eq_add_neg] at htri
  have hv := mul_le_mul_of_nonneg_right (abs_inner_le_sqrt_mul_sqrt G x v w)
    (Real.sqrt_nonneg (G.inner x u u))
  have hu := mul_le_mul_of_nonneg_right (abs_inner_le_sqrt_mul_sqrt G x u w)
    (Real.sqrt_nonneg (G.inner x v v))
  calc
    Real.sqrt (G.inner x (riemannOp (LeviCivita G) x u v w)
        (riemannOp (LeviCivita G) x u v w)) =
        κ * Real.sqrt (G.inner x (G.inner x v w • u - G.inner x u w • v)
          (G.inner x v w • u - G.inner x u w • v)) := by
      rw [hR, sqrt_inner_smul, abs_neg, abs_of_pos hκ]
    _ ≤ κ * (|G.inner x v w| * Real.sqrt (G.inner x u u) +
        |G.inner x u w| * Real.sqrt (G.inner x v v)) :=
      mul_le_mul_of_nonneg_left htri hκ.le
    _ ≤ κ * ((Real.sqrt (G.inner x v v) * Real.sqrt (G.inner x w w)) *
        Real.sqrt (G.inner x u u) +
        (Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x w w)) *
          Real.sqrt (G.inner x v v)) :=
      mul_le_mul_of_nonneg_left (add_le_add hv hu) hκ.le
    _ = (2 * κ) * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
        Real.sqrt (G.inner x w w) := by ring

end

universe uE uH uM

theorem exists_pos_sectional_pinching_of_metricDerivNorm_le
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∃ ε > 0,
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] (H : Type uH) [TopologicalSpace H]
        (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M]
        (g G : SmoothRiemannianMetric I M) (x : M),
        (∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ ε) →
        (∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
          sectionalCurvature G x u v = -κ) →
        SectionalBoundedBelowAt g x (-(κ + η)) ∧
          ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
            sectionalCurvature g x u v ≤ -(κ - η) := by
  let θ := min η (κ / 2)
  have hθ : 0 < θ := lt_min hη (by linarith)
  have hθη : θ ≤ η := min_le_left _ _
  have hθκ : θ ≤ κ / 2 := min_le_right _ _
  let D := 360 + 5 * κ + 2 * θ
  have hD : 0 < D := by dsimp [D]; positivity
  let ε := min (1 / 2 : ℝ) (θ / D)
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hθ hD)
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hεD : ε * D ≤ θ :=
    (le_div_iff₀ hD).mp (min_le_right _ _)
  have hlowerBudget : -(κ + θ) * (1 - 2 * ε) + ε * (360 + 2 * κ) ≤ -κ := by
    dsimp [D] at hεD
    nlinarith [mul_nonneg hε.le hκ.le]
  have hupperBudget : ε * (360 + 2 * κ) + (1 + ε) ^ 2 * (κ - θ) ≤ κ := by
    have hεsq : ε ^ 2 ≤ ε := by
      simpa only [pow_two, mul_one] using
        mul_le_mul_of_nonneg_left (show ε ≤ 1 by linarith) hε.le
    have hsq : (1 + ε) ^ 2 ≤ 1 + 3 * ε := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hsq (show 0 ≤ κ - θ by linarith)
    dsimp [D] at hεD
    nlinarith [mul_nonneg hε.le hθ.le]
  refine ⟨ε, hε, ?_⟩
  intro E _ _ _ H _ I _ M _ _ _ _ g G x hsmall hsec
  have hmodel := riemannOp_bound_of_sectionalCurvature_eq_neg G x hκ hsec
  have hconst (u v : TangentSpace I x) :
      metricRm04StandardAt G x u v v u =
        -κ * (G.inner x u u * G.inner x v v - (G.inner x u v) ^ 2) := by
    simpa only [pow_two] using
      metricRm04StandardAt_eq_of_sectionalCurvature_eq G (-κ) x hsec u v
  have hlo : SectionalBoundedBelowAt g x (-(κ + θ)) :=
    metricRm04StandardAt_lower_bound_nonpos_of_small_metric_derivatives g G x
      (c := -κ) (c' := -(κ + θ)) hεhalf (by linarith) hsmall hmodel
      (fun u v => (hconst u v).ge) hlowerBudget
  have hhi := metricRm04StandardAt_upper_bound_of_small_metric_derivatives g G x
    (c := κ) (c' := κ - θ) hεhalf (show 0 ≤ κ - θ by linarith) hsmall hmodel
    (fun u v => by rw [hconst u v]; ring_nf; exact le_rfl) hupperBudget
  refine ⟨hlo.mono (by linarith), ?_⟩
  intro u v huv
  have hden : 0 < g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
    simpa only [sectionalCurvatureDenominator_def] using
      sectionalCurvatureDenominator_pos_of_linearIndependent g x u v huv
  rw [sectionalCurvature_eq_metricRm04StandardAt_div]
  apply (div_le_iff₀ hden).mpr
  have hcoef := mul_le_mul_of_nonneg_right (show -(κ - θ) ≤ -(κ - η) by linarith)
    hden.le
  have hh := hhi u v
  nlinarith

end DifferentialGeometry.Geometry.Curvature
