import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.SmoothSolutions

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem forward_uniqueness_cutoff_flux_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : C^∞⟮I, M; ℝ⟯) (t : ℝ) (x : M)
    {B₂ BP Background ε : ℝ} (hε : 0 < ε)
    (hB₂ : normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ B₂)
    (hBP : normSq0S (I := I) (g₁ t) x 4
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
        (metricCov_smooth (I := I) (g₂ t)) x) ≤ BP)
    (hBackground : normSq0S (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₂ t) x) ≤ Background) :
    let S := forwardUniquenessSfield (I := I) g₁ g₂ t
    let U := forwardUniquenessUflux (I := I) g₁ g₂ t x
    let A := metricNabla0S (I := I) (g₁ t) S x
    let B := (covGradBundleEquiv (I := I) (M := M) 0 4 x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
    let C_U := 32 * (Module.finrank ℝ E : ℝ) ^ 5 * B₂ +
      8 * (Module.finrank ℝ E : ℝ) ^ 10 * (BP * Background);
    -(2 * χ x ^ 2 * inner0S (I := I) (g₁ t) x 5 A U) -
      4 * χ x * inner0S (I := I) (g₁ t) x 5 B U ≤
      ε * χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 A +
      (ε⁻¹ + 2) * χ x ^ 2 * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x +
      2 * normSq0S (I := I) (g₁ t) x 5 B := by
  dsimp only
  let S := forwardUniquenessSfield (I := I) g₁ g₂ t
  let U := forwardUniquenessUflux (I := I) g₁ g₂ t x
  let A := metricNabla0S (I := I) (g₁ t) S x
  let B := (covGradBundleEquiv (I := I) (M := M) 0 4 x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
  let C_U := 32 * (Module.finrank ℝ E : ℝ) ^ 5 * B₂ +
    8 * (Module.finrank ℝ E : ℝ) ^ 10 * (BP * Background)
  have hB₂0 : 0 ≤ B₂ := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans hB₂
  have hBP0 : 0 ≤ BP := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans hBP
  have hBackground0 : 0 ≤ Background :=
    (normSq0S_nonneg (I := I) (g₁ t) x 2 _).trans hBackground
  have hBP' : normSq0S (I := I) (g₁ t) x 4
      ((forwardUniquenessTf (I := I) g₁ t - forwardUniquenessSfield (I := I) g₁ g₂ t) x) ≤ BP := by
    rw [forwardUniquenessP_eq]
    exact hBP
  have hU : normSq0S (I := I) (g₁ t) x 5 U ≤
      C_U * forwardUniqueDensity (I := I) g₁ g₂ t x :=
    fluxSlabLe (I := I) g₁ g₂ (forwardUniquenessTf (I := I) g₂)
      (fun z => forwardUniquenessTf (I := I) g₁ z - forwardUniquenessSfield (I := I) g₁ g₂ z)
      t x hB₂0 hBP0 hBackground0 hB₂ hBP' hBackground
  have hmain := neg_two_inner0S_le_eps (I := I) (g₁ t) x 5
    (χ x • A) (χ x • U) hε
  rw [_root_.Tensor0SBundle.inner0S_smul_left, _root_.Tensor0SBundle.inner0S_smul_right, normSq0S_smul, normSq0S_smul] at hmain
  have hboundary := neg_two_inner0S_le_eps (I := I) (g₁ t) x 5 B (χ x • U)
    (ε := 1) (by norm_num)
  rw [_root_.Tensor0SBundle.inner0S_smul_right, normSq0S_smul] at hboundary
  norm_num only [inv_one, one_mul] at hboundary
  have hflux_bound := mul_le_mul_of_nonneg_left hU
    (show 0 ≤ (ε⁻¹ + 2) * χ x ^ 2 by positivity)
  change -(2 * χ x ^ 2 * inner0S (I := I) (g₁ t) x 5 A U) -
      4 * χ x * inner0S (I := I) (g₁ t) x 5 B U ≤
      ε * χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 A +
      (ε⁻¹ + 2) * χ x ^ 2 * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x +
      2 * normSq0S (I := I) (g₁ t) x 5 B
  nlinarith only [hmain, hboundary, hflux_bound]

end DifferentialGeometry.PDE.RicciFlow
