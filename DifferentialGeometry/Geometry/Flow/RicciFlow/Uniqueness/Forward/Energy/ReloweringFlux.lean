import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.SmoothSolutions
import DifferentialGeometry.Geometry.Curvature.Bounds.ReloweringFlux

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle (normSq0S_sub_le)
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

section NormedBase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

def forwardUniquenessReloweringFlux
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 5 :=
  reLower (I := I) (g₂ t) (g₁ t)
    (metricNabla0S (I := I) (g₁ t)
      (CovariantDerivative.rm04Section (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
        (metricCov_smooth (I := I) (g₂ t)))) -
  metricNabla0S (I := I) (g₁ t)
    (CovariantDerivative.rm04Section (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
      (metricCov_smooth (I := I) (g₂ t)))

end NormedBase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem forward_uniqueness_relowering_flux_norm_sq_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M)
    {C BH B₀ B₁ : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hBH : metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ BH)
    (hB₀ : normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ B₀)
    (hB₁ : normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ B₁) :
    normSq0S (I := I) (g₁ t) x 5 (forwardUniquenessReloweringFlux (I := I) g₁ g₂ t x) ≤
      (4 * (Module.finrank ℝ E : ℝ) ^ 15 * C ^ 7 * B₁ +
        (16 * (Module.finrank ℝ E : ℝ) ^ 18 * C ^ 8 +
          32 * (Module.finrank ℝ E : ℝ) ^ 19 * C ^ 6) * B₀ * BH) *
        forwardUniqueDensity (I := I) g₁ g₂ t x := by
  let k₁ : ℝ := 4 * (Module.finrank ℝ E : ℝ) ^ 15 * C ^ 7
  let k₂ : ℝ := 16 * (Module.finrank ℝ E : ℝ) ^ 18 * C ^ 8 +
    32 * (Module.finrank ℝ E : ℝ) ^ 19 * C ^ 6
  let h := metricDiffSq (I := I) (g₁ t) (g₂ t) x
  let a := connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x
  let r := normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x)
  let q := normSq0S (I := I) (g₂ t) x 5
    (metricNabla0S (I := I) (g₂ t)
      (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
        (metricCov_smooth (I := I) (g₂ t))) x)
  let d := forwardUniqueDensity (I := I) g₁ g₂ t x
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hk₁ : 0 ≤ k₁ := by dsimp [k₁]; positivity
  have hk₂ : 0 ≤ k₂ := by dsimp [k₂]; positivity
  have hh : 0 ≤ h := by
    dsimp [h]
    rw [metricDiffSq_def]
    exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have ha : 0 ≤ a := by
    dsimp [a]
    rw [connectionDifferenceSq_def]
    exact normSq0S_nonneg (I := I) (g₁ t) x 3 _
  have hB₀0 : 0 ≤ B₀ := (normSq0S_nonneg (I := I) (g₂ t) x 4 _).trans hB₀
  have hB₁0 : 0 ≤ B₁ := (normSq0S_nonneg (I := I) (g₂ t) x 5 _).trans hB₁
  have hBH0 : 0 ≤ BH := hh.trans hBH
  have hhd : h ≤ d := metricDiffSq_le_dens (I := I) g₁ g₂ t x
  have had : a ≤ d := connectionDifferenceSq_le_dens (I := I) g₁ g₂ t x
  have hqh : q * h ≤ B₁ * d := mul_le_mul hB₁ hhd hh hB₁0
  have hrh : r * h ≤ B₀ * BH := mul_le_mul hB₀ hBH hh hB₀0
  have harh : a * (r * h) ≤ (B₀ * BH) * d := by
    calc a * (r * h) ≤ a * (B₀ * BH) := mul_le_mul_of_nonneg_left hrh ha
      _ ≤ d * (B₀ * BH) := mul_le_mul_of_nonneg_right had (mul_nonneg hB₀0 hBH0)
      _ = (B₀ * BH) * d := mul_comm _ _
  have hflux := norm_sq_cross_curvature_relowering_flux_le (I := I) (g₁ t) (g₂ t) x hC hEquiv
  change normSq0S (I := I) (g₁ t) x 5
      (forwardUniquenessReloweringFlux (I := I) g₁ g₂ t x) ≤
    (k₁ * q + k₂ * a * r) * h at hflux
  refine hflux.trans ?_
  change (k₁ * q + k₂ * a * r) * h ≤ (k₁ * B₁ + k₂ * B₀ * BH) * d
  calc (k₁ * q + k₂ * a * r) * h = k₁ * (q * h) + k₂ * (a * (r * h)) := by ring
    _ ≤ k₁ * (B₁ * d) + k₂ * ((B₀ * BH) * d) :=
      add_le_add (mul_le_mul_of_nonneg_left hqh hk₁) (mul_le_mul_of_nonneg_left harh hk₂)
    _ = (k₁ * B₁ + k₂ * B₀ * BH) * d := by ring

theorem forward_uniqueness_corrected_flux_norm_sq_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M)
    {C BH B₀ B₁ B₂ BP Background : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hBH : metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ BH)
    (hB₀ : normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ B₀)
    (hB₁ : normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ B₁)
    (hB₂ : normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ B₂)
    (hBP : normSq0S (I := I) (g₁ t) x 4
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
        (metricCov_smooth (I := I) (g₂ t)) x) ≤ BP)
    (hBackground : normSq0S (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₂ t) x) ≤ Background) :
    let n : ℝ := Module.finrank ℝ E
    let C_U := 32 * n ^ 5 * B₂ + 8 * n ^ 10 * (BP * Background)
    let C_V := 4 * n ^ 15 * C ^ 7 * B₁ +
      (16 * n ^ 18 * C ^ 8 + 32 * n ^ 19 * C ^ 6) * B₀ * BH
    normSq0S (I := I) (g₁ t) x 5
        ((forwardUniquenessUflux (I := I) g₁ g₂ t -
          forwardUniquenessReloweringFlux (I := I) g₁ g₂ t) x) ≤
      (2 * C_U + 2 * C_V) * forwardUniqueDensity (I := I) g₁ g₂ t x := by
  dsimp only
  let n : ℝ := Module.finrank ℝ E
  let C_U := 32 * n ^ 5 * B₂ + 8 * n ^ 10 * (BP * Background)
  let C_V := 4 * n ^ 15 * C ^ 7 * B₁ +
    (16 * n ^ 18 * C ^ 8 + 32 * n ^ 19 * C ^ 6) * B₀ * BH
  let d := forwardUniqueDensity (I := I) g₁ g₂ t x
  have hB₂0 : 0 ≤ B₂ := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans hB₂
  have hBP0 : 0 ≤ BP := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans hBP
  have hBackground0 : 0 ≤ Background :=
    (normSq0S_nonneg (I := I) (g₁ t) x 2 _).trans hBackground
  have hBP' : normSq0S (I := I) (g₁ t) x 4
      ((forwardUniquenessTf (I := I) g₁ t - forwardUniquenessSfield (I := I) g₁ g₂ t) x) ≤ BP := by
    rw [forwardUniquenessP_eq]
    exact hBP
  have hU : normSq0S (I := I) (g₁ t) x 5 (forwardUniquenessUflux (I := I) g₁ g₂ t x) ≤
      C_U * d :=
    fluxSlabLe (I := I) g₁ g₂ (forwardUniquenessTf (I := I) g₂)
      (fun z => forwardUniquenessTf (I := I) g₁ z - forwardUniquenessSfield (I := I) g₁ g₂ z)
      t x hB₂0 hBP0 hBackground0 hB₂ hBP' hBackground
  have hV : normSq0S (I := I) (g₁ t) x 5
      (forwardUniquenessReloweringFlux (I := I) g₁ g₂ t x) ≤ C_V * d :=
    forward_uniqueness_relowering_flux_norm_sq_le (I := I) g₁ g₂ t x hC hEquiv hBH hB₀ hB₁
  have hsub := normSq0S_sub_le (I := I) (g₁ t) x 5
    (forwardUniquenessUflux (I := I) g₁ g₂ t x)
    (forwardUniquenessReloweringFlux (I := I) g₁ g₂ t x)
  change normSq0S (I := I) (g₁ t) x 5
    (forwardUniquenessUflux (I := I) g₁ g₂ t x -
      forwardUniquenessReloweringFlux (I := I) g₁ g₂ t x) ≤ (2 * C_U + 2 * C_V) * d
  calc _ ≤ 2 * normSq0S (I := I) (g₁ t) x 5 (forwardUniquenessUflux (I := I) g₁ g₂ t x) +
      2 * normSq0S (I := I) (g₁ t) x 5 (forwardUniquenessReloweringFlux (I := I) g₁ g₂ t x) := hsub
    _ ≤ 2 * (C_U * d) + 2 * (C_V * d) := by linarith
    _ = (2 * C_U + 2 * C_V) * d := by ring

end DifferentialGeometry.PDE.RicciFlow
