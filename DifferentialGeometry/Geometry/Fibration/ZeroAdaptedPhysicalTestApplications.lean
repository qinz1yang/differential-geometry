import DifferentialGeometry.Geometry.Fibration.ZeroAdaptedPhysicalTest

/-!
# Consumer of LC73 in physical form: the zero test on a met reference ball, in reference units

Blueprint `master207B.tex`, TCP03 (B:5430), SGP03, EGP04: "LC73 at EVERY `x ∈ D_i`" with the
reference scale `ρ(p)` of the ball (the ratio `λ = R/ρ(p)`).

* `zero_adapted_reference_KA5`: if a zero support meets `B(p, ℓρ(p))` (`2ℓ/T + 2ℓΛ ≤ 1/40`,
  `20Λz ≤ T`), then at every `x` of the ball: `|R dη₀(v)| ≤ (1 + ζ)√(g(v, v))`, and along every
  physical unit direction `w₀` whose normalized geodesics reach `y` with
  `ρ(p) < d(x, y)`, `ζ d(x, y) < ρ(p)`: `|R dη₀(w₀) − (d(k, y) − d(k, x))/d(x, y)| < ζ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ_ZAPA_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ_ZAPA_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ_ZAPA_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **LC73 on a met reference ball, in reference units `ρ(p)`**: derivative bound and test of the
radial coordinate at every point of the ball (ratio `λ = R/ρ(p)`). -/
theorem zero_adapted_reference_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    (hΛ : 0 ≤ Λ) (he : e < 1 / 40) (hT : 0 < T) (hΛz : 20 * Λz ≤ T) (p : X) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) {k : X} (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty) {x : X}
    (hx : x ∈ ball p (ℓ * ρ p)) :
    (∀ v : TangentSpace 𝓘(ℝ, E3) x,
      |(P.zero.zero k hk).radius * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v| ≤
        (1 + ζ) * Real.sqrt (g.inner x v v)) ∧
    (0 < ζ → ∀ y : X, ρ p < dist x y → ζ * dist x y < ρ p →
      ∀ (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 →
      (∀ (R : ℝ) (hR : 0 < R),
        let hMc : CompleteSpace X := complete_of_compact
        letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
        letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
        letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
          isMetricNorm_of_riemannianBundle gR
        intrinsicGeodesic gR hnR x (R • w₀) (dist x y) = y) →
      |(P.zero.zero k hk).radius * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w₀ -
        (dist k y - dist k x) / dist x y| < ζ) := by
  have hpp : p ∈ ball p (ℓ * ρ p) := mem_ball_self (mul_pos hℓ (hρ p))
  obtain ⟨-, -, -, hΛp⟩ := zero_adapted_ratio_ZERO P hΛ he hT hΛz p hℓ hsmall hk hmeet p hpp
  obtain ⟨h1, h2, -, -⟩ := zero_adapted_ratio_ZERO P hΛ he hT hΛz p hℓ hsmall hk hmeet x hx
  exact ⟨fun v => zero_adapted_deriv_bound_KA5 P hk h1 h2 (hρ p) hΛp v,
    fun hζ y hy1 hy2 w₀ hw₀ hgeo =>
      zero_adapted_test_phys_KA5 P hk h1 h2 (hρ p) hΛp hζ hy1 hy2 w₀ hw₀ hgeo⟩

end DifferentialGeometry.Geometry.Collapse
