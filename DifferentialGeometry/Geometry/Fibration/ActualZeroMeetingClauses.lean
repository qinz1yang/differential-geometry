import DifferentialGeometry.Geometry.Fibration.ActualEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsResidualApplications

/-!
# SGP01's zero clauses on the actual zero family (FC09/FC13 with LC62's local comparison)

Blueprint `master207B.tex`, SGP01 (`lem:fibration-slim-comparison-list`, B:4353–4408): "With the
zero-radius parameter `T₀ ≥ 1600L`, at most one zero support meets `D_i`. If it does, its radius
`R₀` satisfies `R₀/R_i ≥ T₀/20` and the whole `D_i` is inside FC13's buffered closed radial
shell", `L = 10⁶Δ`, `D_i = B(p_i, .95LR_i)`; the same assertions in TCP01 (B:5259) and EGP02.
On the final family with LC62's local comparison `P : LocalChartPacketsR`:

* `zero_meeting_clauses_ZERO` (any reference point `p`, any comparison radius `ℓρ(p)` with
  `2ℓ/T + 2ℓΛ ≤ 1/40`): at most one LC31 zero support of `P.zero` meets `B(p, ℓρ(p))`; for a
  meeting one, every point `x` of the ball lies in the buffered shell `3r/20 < d(k,x) < 19r/20`,
  in LC73's CLOSED shell `r/10 ≤ d(k,x) ≤ 10r`, and has `T/20 ≤ r/ρ(x)` (LC62); the ORIGINAL
  radial function is smooth on an open neighbourhood of the ball.
* `sgp01_zero_clauses`: SGP01's zero clauses (`ℓ = .95L`, `T ≥ 1600L`, `LΛ < 10⁻⁵`), with
  `R₀/R_i ≥ T/20` at the reference point. The reference point need not be a slim centre (the
  row's `i ∈ I_s` is unused; strengthening, verbatim form as an `example`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
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
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricN_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedN_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricC_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC09/FC13 with LC62 on the actual zero family**, at a reference ball `B(p, ℓρ(p))` with
`2ℓ/T + 2ℓΛ ≤ 1/40`: at most one zero support meets the ball; a meeting one has every point of the
ball in its buffered shell `3r/20 < d(k,·) < 19r/20`, in LC73's closed shell `r/10 ≤ d(k,·) ≤ 10r`,
with `T/20 ≤ r/ρ(x)`, and its original radial function is smooth near the ball. -/
theorem zero_meeting_clauses_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (he : e < 1 / 40) (hT : 0 < T) (p : X) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) :
    (∀ k₁ (hk₁ : k₁ ∈ P.zero.centres) k₂ (hk₂ : k₂ ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k₁ hk₁).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty →
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k₂ hk₂).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty → k₁ = k₂) ∧
    ∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty →
      (∀ x ∈ ball p (ℓ * ρ p),
        3 / 20 * (P.zero.zero k hk).radius < dist k x ∧
          dist k x < 19 / 20 * (P.zero.zero k hk).radius ∧
          (P.zero.zero k hk).radius / 10 ≤ dist k x ∧
          dist k x ≤ 10 * (P.zero.zero k hk).radius ∧
          T / 20 ≤ (P.zero.zero k hk).radius / ρ x) ∧
      ∃ O : Set X, IsOpen O ∧ ball p (ℓ * ρ p) ⊆ O ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.zero.zero k hk).radial O := by
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := P.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hsmall' : 2 * (ℓ / T) + 2 * (ℓ * ((Real.toNNReal Λ : NNReal) : ℝ)) ≤ 1 / 40 := by
    rwa [hc]
  obtain ⟨huniq, hshell⟩ := zero_supports_meeting_ball_shell P.zero hρL he hT p hℓ hsmall'
  refine ⟨huniq, fun k hk hmeet => ?_⟩
  obtain ⟨hball, hO⟩ := hshell k hk hmeet
  refine ⟨fun x hx => ?_, hO⟩
  have hr := (P.zero.zero k hk).radius_pos
  obtain ⟨h1, h2⟩ := hball x hx
  refine ⟨h1, h2, by linarith, by linarith, ?_⟩
  exact P.zero_local_comparison k hk x (by linarith)

/-- The smallness of SGP01's comparison radius `ℓ = .95L` (`L = 10⁶Δ`) for `T ≥ 1600L` and
`LΛ < 10⁻⁵`. -/
theorem sgp01_zero_smallness_ZERO {Δ Λ T : ℝ} (hΔ : 1 ≤ Δ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hT : 1600 * (1000000 * Δ) ≤ T) :
    0 < T ∧ 0 < 95 / 100 * (1000000 * Δ) ∧
      2 * (95 / 100 * (1000000 * Δ) / T) + 2 * (95 / 100 * (1000000 * Δ) * Λ) ≤ 1 / 40 := by
  have hL : 0 < 1000000 * Δ := by positivity
  have hT0 : 0 < T := by linarith
  refine ⟨hT0, by positivity, ?_⟩
  have hq : 95 / 100 * (1000000 * Δ) / T ≤ 1 / 1600 := by
    rw [div_le_iff₀ hT0]
    linarith
  have hΛL : 95 / 100 * (1000000 * Δ) * Λ ≤ 1 / 100000 := by nlinarith
  linarith

/-- **SGP01, zero clauses** (`lem:fibration-slim-comparison-list`), at `D_i = B(i, .95Lρ(i))`,
`L = 10⁶Δ`, `T ≥ 1600L`, `LΛ < 10⁻⁵`: at most one zero support meets `D_i`; a meeting one has
`R₀/R_i ≥ T/20`, the whole `D_i` inside its buffered shell `3R₀/20 < d(k,·) < 19R₀/20` (and inside
LC73's closed shell `R₀/10 ≤ d(k,·) ≤ 10R₀`, with `T/20 ≤ R₀/ρ(x)` at every `x ∈ D_i`), and its
original radial function smooth on an open neighbourhood of `D_i`. -/
theorem sgp01_zero_clauses
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (i : X) :
    (∀ k₁ (hk₁ : k₁ ∈ P.zero.centres) k₂ (hk₂ : k₂ ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k₁ hk₁).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k₂ hk₂).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
      k₁ = k₂) ∧
    ∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
      T / 20 ≤ (P.zero.zero k hk).radius / ρ i ∧
      (∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
        3 / 20 * (P.zero.zero k hk).radius < dist k x ∧
          dist k x < 19 / 20 * (P.zero.zero k hk).radius ∧
          (P.zero.zero k hk).radius / 10 ≤ dist k x ∧
          dist k x ≤ 10 * (P.zero.zero k hk).radius ∧
          T / 20 ≤ (P.zero.zero k hk).radius / ρ x) ∧
      ∃ O : Set X, IsOpen O ∧ ball i (95 / 100 * (1000000 * Δ) * ρ i) ⊆ O ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.zero.zero k hk).radial O := by
  obtain ⟨hT0, hℓ, hsmall⟩ := sgp01_zero_smallness_ZERO hΔ hLΛ hT
  obtain ⟨huniq, hcl⟩ := zero_meeting_clauses_ZERO P hΛ he hT0 i hℓ hsmall
  refine ⟨huniq, fun k hk hmeet => ?_⟩
  obtain ⟨hball, hO⟩ := hcl k hk hmeet
  have hi : i ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i) := mem_ball_self (mul_pos hℓ (hρ i))
  exact ⟨(hball i hi).2.2.2.2, hball, hO⟩

/-- SGP01's zero clauses in the row's verbatim form (reference centre `i ∈ I_s`). -/
example
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) :
    ∀ i ∈ P.slim.centres, ∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
      T / 20 ≤ (P.zero.zero k hk).radius / ρ i :=
  fun i _ k hk hmeet => ((sgp01_zero_clauses P hΛ hΔ hLΛ he hT i).2 k hk hmeet).1

end DifferentialGeometry.Geometry.Collapse
