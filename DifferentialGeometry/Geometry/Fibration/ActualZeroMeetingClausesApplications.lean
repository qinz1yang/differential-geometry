import DifferentialGeometry.Geometry.Fibration.ActualZeroMeetingClauses

/-!
# LC73's inputs on the reference balls of SGP01, TCP01 and EGP02

Consumer of `zero_meeting_clauses_ZERO`: if a zero support of `P.zero` meets a reference ball, every
point `x` of the ball lies in LC73's CLOSED shell `r/10 ≤ d(k, x) ≤ 10r` and has `Λz ≤ r/ρ(x)`
for every LC73 ratio threshold with `20Λz ≤ T` — exactly the hypotheses under which LC73's
adapted coordinate is produced at `x` (the zero blocks of SGP03, TCP03 and EGP04: "LC73 at EVERY
`x ∈ D_i`", B:5431). Instances at the three reference balls: slim `B(i, .95Lρ(i))` (SGP01),
circle `B(i, 10ρ(i))` (TCP01), edge `B(i, 20Δρ(i))` (EGP02), `L = 10⁶Δ`, `T ≥ 1600L`.
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
local instance instMetricN'_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedN'_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricC'_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **LC73's inputs on a met reference ball**: a zero support of `P.zero` meeting `B(p, ℓρ(p))`
(`2ℓ/T + 2ℓΛ ≤ 1/40`) puts every point of the ball in LC73's closed shell, with
`Λz ≤ r/ρ(x)` for every ratio threshold `20Λz ≤ T`. -/
theorem zero_lc73_inputs_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (he : e < 1 / 40) (hT : 0 < T) (p : X) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) {Λz : ℝ} (hΛz : 20 * Λz ≤ T)
    {k : X} (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty) :
    ∀ x ∈ ball p (ℓ * ρ p), (P.zero.zero k hk).radius / 10 ≤ dist k x ∧
      dist k x ≤ 10 * (P.zero.zero k hk).radius ∧ Λz ≤ (P.zero.zero k hk).radius / ρ x := by
  intro x hx
  obtain ⟨-, -, h3, h4, h5⟩ :=
    (zero_meeting_clauses_ZERO P hΛ he hT p hℓ hsmall).2 k hk hmeet |>.1 x hx
  exact ⟨h3, h4, by linarith⟩

/-- LC73's inputs on SGP01's slim reference ball `D_i = B(i, .95Lρ(i))`. -/
theorem sgp01_zero_lc73_inputs_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) {Λz : ℝ} (hΛz : 20 * Λz ≤ T) (i : X) {k : X}
    (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty) :
    ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), (P.zero.zero k hk).radius / 10 ≤ dist k x ∧
      dist k x ≤ 10 * (P.zero.zero k hk).radius ∧ Λz ≤ (P.zero.zero k hk).radius / ρ x := by
  obtain ⟨hT0, hℓ, hsmall⟩ := sgp01_zero_smallness_ZERO hΔ hLΛ hT
  exact zero_lc73_inputs_ZERO P hΛ he hT0 i hℓ hsmall hΛz hk hmeet

/-- LC73's inputs on TCP01's circle reference ball `D_i = B(i, 10ρ(i))`. -/
theorem tcp01_zero_lc73_inputs_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) {Λz : ℝ} (hΛz : 20 * Λz ≤ T) (i : X) {k : X}
    (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty) :
    ∀ x ∈ ball i (10 * ρ i), (P.zero.zero k hk).radius / 10 ≤ dist k x ∧
      dist k x ≤ 10 * (P.zero.zero k hk).radius ∧ Λz ≤ (P.zero.zero k hk).radius / ρ x := by
  have hT0 : 0 < T := by nlinarith
  have hsmall : 2 * (10 / T) + 2 * (10 * Λ) ≤ 1 / 40 := by
    have hq : 10 / T ≤ 1 / 160000000 := by
      rw [div_le_iff₀ hT0]
      nlinarith
    have hΛ1 : Λ ≤ 1 / 100000000000 := by nlinarith
    linarith
  exact zero_lc73_inputs_ZERO P hΛ he hT0 i (by norm_num) hsmall hΛz hk hmeet

/-- LC73's inputs on EGP02's edge reference ball `D_i = B(i, 20Δρ(i))`. -/
theorem egp02_zero_lc73_inputs_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) {Λz : ℝ} (hΛz : 20 * Λz ≤ T) (i : X) {k : X}
    (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty) :
    ∀ x ∈ ball i (20 * Δ * ρ i), (P.zero.zero k hk).radius / 10 ≤ dist k x ∧
      dist k x ≤ 10 * (P.zero.zero k hk).radius ∧ Λz ≤ (P.zero.zero k hk).radius / ρ x := by
  have hΔ0 : 0 < Δ := by linarith
  have hT0 : 0 < T := by nlinarith
  have hsmall : 2 * (20 * Δ / T) + 2 * (20 * Δ * Λ) ≤ 1 / 40 := by
    have hq : 20 * Δ / T ≤ 1 / 80000000 := by
      rw [div_le_iff₀ hT0]
      nlinarith
    have hΛ1 : 20 * Δ * Λ ≤ 1 / 5000000000 := by nlinarith
    linarith
  exact zero_lc73_inputs_ZERO P hΛ he hT0 i (by positivity) hsmall hΛz hk hmeet

end DifferentialGeometry.Geometry.Collapse
