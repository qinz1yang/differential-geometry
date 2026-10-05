import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsZeroProducer
import DifferentialGeometry.Geometry.Fibration.ActualZeroMeetingClausesApplications

/-!
# Consumers of LC73's zero shell clauses on reference balls (`LocalChartPacketsZ`)

Blueprint 207B, SGP02 (B:4473: "For the zero coordinate, SGP01 puts `p_i` in the required shell.
LC73/LCP04 give an actual `(1, β₁)`-splitting there whose real coordinate is EXACTLY
`d(p₀,·) − d(p₀,p_i)` in reference units"), TCP02 (B:5362), TCP03 (B:5431: "LC73 at EVERY
`x ∈ D_i`"):

* `zero_shell_split_of_meets_ZERO`: if a zero support meets `B(p, ℓρ(p))`
  (`2ℓ/T + 2ℓΛ ≤ 1/40`), then at EVERY point `x` of the ball there is an actual Kleiner–Lott
  `(1, β₁)`-splitting of `(X, ρ(x)⁻¹ d, x)` with real coordinate exactly
  `ρ(x)⁻¹ (d(k, ·) − d(k, x))` (G1's shell clause + the field `zero_shell_split`);
* `sgp01_zero_shell_split_ZERO`: the same on SGP01's `D_i = B(i, .95Lρ(i))` (`T ≥ 1600L`), in
  particular at `p_i` itself — the input of SGP02's (R0);
* `zero_adapted_ratio_ZERO`: LC73's field `zero_adapted` applies at every point `x` of a met ball
  with the ratio `λ = r/ρ(x)` (its hypotheses `r/10 ≤ d(k, x) ≤ 10r`, `Λz ≤ r/ρ(x)` hold when
  `20Λz ≤ T`): the zero-block input of SGP03 / TCP03 / EGP04.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry
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
local instance instMetricNZ_ZERO
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ_ZERO
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ_ZERO
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **X82's exact-coordinate splitting at every point of a met reference ball.** If a zero support
of `P.zero` meets `B(p, ℓρ(p))` (`2ℓ/T + 2ℓΛ ≤ 1/40`), every point `x` of the ball carries an
actual Kleiner–Lott `(1, β₁)`-splitting of `(X, ρ(x)⁻¹ d, x)` whose real coordinate is exactly
`ρ(x)⁻¹ (d(k, ·) − d(k, x))`. -/
theorem zero_shell_split_of_meets_ZERO
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    (hΛ : 0 ≤ Λ) (he : e < 1 / 40) (hT : 0 < T) (p : X) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) {k : X} (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty) :
    ∀ x ∈ ball p (ℓ * ρ p),
      ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
        ∃ (z : Zf) (F : @KleinerLottApprox X
          (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
          (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) inferInstance
          x (WithLp.toLp 2 (0, z)) (β 1)),
          ∀ y : X, (@KleinerLottApprox.toFun X
            (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
            (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) inferInstance
            x (WithLp.toLp 2 (0, z)) (β 1) F y).fst = WithLp.toLp 2
            (Function.const (Fin 1) ((ρ x)⁻¹ * (dist k y - dist k x))) := by
  intro x hx
  obtain ⟨-, -, h3, h4, -⟩ :=
    (zero_meeting_clauses_ZERO P.toLocalChartPacketsR hΛ he hT p hℓ hsmall).2 k hk hmeet |>.1
      x hx
  exact P.zero_shell_split k hk x h3 h4

/-- **The input of SGP02's (R0)**: if a zero support meets SGP01's `D_i = B(i, .95Lρ(i))`
(`L = 10⁶Δ`, `T ≥ 1600L`, `LΛ < 10⁻⁵`, `e < 1/40`), every point `x ∈ D_i` — in particular `p_i`
itself — carries an actual `(1, β₁)`-splitting of `(X, ρ(x)⁻¹ d, x)` with real coordinate exactly
`ρ(x)⁻¹ (d(p₀, ·) − d(p₀, x))`. -/
theorem sgp01_zero_shell_split_ZERO
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (i : X) {k : X} (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty) :
    ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
      ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
        ∃ (z : Zf) (F : @KleinerLottApprox X
          (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
          (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) inferInstance
          x (WithLp.toLp 2 (0, z)) (β 1)),
          ∀ y : X, (@KleinerLottApprox.toFun X
            (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
            (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) inferInstance
            x (WithLp.toLp 2 (0, z)) (β 1) F y).fst = WithLp.toLp 2
            (Function.const (Fin 1) ((ρ x)⁻¹ * (dist k y - dist k x))) := by
  obtain ⟨hT0, hℓ, hsmall⟩ := sgp01_zero_smallness_ZERO hΔ hLΛ hT
  exact zero_shell_split_of_meets_ZERO P hΛ he hT0 i hℓ hsmall hk hmeet

/-- **LC73 applies at every point of a met reference ball with the ratio `λ = r/ρ(x)`**: the
hypotheses of the field `zero_adapted` at `q = x`, `λ = r/ρ(x)` (closed shell, `0 < λ`,
`Λz ≤ λ`) hold when `20Λz ≤ T`. -/
theorem zero_adapted_ratio_ZERO
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    (hΛ : 0 ≤ Λ) (he : e < 1 / 40) (hT : 0 < T) (hΛz : 20 * Λz ≤ T) (p : X) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) {k : X} (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty) :
    ∀ x ∈ ball p (ℓ * ρ p), (P.zero.zero k hk).radius / 10 ≤ dist k x ∧
      dist k x ≤ 10 * (P.zero.zero k hk).radius ∧ 0 < (P.zero.zero k hk).radius / ρ x ∧
      Λz ≤ (P.zero.zero k hk).radius / ρ x := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ :=
    zero_lc73_inputs_ZERO P.toLocalChartPacketsR hΛ he hT p hℓ hsmall hΛz hk hmeet x hx
  exact ⟨h1, h2, div_pos (P.zero.zero k hk).radius_pos (hρ x), h3⟩

/-- **LC73's splitting at every point of a met reference ball has the exact radial coordinate**:
the splitting `κ` of the field `zero_adapted` at `x` with `λ = r/ρ(x)` (metric `λ · r⁻¹ d`) has real
coordinate exactly `ρ(x)⁻¹ (d(k, ·) − d(k, x))`. -/
theorem zero_adapted_coordinate_ZERO
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    (hΛ : 0 ≤ Λ) (he : e < 1 / 40) (hT : 0 < T) (hΛz : 20 * Λz ≤ T) (p : X) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) {k : X} (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty) :
    ∀ x ∈ ball p (ℓ * ρ p),
      ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
        ∃ (z : Zf) (κ : @KleinerLottApprox X (WithLp 2 (ℝ × Zf))
          ((mX.rescale (P.zero.zero k hk).radius⁻¹
              (inv_pos.mpr (P.zero.zero k hk).radius_pos)).rescale
            ((P.zero.zero k hk).radius / ρ x) (div_pos (P.zero.zero k hk).radius_pos (hρ x)))
          inferInstance x (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
          ∀ y, (@KleinerLottApprox.toFun X (WithLp 2 (ℝ × Zf))
            ((mX.rescale (P.zero.zero k hk).radius⁻¹
              (inv_pos.mpr (P.zero.zero k hk).radius_pos)).rescale
            ((P.zero.zero k hk).radius / ρ x) (div_pos (P.zero.zero k hk).radius_pos (hρ x)))
            inferInstance x (WithLp.toLp 2 ((0 : ℝ), z)) (β 1) κ y).fst =
              (ρ x)⁻¹ * (dist k y - dist k x) := by
  intro x hx
  obtain ⟨h1, h2, h3, h4⟩ := zero_adapted_ratio_ZERO P hΛ he hT hΛz p hℓ hsmall hk hmeet x hx
  obtain ⟨-, Zf, mZ, z, κ, hκ, -⟩ := P.zero_adapted k hk x h1 h2 _ h3 h4
  refine ⟨Zf, mZ, z, κ, fun y => ?_⟩
  rw [hκ y]
  have hr := (P.zero.zero k hk).radius_pos
  have hx' := hρ x
  change (P.zero.zero k hk).radius / ρ x * ((P.zero.zero k hk).radius⁻¹ * @dist X mX.toDist k y -
    (P.zero.zero k hk).radius⁻¹ * @dist X mX.toDist k x) = (ρ x)⁻¹ * (dist k y - dist k x)
  field_simp

end DifferentialGeometry.Geometry.Collapse
