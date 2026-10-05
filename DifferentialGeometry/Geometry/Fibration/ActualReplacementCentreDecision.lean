import DifferentialGeometry.Geometry.Fibration.ActualReplacementExclusionsApplications

/-!
# FDC01, first step: the selected edge centre is neither zero-stratum nor slim

Blueprint `master207B.tex`, FDC01 (`lem:fibration-actual-replacement-edge-chart`, B:7174–7199);
draft 61 §6.2, step one of (Repl∂) ("prove first that the selected centre `p_i` is a nonslim
one-stratum point; strong-edge quality alone cannot replace this step").

FDC01 uses `q ∈ M₂` only through two ORIGINAL-coordinate facts: `q` lies outside every selected
zero ball `B(z, .38R_z)` (ZSP02 puts that ball in `int Z`, and `M₂ ⊆ M ∖ int Z`), and `q` lies
outside every selected slim region `{d(q, k) < 9Δρ(k), |η_k(q)| < 10Δ}` (GAF07 and (SK) put it in
`int_{M₁} M^slim`, which is removed from `M₂`). With exactly these two hypotheses:

* `fdc01_centre_exclusions_FDC` (`LocalChartPacketsC14`): for `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`,
  `t(q) ≤ 4.01Δ`, the centre `p_i` is not zero-stratum, and if it is one-stratum it is nonslim
  (LFR44's nonslim hypothesis at `p_i`, the ORIGINAL slim predicate at scale `ρ(p_i)`).

The inclusions of `M₂` into these two complements are the ZSP02 / GAF07 bindings of the final
map, not claimed here.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14Dec_FDC
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14Dec_FDC
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14Dec_FDC
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FDC01's centre decision** (`LocalChartPacketsC14`): for `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`,
`t(q) ≤ 4.01Δ`, lying outside every selected zero ball `B(z, .38R_z)` and outside every selected
slim region `{d(q, k) < 9Δρ(k), |η_k(q)| < 10Δ}`, the selected edge centre `p_i` is not
zero-stratum, and if it is one-stratum it is nonslim. -/
theorem fdc01_centre_exclusions_FDC
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    {i : X} (hi : i ∈ P.edge.centres) {q : X} (hq : q ∈ ball i (100 * Δ * ρ i))
    (hηq : |P.edge.coord i q| ≤ 401 / 100 * Δ) (htq : P.edge.smoothing q / ρ q ≤ 401 / 100 * Δ)
    (hZ : ∀ z (hz : z ∈ P.zero.centres), 38 / 100 * (P.zero.zero z hz).radius ≤ dist q z)
    (hS : ∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρ k →
      10 * Δ ≤ |(P.slim.centre k hk).coord q|) :
    i ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0 ∧
      (i ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1 →
        ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 ((0 : ℝ), z))
              (β 1)))) := by
  obtain ⟨-, hzero, hslim⟩ :=
    fdc01_exclusion_inputs_C14 P hΔ hΛ hμ hτ hlam hT hσs hσs1 hi hq hηq htq
  refine ⟨fun h0 => ?_, fun h1 hsl => ?_⟩
  · obtain ⟨z, hz, -, hqz⟩ := hzero h0
    exact absurd (hZ z hz) (not_le.mpr hqz)
  · obtain ⟨k, hk, hqk, hηk⟩ := hslim h1 hsl
    exact absurd (hS k hk hqk) (not_le.mpr hηk)

end DifferentialGeometry.Geometry.Collapse
