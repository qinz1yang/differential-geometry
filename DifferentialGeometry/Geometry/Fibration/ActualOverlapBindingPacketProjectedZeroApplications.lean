import DifferentialGeometry.Geometry.Fibration.ActualOverlapBindingPacketProjectedZero
import DifferentialGeometry.Geometry.Fibration.ActualOverlapBindingPacketZero
import DifferentialGeometry.Geometry.Fibration.ActualZeroConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualRawAlignmentZeroApplications
import DifferentialGeometry.Geometry.Fibration.ActualEdgeZeroComparison
import DifferentialGeometry.Geometry.Fibration.ActualSlimZeroComparison

/-!
# FC23, zero radial row: items 1–4 assembled at the two-stratum base

Lane S-ROWS-FIN (suffix `_SRF`), consumer of `ActualOverlapBindingPacketProjectedZero` (G1).
Blueprint `master207B.tex`, FC23 (B:1505–1541), binding matrix row "Zero radial".

* `fc23_zero_radial_row_SRF` — the ZERO RADIAL ROW at the two-stratum base `D_i = B(i, 10ρ(i))`,
  items 1–4 on ONE actual `LocalChartPacketsZ` and ONE zero ball meeting `D_i`:
  items 1–2 = `fc23_items12_zero_RFC` (FC13's shell, LC73's scale ratio `Λz ≤ R₀/ρ(i)`, the long
  endpoint `y` with the reference circle's original tests and LC73's original radial test domain),
  item 3 = TCP02's (TR0) and item 4 = TCP03's zero block (TC) (`tcp03_zero_row`, which carries
  `tcp02_rowZ`'s (TR0) at accuracy `θ²/2000` for the SAME unit row `A₀`).
  The thresholds are those of `tcp03_zero_row`; the two numerical side conditions of
  `fc23_items12_zero_RFC` (`ζ ≤ 1/1000`, `β₂ ≤ 1/1000`) follow from `ζ ≤ θ²/1000`, `θ < 1` and
  `3β₂ ≤ σ ≤ 1/1000`, so they are not hypotheses.
* `fc23_zero_edgebase_row_SRF`, `fc23_zero_slimbase_row_SRF` — the zero radial row at the EDGE base
  (`D_i = B(i, 20Δρ(i))`, EGP04's `egp04_zero_row` = items 3–4) and at the SLIM base
  (`D_i = B(i, .95·10⁶Δρ(i))`, SGP03's `sgp03_zero_row` = items 3–4) on the complete closed
  family `LocalChartPacketsC14Z`, with items 1–2 (`fc23_edgebase_zero_row_RWS`,
  `fc23_slimbase_zero_row_RWS`, scale ratio derived, no ratio hypothesis) for the SAME sign `a₀`
  that items 3–4 select. The numerical premises are those of `fc23_zero_premises_RWS`.
* Consumer `fc23_zero_radial_row_far_SRF`: the two-stratum row gives, at every `x ∈ D_i` and unit
  `ξ`, an endpoint `y` with `ρ(i) < d(x, y)` together with the unit row `A₀` of items 3–4.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ_SRF
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ_SRF
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ_SRF
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **FC23, the zero radial row, items 1–4 at the two-stratum base** (B:1505–1541, binding matrix
row "Zero radial"). For `0 < θ < 1` and `0 < ν < 1` there are an early `σ ≤ 1/1000`, a circle
quality bound `η₂`, an adaptation bound `γ₀` and a zero quality bound `η₁` (independent of `Δ`)
such that every actual `P : LocalChartPacketsZ` in the zero ranges (`0 ≤ Λ`, `1 ≤ Δ`,
`10⁶ΔΛ < 10⁻⁵`, `e < 1/40`, `T ≥ 1600·10⁶Δ`, `20Λz ≤ T`, `3ν ≤ β₃ < 1`, `3β₂ ≤ σ`, `β₂ ≤ η₂`,
`γ ≤ γ₀`, `β₁ ≤ η₁`, `0 < ζ ≤ θ²/1000`, `εr ≤ θ/100`, `σ⁻¹ ≤ Lmax`) has, at every circle centre
`i` and every zero ball (centre `k`, radius `R₀`) whose cutoff support meets `D_i = B(i, 10ρ(i))`:
items 1–2 (`Λz ≤ R₀/ρ(i)`; at every `x ∈ D_i` FC13's shell and, for every unit `ξ`, the long
endpoint `y` with the original tests and LC73's test domain) and ONE unit row `A₀` with item 3
(TR0 on `B(i, 1000ρ(i))` at accuracy `θ²/2000`) and item 4 ((TC) on `D_i`: value `≤ θ/2` and
differential `≤ (θ/2)|w|` in the norm of `ρ(i)⁻²g`). -/
theorem fc23_zero_radial_row_SRF {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν)
    (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
      (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V ζ Λz),
      0 ≤ Λ → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → β 1 ≤ η₁ → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres), ∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
        (Λz ≤ (P.zero.zero k hk).radius / ρ i ∧
          ∀ x ∈ ball i (10 * ρ i),
            (P.zero.zero k hk).radius / 10 ≤ dist k x ∧
              dist k x ≤ 10 * (P.zero.zero k hk).radius ∧
            ∀ ξ : ℝ², ‖ξ‖ = 1 →
            ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
              ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
              397 * ρ i ≤ dist x y ∧ dist x y ≤ (400 + 3 * β 2) * ρ i ∧
              ‖circleRaw_KA3
                  P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets i y -
                circleRaw_KA3
                  P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets i x -
                (400 : ℝ) • ξ‖ < 2 * β 2 ∧
              x ∈ ball i (200 * ρ i) ∧ y ∈ ball i (201 * 10000 * ρ i) ∧ 201 * ρ i < dist x y ∧
              y ∈ ball i (1000 * ρ i) ∧ ρ i < dist x y ∧ ζ * dist x y < ρ i) ∧
        ∃ A₀ : ℝ² →L[ℝ] ℝ¹,
          A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
          (∀ x, dist x i < 1000 * ρ i →
            ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k i)) -
              A₀ (circleRaw_KA3
                P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets i x)‖ <
              θ ^ 2 / 2000) ∧
          ∀ x ∈ ball i (10 * ρ i),
            ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                  ((P.zero.zero k hk).radial x - (P.zero.zero k hk).radial i)) -
                A₀ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤ θ / 2 ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                    mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w) -
                  A₀ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  obtain ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, η₁, hη₁, hrow⟩ := tcp03_zero_row hθ hθ1 hν hν1
  refine ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P hΛ
    hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ2 hγ hβ1 hζ hζθ hεr hΛz hσL i hi k hk hmeet
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  have hζ1 : ζ ≤ 1 / 1000 := by linarith
  have hβ1000 : β 2 ≤ 1 / 1000 := by linarith
  exact ⟨fc23_items12_zero_RFC P hΛ hΔ hLΛ he hT hΛz hζ hζ1 hβ1000 hi hk hmeet,
    hrow P hΛ hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ2 hγ hβ1 hζ hζθ hεr hΛz hσL i hi k hk hmeet⟩


/-- **FC23, the zero radial row at the EDGE base** (EGP04, `D_i = B(i, 20Δρ(i))`): items 3–4 and
items 1–2 on the complete closed family `LocalChartPacketsC14Z`, with the scale ratio DERIVED.
For `Δ ≥ 1`, `β₂ < 10⁻⁶` and `0 < θ < 1` there are `Lc`, `η₀` such that every actual `P` with
`egp04_zero_row`'s hypotheses has, at every edge centre `i` and zero ball (`k`, `R₀`) meeting
`D_i`, ONE sign `a₀ = ±1` with: (EGP04) `|s₀η₀ − (a₀η_i + s₀η₀(p_i))| < θ` and
`|s₀dη₀(w) − a₀dη_i(w)| < θ` for unit `w` on all of `D_i`; and at every `x ∈ D_i`: the ratio
`.99ρ(i) < ρ(x) < 1.01ρ(i)`, LC73's shell and scale clause `Λz ≤ R₀/ρ(x)`, and the reference lift
`y` of sign `a₀` in LC73's test domain `ρ(x) < d(x, y) < ζ⁻¹ρ(x)` (EGP04's lift, the edge test
domains of `i`, the (ER) ball). -/
theorem fc23_zero_edgebase_row_SRF {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
        (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz oM),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        σc ≤ θ ^ 2 / 10 ^ 8 → μ * Δ < θ / 100 → 0 < ζ → ζ ≤ θ ^ 2 / 10 ^ 8 →
        ζ ≤ 1 / (1000 * (1000000 * Δ)) → εr < θ / (100 * (1000000 * Δ)) →
        ∀ i ∈ P.edge.centres, ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
          ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
            (|(P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial x -
                (a₀ * P.edge.coord i x +
                  (P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)| < θ ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                |(P.zero.zero k hk).radius / ρ i *
                    mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w -
                  a₀ * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ) ∧
            (99 / 100 * ρ i < ρ x ∧ ρ x < 101 / 100 * ρ i) ∧
            ((P.zero.zero k hk).radius / 10 ≤ dist k x ∧
              dist k x ≤ 10 * (P.zero.zero k hk).radius ∧
              Λz ≤ (P.zero.zero k hk).radius / ρ x) ∧
            ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
              ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
              |egpRaw P.edge i y - egpRaw P.edge i x - 400 * Δ * a₀| < 2 * b ∧
              (400 * Δ - 3 * b) * ρ i < dist x y ∧ dist x y < (400 * Δ + 3 * b) * ρ i ∧
              x ∈ ball i (100 * Δ * ρ i) ∧ y ∈ ball i (1000 * Δ * ρ i) ∧
              100 * Δ * ρ i < dist x y ∧
              x ∈ ball i (600 * Δ * ρ i) ∧ y ∈ ball i (600 * Δ * ρ i) ∧
              ρ x < dist x y ∧ dist x y < ζ⁻¹ * ρ x := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := egp04_zero_row hΔ hβ₂ hβ₂1 hθ hθ1
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨Lc, min η₀ (1 / (1000 * (1000000 * Δ))), hLc, lt_min hη₀ (by positivity), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hb hs hβ1 hLmax hΛ hLΛ he hT hTz hσc hμΔ hζ0 hζθ hζL hεr i hi k hk hmeet
  obtain ⟨a₀, ha₀, hal⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    ζ Λz P.toLocalChartPacketsZ (hb.trans (min_le_left _ _)) hs (hβ1.trans (min_le_left _ _))
    hLmax hΛ hLΛ he hT hTz hσc hμΔ hζ0 (hζθ) hζL hεr i hi k hk hmeet
  refine ⟨a₀, ha₀, fun x hx => ⟨hal x hx, ?_⟩⟩
  obtain ⟨hρx, hshell, htest⟩ := fc23_edgebase_zero_row_RWS P hΛ (hΔ) hLΛ he hT hTz
    (hb.trans (min_le_right _ _)) hζ0 hζL hi x hx
  exact ⟨hρx, hshell k hk hmeet, htest a₀ ha₀⟩


/-- **FC23, the zero radial row at the SLIM base** (SGP03, `D_i = B(i, .95Lρ(i))`, `L = 10⁶Δ`):
items 3–4 and items 1–2 on `LocalChartPacketsC14Z`, with the scale ratio DERIVED. For `Δ ≥ 1`,
the exclusion quality `β₂ < 1`, `0 < θ < 1`, `0 < E < θ²/10⁶` and `0 < δr < 1` there are `Lc`,
`η₀` such that every actual `P` with `sgp03_zero_row`'s hypotheses has, at every slim centre `i`
and zero ball (`k`, `R₀`) meeting `D_i`, ONE sign `a₀ = ±1` with SGP03's (R0) on `B(i, 30Lρ(i))`,
derivative and value bounds on all of `D_i`; and at every `x ∈ D_i`: the ratio
`.99ρ(i) < ρ(x) < 1.01ρ(i)`, LC73's shell and scale clause, and SGP03's reference lift `y` of sign
`a₀` (length `≈ 10Lρ(i)`, accuracy `δr`, the slim test domains of `i`, the (RA) ball) in LC73's
test domain `ρ(x) < d(x, y) < ζ⁻¹ρ(x)`. -/
theorem fc23_zero_slimbase_row_SRF {Δ β₂ θ E δr : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 < E) (hEθ : E < θ ^ 2 / 10 ^ 6) (hδr : 0 < δr)
    (hδ1 : δr < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
        (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz oM),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        ∀ i (hi : i ∈ P.slim.centres), ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
          ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧
            (∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
              |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * sgpRaw P.slim i x| < E) ∧
            (∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              |(P.zero.zero k hk).radius / ρ i *
                  mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w -
                a₀ * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| ≤
                θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
            (∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
              |(P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial x -
                (a₀ * (P.slim.centre i hi).coord x +
                  (P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)| < θ) ∧
            ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
              (99 / 100 * ρ i < ρ x ∧ ρ x < 101 / 100 * ρ i) ∧
              ((P.zero.zero k hk).radius / 10 ≤ dist k x ∧
                dist k x ≤ 10 * (P.zero.zero k hk).radius ∧
                Λz ≤ (P.zero.zero k hk).radius / ρ x) ∧
              ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
                ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
                |(ρ i)⁻¹ * dist x y - 10 * (1000000 * Δ)| < 2 * δr ∧
                10 * (1000000 * Δ) - δr < a₀ * (sgpRaw P.slim i y - sgpRaw P.slim i x) ∧
                x ∈ ball i (10 ^ 6 * Δ * ρ i) ∧ y ∈ ball i (10 ^ 6 * Δ / σs * ρ i) ∧
                10 ^ 6 * Δ * ρ i < dist x y ∧
                x ∈ ball i (30 * (1000000 * Δ) * ρ i) ∧ y ∈ ball i (30 * (1000000 * Δ) * ρ i) ∧
                ρ x < dist x y ∧ dist x y < ζ⁻¹ * ρ x := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := sgp03_zero_row hΔ hβ₂ hβ₂1 hθ hθ1 hE hEθ
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨Lc, min η₀ (min (1 / (1000 * (1000000 * Δ))) (δr / 100)), hLc,
    lt_min hη₀ (lt_min (by positivity) (by positivity)), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hTz hσs hσθ hvs hζ hζθ hζL hεr i hi k hk hmeet
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  obtain ⟨a₀, ha₀, hRA, hder, hval⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ
    γ δ εr e T V vs ζ Λz P.toLocalChartPacketsRVZ hβ2 (hβ1.trans (min_le_left _ _)) hLmax hΛ hLΛ
    he hT hTz hσs hσθ hvs hζ hζθ hζL hεr i hi k hk hmeet
  refine ⟨a₀, ha₀, hRA, hder, hval, fun x hx => ?_⟩
  obtain ⟨hρx, hshell, htest⟩ := fc23_slimbase_zero_row_RWS P hΛ hΔ hLΛ he hT hTz hδ1
    (hβ1.trans (min_le_right _ _)) hσs (by nlinarith) hζ hζL hi x hx
  exact ⟨hρx, hshell k hk hmeet, htest a₀ ha₀⟩


/-- **Consumer: the zero radial row yields, at every `x ∈ D_i` and unit `ξ`, a test endpoint farther
than `ρ(i)` from `x`, together with the unit row `A₀` of items 3–4 for the same `i`, `k`** (the
point-wise TR0 comparison at `x`, value `< θ²/2000`). Thresholds as in
`fc23_zero_radial_row_SRF`. -/
theorem fc23_zero_radial_row_far_SRF {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν)
    (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
      (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V ζ Λz),
      0 ≤ Λ → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → β 1 ≤ η₁ → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      ∀ i ∈ P.circle.centres, ∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
        ∀ x ∈ ball i (10 * ρ i), ∀ ξ : ℝ², ‖ξ‖ = 1 →
          (∃ y : X, ρ i < dist x y) ∧
          ∃ A₀ : ℝ² →L[ℝ] ℝ¹,
            A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
            ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k i)) -
              A₀ (circleRaw_KA3
                P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets i x)‖ <
              θ ^ 2 / 2000 := by
  obtain ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, η₁, hη₁, hrow⟩ := fc23_zero_radial_row_SRF hθ hθ1 hν hν1
  refine ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P hΛ
    hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ2 hγ hβ1 hζ hζθ hεr hΛz hσL i hi k hk hmeet x hx ξ hξ
  obtain ⟨⟨-, hitems⟩, A₀, hA₀, hTR, -⟩ := hrow P hΛ hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ2 hγ hβ1 hζ hζθ
    hεr hΛz hσL i hi k hk hmeet
  obtain ⟨-, -, hξrow⟩ := hitems x hx
  obtain ⟨y, -, -, -, -, -, -, -, -, -, -, hfar, -⟩ := hξrow ξ hξ
  exact ⟨⟨y, hfar⟩, A₀, hA₀, hTR x (by have := mem_ball.mp hx; linarith [(hρ i)])⟩

end DifferentialGeometry.Geometry.Collapse
