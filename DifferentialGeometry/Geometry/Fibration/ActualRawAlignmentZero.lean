import DifferentialGeometry.Geometry.Fibration.ActualZeroRawAlignmentApplications

/-!
# TCP02 as one complete row on the zero family: (TR) for the listed charts and (TR0)

Blueprint `master207B.tex`, TCP02 (B:5311–5369): with early `E, δ` and `β₂` chosen before `Δ`,
every listed constant-radius coordinate (circle, slim, edge) has on `B(p_i, 1000ρ(i))` one
coisometry with (TR), and every meeting zero block has a unit row `A₀` with (TR0)
(B:5327–5333, proof B:5362–5367).

* `tcp02_rowZ`: the complete row on `P : LocalChartPacketsZ` under ONE threshold choice: C14-KA3's
  `tcp02_row` (circle / slim / edge, applied to the underlying `LocalChartPackets`) and C14-ZERO's
  `tcp02_zero_supplier_ZERO` (zero), with `σ` the minimum of the two early radii and `η₁` the
  minimum of the two quality bounds (the zero bound is independent of `Δ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ_TCP02_KA5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ_TCP02_KA5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ_TCP02_KA5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP02, complete row on the zero family.** For a target error `E₀` and the exclusion quality
`ν` (`3ν ≤ β₃ < 1`) there are an early `σ ≤ 1/1000`, a circle quality bound `η₂` and, for every
`Δ ≥ 1`, a quality bound `η₁` such that every actual `P : LocalChartPacketsZ` in the FC07 ranges
with `3β₂ ≤ σ`, `β₂ ≤ η₂`, `β₁, b ≤ η₁`, `σ⁻¹ ≤ Lmax` has, at every circle centre `i`:
(TR) for every listed circle, slim and edge chart (`tcp02_row`) and (TR0) for every zero ball whose
support meets `D_i = B(i, 10ρ(i))`: a unit row `A₀` with
`‖ρ(i)⁻¹ (d(p₀, x) − d(p₀, i)) − A₀ u_i(x)‖ < E₀` on `B(i, 1000ρ(i))`. -/
theorem tcp02_rowZ {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ Δ : ℝ, 1 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
      (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → β 1 ≤ η₁ → b ≤ η₁ → σ⁻¹ ≤ Lmax →
      ∀ i ∈ P.circle.centres,
        (∀ j ∈ P.circle.centres, (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • circleRaw_KA3
                  P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets j x -
                A (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
                  i x) -
                (ρ j / ρ i) • circleRaw_KA3
                  P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets j i‖ < E₀) ∧
        (∀ j ∈ P.slim.centres, (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] E1, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j x) -
                A (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
                  i x) -
                (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j i)‖ <
                E₀) ∧
        (∀ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] E1, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j x) -
                A (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
                  i x) -
                (ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j i)‖ <
                E₀) ∧
        ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A₀ : ℝ² →L[ℝ] E1,
            A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k i)) -
                A₀ (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
                  i x)‖ < E₀ := by
  obtain ⟨σ₀, hσ₀, hσ₀1, η₂, hη₂, hrow⟩ := tcp02_row hE hν hν1
  obtain ⟨σz, hσz, -, ηz, hηz, hzero⟩ := tcp02_zero_supplier_ZERO hE hν hν1
  refine ⟨min σ₀ σz, lt_min hσ₀ hσz, (min_le_left _ _).trans hσ₀1, η₂, hη₂, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, hrow'⟩ := hrow Δ hΔ
  refine ⟨min η₁ ηz, lt_min hη₁ hηz, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P hΛ hμ
    hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hβ1 hb hσL i hi
  have hσm := lt_min hσ₀ hσz
  have hL₀ : σ₀⁻¹ ≤ Lmax := (inv_anti₀ hσm (min_le_left _ _)).trans hσL
  have hLz : σz⁻¹ ≤ Lmax := (inv_anti₀ hσm (min_le_right _ _)).trans hσL
  obtain ⟨hc, hsl, hed⟩ := hrow' P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
    hΛ hμ hτ hLΛ hLmax he hT hν3 hβ3 (hβ2σ.trans (min_le_left _ _)) hβ2
    (hβ1.trans (min_le_left _ _)) (hb.trans (min_le_left _ _)) hL₀ i hi
  exact ⟨hc, hsl, hed, fun k hk hmeet => hzero P hΛ hΔ hLΛ he hT hν3 hβ3
    (hβ2σ.trans (min_le_right _ _)) (hβ1.trans (min_le_right _ _)) hLz i hi k hk hmeet⟩

end DifferentialGeometry.Geometry.Collapse
