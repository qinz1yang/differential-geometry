import DifferentialGeometry.Geometry.Fibration.ActualZeroRawAlignmentApplications
import DifferentialGeometry.Geometry.Fibration.ActualEdgeRawAlignment

/-!
# EGP03 (ER0) in EGP03's own notation (`egpRaw`)

C14-KC2's EGP03 (`egp03_row`, Fib/ActualEdgeRawAlignment.lean) writes the edge raw coordinate as
`egpRaw L.edge j`; C14-ZERO's (ER0) supplier `egp03_zero_supplier_ZERO` uses C14-KA3's
`edgeRaw_KA3`. Both are the real factor of the SAME edge chart's normalized `(1, b)`-splitting:

* `egpRaw_eq_edgeRaw_KA3_ZERO`: `egpRaw L.edge j x = edgeRaw_KA3 L j x`;
* `egp03_zero_supplier_egpRaw_ZERO`: (ER0) with `u_i = egpRaw P.edge i` (same thresholds, same
  hypotheses as `egp03_zero_supplier_ZERO`), ready to be appended to `egp03_row`;
* consumer: `egp03_row`'s edge clause (ER) and (ER0) under one threshold choice (example).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZE_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZE_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZE_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- C14-KC2's and C14-KA3's edge raw coordinates agree: both are the real factor of the edge
chart's normalized `(1, b)`-splitting (zero off the edge centres). -/
theorem egpRaw_eq_edgeRaw_KA3_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc : ℝ}
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (j x : X) :
    egpRaw L.edge j x = edgeRaw_KA3 L j x := by
  by_cases hj : j ∈ L.edge.centres
  · rw [egpRaw_of_mem L.edge hj]
    unfold edgeRaw_KA3
    rw [dite_eq_left hj]
    rfl
  · unfold egpRaw edgeRaw_KA3
    rw [dite_eq_right hj, dite_eq_right hj]
    rfl

/-- **EGP03 (ER0) in EGP03's notation** (`u_i = egpRaw P.edge i`): the statement of
`egp03_zero_supplier_ZERO` with C14-KC2's raw coordinate. -/
theorem egp03_zero_supplier_egpRaw_ZERO {Δ ν E : ℝ} (hΔ : 1 ≤ Δ) (hν : 0 < ν)
    (hν1 : ν < 1 / 1000000) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ)
        (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        ∀ i ∈ P.edge.centres, ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
          ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (600 * Δ * ρ i),
            |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x| < E := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := egp03_zero_supplier_ZERO hΔ hν hν1 hE
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P
    hb hs hβ1 hLmax hΛ hLΛ he hT i hi k hk hmeet
  obtain ⟨a₀, ha₀, hal⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    ζ Λz P hb hs hβ1 hLmax hΛ hLΛ he hT i hi k hk hmeet
  refine ⟨a₀, ha₀, fun x hx => ?_⟩
  rw [egpRaw_eq_edgeRaw_KA3_ZERO]
  exact hal x hx

/-- Consumer: EGP03's (ER) for the listed edge charts (`egp03_row`, C14-KC2) and (ER0) under ONE
choice of thresholds on the same family `P : LocalChartPacketsZ`. -/
example {Δ ν E : ℝ} (hΔ : 1 ≤ Δ) (hν : 0 < ν) (hν1 : ν < 1 / 1000000) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ)
        (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T →
        ∀ i ∈ P.edge.centres,
          (∀ j ∈ egpEdgeList P.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * egpRaw P.edge j x - a * egpRaw P.edge i x -
                ρ j / ρ i * egpRaw P.edge j i| < E) ∧
          ∀ k (hk : k ∈ P.zero.centres),
            (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
              ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
            ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (600 * Δ * ρ i),
              |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x| < E := by
  obtain ⟨L₁, η₁, hL₁, hη₁, hER⟩ := egp03_row hΔ hν hν1 hE
  obtain ⟨L₂, η₂, hL₂, hη₂, hER0⟩ := egp03_zero_supplier_egpRaw_ZERO hΔ hν hν1 hE
  refine ⟨max L₁ L₂, min η₁ η₂, lt_max_of_lt_left hL₁, lt_min hη₁ hη₂, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P
    hb hs hβ1 hLc hΛ hLΛ hμ hτ he hT i hi
  let Q := P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets.toLocalChartFamilyE
  refine ⟨(hER X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ Q
    (hb.trans (min_le_left _ _)) hs (hβ1.trans (min_le_left _ _)) ((le_max_left _ _).trans hLc)
    hΛ hLΛ hμ hτ i hi).1, ?_⟩
  exact hER0 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P
    (hb.trans (min_le_right _ _)) hs (hβ1.trans (min_le_right _ _))
    ((le_max_right _ _).trans hLc) hΛ hLΛ he hT i hi

end DifferentialGeometry.Geometry.Collapse
