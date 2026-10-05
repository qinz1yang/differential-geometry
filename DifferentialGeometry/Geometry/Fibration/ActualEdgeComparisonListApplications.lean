import DifferentialGeometry.Geometry.Fibration.ActualEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPackets

/-!
# Consumers of EGP02

* `egp02_edge_cutoff_eq_zero_of_unlisted`: on `D_i` every unlisted actual edge cutoff vanishes, so
  `Σ_{I_e} ζ_j = Σ_{J_e} ζ_j` there.
* On LC87's final `LocalChartPackets P` (projections `P.toLocalChartFamilyE`, `P.zero`, the inputs of
  `cgpGlobalMap P.toLocalChartFamily P.zero`): `egp02_list_count_P` (the numerical list bound) and
  `egp02_zero_cutoff_unique_P` (at a point of `D_i` at most one zero cutoff is nonzero).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section General

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}

/-- On `D_i` every actual edge cutoff outside EGP02's list `J_e` vanishes. -/
theorem egp02_edge_cutoff_eq_zero_of_unlisted
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) {i j x : X}
    (hj : j ∈ L.edge.centres) (hjl : j ∉ egpEdgeList L i) (hx : x ∈ ball i (20 * Δ * ρ i)) :
    L.edge.cutoff j x = 0 := by
  by_contra hne
  exact hjl ⟨hj, x, subset_tsupport _ hne, hx⟩

end General

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNP_C14KA
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNP_C14KA
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCP_C14KA
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- EGP02's numerical list bound on LC87's final family. -/
theorem egp02_list_count_P
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : X) :
    ((egpEdgeList P.toLocalChartFamily i).ncard : ℝ) +
        (egpSlimList P.toLocalChartFamily i).ncard ≤ egp02ListBound :=
  egp02_list_count P.toLocalChartFamily hΛ hΔ hLΛ i

/-- On LC87's final family, at a point of `D_i` at most one zero cutoff `Φ ∘ radial` of `P.zero`
(the zero blocks of `cgpGlobalMap P.toLocalChartFamily P.zero`) is nonzero. -/
theorem egp02_zero_cutoff_unique_P
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T)
    {i : X} (hi : i ∈ P.edge.centres) {x : X} (hx : x ∈ ball i (20 * Δ * ρ i))
    {k₁ : X} (hk₁ : k₁ ∈ P.zero.centres) {k₂ : X} (hk₂ : k₂ ∈ P.zero.centres)
    (h₁ : Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero k₁ hk₁).radial x) ≠ 0)
    (h₂ : Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero k₂ hk₂).radial x) ≠ 0) :
    k₁ = k₂ := by
  have h := (egp02_row P.toLocalChartFamilyE P.zero hΛ hΔ hμ hτ hLΛ he hT hi).2.2.2.2.2.1
  exact h k₁ hk₁ k₂ hk₂ ⟨x, subset_tsupport _ h₁, hx⟩ ⟨x, subset_tsupport _ h₂, hx⟩

end Packets

end DifferentialGeometry.Geometry.Collapse
