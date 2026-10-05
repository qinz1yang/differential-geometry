import DifferentialGeometry.Geometry.Fibration.ActualSlimSlabs
import DifferentialGeometry.Geometry.Fibration.ActualCloudPackets
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumer: ZSP04's union of original `3.5·10⁵Δ` slim slabs on `LocalChartPacketsC14`

* `zsp04_slabs_C14`: on the family of `LocalChartPacketsC14` (`0 < Δ`), the union over all slim
  centres of the closed slabs `{|η_i| ≤ 3.5·10⁵Δ}` is compact and lies in FC27's slim core set
  `fc27SlimSet L 7` (the domain of the stage-three cloud). Consumes
  `isCompact_iUnion_slimSlab_GAFS`.
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
local instance instMetricNC14SS_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14SS_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14SS_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **ZSP04's original slabs** (`LocalChartPacketsC14`, `0 < Δ`): the union of the closed slabs
`{|η_i| ≤ 3.5·10⁵Δ}` over all slim centres is compact and contained in `fc27SlimSet L 7`. -/
theorem zsp04_slabs_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΔ : 0 < Δ) :
    IsCompact (⋃ i : P.slim.finite_centres.toFinset,
      {p | p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
          35 / 10 * 10 ^ 5 * Δ}) ∧
    (⋃ i : P.slim.finite_centres.toFinset,
      {p | p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
          35 / 10 * 10 ^ 5 * Δ})
      ⊆ fc27SlimSet P.toLocalChartFamily 7 := by
  refine ⟨isCompact_iUnion_slimSlab_GAFS P.toLocalChartFamily hΔ (by nlinarith), ?_⟩
  intro p hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  exact ⟨i, hi.1, hi.2.trans (by nlinarith)⟩

end DifferentialGeometry.Geometry.Collapse
