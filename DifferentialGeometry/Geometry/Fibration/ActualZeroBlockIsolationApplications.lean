import DifferentialGeometry.Geometry.Fibration.ActualZeroBlockIsolation

/-!
# Consumers of ZSP01's original half

* `zsp01_original_zero_block_ZI`: in (ZI)'s range `200 R_c/T₀ < ρ(p)` the whole zero block of the
  actual `𝓔⁰(p)` is zero (`J_i F(p) = 0`), on `LocalChartPacketsR` with the producer's `T ≥ 200`
  range (`T ≥ 1600·10⁶Δ`).
* `zsp01_original_zero_marker`: the same for the zero marker `(𝓔⁰ p)_i.snd = R_c ζ_c(p)`.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNZA_GAF
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNZA_GAF
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCZA_GAF
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **ZSP01 (ZI) for `F = 𝓔⁰`**: `200 R_c/T < ρ(p)` ⇒ the whole zero block of `𝓔⁰(p)` is zero. -/
theorem zsp01_original_zero_block_ZI
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr) (i : P.zero.finite_centres.toFinset)
    {p : X} (hρp : 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p) :
    cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i)))) = 0 := by
  have hr := (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius_pos
  refine zsp01_original_zero_block P hT he hεr i (lt_of_le_of_lt ?_ hρp)
  rw [div_le_div_iff_of_pos_right hT]
  linarith

/-- The zero marker of `𝓔⁰` vanishes in (ZI)'s range. -/
theorem zsp01_original_zero_marker
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr) (i : P.zero.finite_centres.toFinset)
    {p : X} (hρp : 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p) :
    (cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))))).snd = 0 := by
  rw [zsp01_original_zero_block_ZI P hT he hεr i hρp]
  rfl

end DifferentialGeometry.Geometry.Collapse
