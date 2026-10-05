import DifferentialGeometry.Geometry.Fibration.ActualSlimComparisonList
import DifferentialGeometry.Geometry.Fibration.ActualActiveSupportPacket

/-!
# Consumers of SGP01: the whole active list at `D_i` and the plateau inside `D_i`

* `sgp01_active_count_ZERO`: the slim list `J_i` and the zero supports meeting
  `D_i = B(i, .95Lρ(i))` number at most `N_* + 1` (SGP01's count and its zero uniqueness, via
  `ncard_zeroMeetingList_le_one`).
* the row's verbatim plateau clause "every point of `{|η_i| ≤ 8ℓ}` lies strictly inside `D_i`"
  (example).
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
local instance instMetricNSA_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNSA_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCSA_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The whole active list at SGP01's `D_i`**: at most `N_* + 1` supports (the slim list `J_i`
and at most one zero support) meet `D_i = B(i, .95Lρ(i))`. -/
theorem sgp01_active_count_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (i : X) :
    ((sgpSlimList P.slim i).ncard : ℝ) +
        (zeroMeetingList P.zero i (95 / 100 * (1000000 * Δ))).ncard ≤ egp02SlimCount + 1 := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hT0, hℓ, hsmall⟩ := sgp01_zero_smallness_ZERO hΔ hLΛ hT
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hsmall' : 2 * (95 / 100 * (1000000 * Δ) / T) +
      2 * (95 / 100 * (1000000 * Δ) * ((Real.toNNReal Λ : NNReal) : ℝ)) ≤ 1 / 40 := by
    rwa [hc]
  have hz := ncard_zeroMeetingList_le_one P.zero P.lipschitz_scale he hT0 i hℓ hsmall'
  have hz' : ((zeroMeetingList P.zero i (95 / 100 * (1000000 * Δ))).ncard : ℝ) ≤ 1 := by
    exact_mod_cast hz
  have hS := sgpSlimList_ncard_le_ZERO P.toLocalChartFamily hΔ0 hΛ hLΛ i
  linarith

/-- SGP01's plateau clause in the row's verbatim form: every point of the original set
`{|η_i| ≤ 8ℓ}` (in the coordinate domain) lies strictly inside `D_i`. -/
example
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) {i : X}
    (hi : i ∈ P.slim.centres) :
    ∀ q ∈ ball i (10 ^ 6 * Δ * ρ i), |(P.slim.centre i hi).coord q| ≤ 8 * (100000 * Δ) →
      q ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i) := by
  intro q hq hη
  have h := (sgp01_row P hΛ hΔ hLΛ he hT hσs hσs1 hi).2.2.2.2.2 q hq hη
  refine ball_subset_ball ?_ h
  have := hρ i
  nlinarith

end DifferentialGeometry.Geometry.Collapse
