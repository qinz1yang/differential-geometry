import DifferentialGeometry.Geometry.Fibration.ActualRetainedMarkerCloud

/-!
# Consumers of FC26/CFS07 on the actual `𝓔⁰`

* `cfs07_off_zero_stratum`: on `LocalChartPackets` (FC07's parameter ranges, `0 ≤ σ_s ≤ 1/100`), any
  two points outside the zero stratum whose images under `𝓔⁰` are within `L'·max(Σρ)` (`L'Σ ≤ 1/5`)
  have scales in ratio `[3/5, 5/3]`.
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
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNM_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNM_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCM_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- CFS07 off the zero stratum, on `LocalChartPackets`. -/
theorem cfs07_off_zero_stratum
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) {L' sg : ℝ} (hL' : 0 ≤ L') (hsg : 0 ≤ sg) (hLsg : L' * sg ≤ 1 / 5)
    {p q : X} (hp : p ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0)
    (hq : q ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0)
    (hd : dist (cgpGlobalMap P.toLocalChartFamily P.zero p)
      (cgpGlobalMap P.toLocalChartFamily P.zero q) ≤ L' * max (sg * ρ p) (sg * ρ q)) :
    (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  exact (cfs07_row P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ hsmall hL' hsg hLsg).1 p
    (exhaustion_cgpRetainedCloud P.toLocalChartFamily hΔ0 hp) q
    (exhaustion_cgpRetainedCloud P.toLocalChartFamily hΔ0 hq) hd

end DifferentialGeometry.Geometry.Collapse
