import DifferentialGeometry.Geometry.Fibration.ActualGlobalDerivative

/-!
# Consumers of CGP02 on the final LC87 family

* `cgp02_row_unit`: on unit tangent vectors (`g_x(v, v) = 1`) the derivative of the actual `𝓔⁰` is
  at most `L₀ = 1000 (N + 2) P₀²`.
* `cgp02_row_full`: CGP01 and CGP02 together on `LocalChartPackets`: `𝓔⁰` is smooth and
  `‖d𝓔⁰(v)‖ ≤ L₀ √(g_x(v, v))` at every point.
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

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNA_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNA_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCA_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- CGP02 on unit tangent vectors: `‖d𝓔⁰(v)‖ ≤ 1000 (N + 2) P₀²` when `g_x(v, v) = 1`. -/
theorem cgp02_row_unit
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1) (x : X)
    (v : TangentSpace 𝓘(ℝ, E3) x) (hv : g.inner x v v = 1) :
    ‖mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x v‖ ≤
      1000 * (fc07ActiveBound + 2) * cgpProfileBound ^ 2 := by
  have h := cgp02_row P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσc hγc hεr x v
  rwa [hv, Real.sqrt_one, mul_one] at h

/-- **CGP01 + CGP02 on `LocalChartPackets`**: the actual original global map is smooth and its
derivative is bounded by `L₀ √(g_x(v, v))`, `L₀ = 1000 (N + 2) P₀²` numerical. -/
theorem cgp02_row_full
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        (cgpGlobalMap P.toLocalChartFamily P.zero) ∧
      1 ≤ cgpProfileBound ∧
      ∀ x (v : TangentSpace 𝓘(ℝ, E3) x),
        ‖mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x v‖ ≤
          1000 * (fc07ActiveBound + 2) * cgpProfileBound ^ 2 * Real.sqrt (g.inner x v v) := by
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  exact ⟨cgp01_rowE P.toLocalChartFamilyE P.zero hΛ hΔ0 hμ hτ hΔΛ (by linarith),
    cgpProfileBound_spec.1,
    fun x v => cgp02_row P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσc hγc hεr x v⟩

end DifferentialGeometry.Geometry.Collapse
