import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoice
import DifferentialGeometry.Geometry.Fibration.ActualGlobalDerivativeApplications

/-!
# Consumers of GAF01 on the actual constants

* `gaf01_cfs31_inputs`: the choice of `gaf01_row` supplies exactly the (MB) hypotheses
  `hc₁0 … ht₃` of CFS31's sequential cutoff assembly `actualCloud_cutoff_sequence` for
  `N = gafMultiplicity`, `P = cgpProfileBound` and the tube radii `σ_j = Σ_j`.
* `gaf01_derivative_bound`: on every `LocalChartPackets` with CGP02's parameter ranges, the actual
  `𝓔⁰` is smooth and `‖d𝓔⁰(v)‖ ≤ L₀ √(g_x(v, v))` for GAF01's `L₀ = gafDerivativeBound`, so CFS20's
  hypothesis `‖D𝓔⁰‖ ≤ L₀` is produced, not assumed.
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

/-- **GAF01 ⇒ CFS31 (MB)**: one choice with `c₃ < c_adjust` meeting CFS31's (MB) hypotheses
verbatim (`c₁ = c 0`, `c₂ = c 1`, `c₃ = c 2`, `t₂ = t 1`, `t₃ = t 2`, `σ 1 = Σ₂`, `σ 2 = Σ₃`). -/
theorem gaf01_cfs31_inputs (K : ℕ) (C : Fin 3 → ℝ) (hC : ∀ j, 0 < C j) {cadj : ℝ}
    (hcadj : 0 < cadj) :
    ∃ (c S : Fin 3 → ℝ) (t₂ t₃ : ℝ), c 2 < cadj ∧ 0 ≤ c 0 ∧ 0 ≤ c 1 ∧ 0 ≤ c 2 ∧
      c 0 ≤ min t₂ (min (4 * (1 / (1000 * ((gafMultiplicity : ℝ) + 1) * cgpProfileBound ^ 2)) / 5)
        (1 / 512)) ∧
      c 1 ≤ min t₃ (min (4 * (1 / (1000 * ((gafMultiplicity : ℝ) + 1) * cgpProfileBound ^ 2)) / 5)
        (1 / 512)) ∧
      c 2 ≤ 1 / 512 ∧ t₂ ≤ 3 * S 1 / 10 ∧ t₃ ≤ 3 * S 2 / 10 := by
  obtain ⟨θ, Ξ, -, hchoice⟩ := gaf01_row K
  obtain ⟨c, Γ, S, e, h⟩ := hchoice C hC cadj hcadj
  obtain ⟨⟨h2a, -, h2c⟩, ⟨-, h1t, h1k, -, h1n⟩, ⟨-, h0t, h0k, -, h0n⟩, hstage⟩ := h
  have hc : ∀ j, 0 < c j := fun j => (hstage j).1.2.1
  refine ⟨c, S, _, _, h2a, (hc 0).le, (hc 1).le, (hc 2).le,
    le_min h0t (le_min h0k h0n), le_min h1t (le_min h1k h1n), h2c.le, min_le_left _ _,
    min_le_left _ _⟩

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF01's `L₀` is produced by CGP02**: on `LocalChartPackets` with CGP02's parameter ranges the
actual `𝓔⁰` is smooth with `‖d𝓔⁰(v)‖ ≤ gafDerivativeBound · √(g_x(v, v))`. -/
theorem gaf01_derivative_bound
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        (cgpGlobalMap P.toLocalChartFamily P.zero) ∧
      ∀ x (v : TangentSpace 𝓘(ℝ, E3) x),
        ‖mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x v‖ ≤
          gafDerivativeBound * Real.sqrt (g.inner x v v) := by
  obtain ⟨hsm, -, hd⟩ := cgp02_row_full P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσc hγc hεr
  exact ⟨hsm, fun x v => hd x v⟩

end DifferentialGeometry.Geometry.Collapse
