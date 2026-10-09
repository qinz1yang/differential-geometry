import DifferentialGeometry.Geometry.Fibration.ActualEdgeHeightFactors
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumer: the weak-edge vector of `𝓔⁰` under (EZ), on `LocalChartPacketsC14`

* `edp02_weakEdge_vector_C14`: on the family of `LocalChartPacketsC14`, at an edge index `i` and
  a point `p` of its chart ball with `|η_i(p)| < 8Δ`, `ζ_i(p) > 1 − d` (`0 ≤ d`, `2P₀d < 1`) and
  `t(p) ≥ .3Δ`: the `E'` vector of `𝓔⁰` has norm `ρ t g(t/Δ) Z₀` and
  `(1 − (1 + 2P₀)d) ρ t ≤ ‖(𝓔⁰ p)_{E'}‖ ≤ ρ t` (EDP02's "the original weak-edge vector is
  `ρ t g(t/Δ) Z₀`" with (EZ)). Consumes `edp02_ez_GAFS` and `norm_cgpGlobalMap_edgeCoord`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14EH_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14EH_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14EH_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EDP02's weak-edge vector under (EZ)** (`LocalChartPacketsC14`): for `|η_i(p)| < 8Δ` on the
chart ball, `ζ_i(p) > 1 − d` (`0 ≤ d`, `2P₀d < 1`) and `t(p) ≥ .3Δ`, the `E'` vector of `𝓔⁰ p` has
norm `ρ t g(t/Δ) Z₀`, between `(1 − (1 + 2P₀)d) ρ t` and `ρ t`. -/
theorem edp02_weakEdge_vector_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΔ : 0 < Δ) (i : P.edge.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball i.1 (100 * Δ * ρ i.1)) (hη : |P.edge.coord i.1 p| < 8 * Δ) {d : ℝ}
    (hd : 0 ≤ d) (hdP : 2 * cgpProfileBound * d < 1) (hζ : 1 - d < P.edge.cutoff i.1 p)
    (ht : 3 / 10 * Δ ≤ cgpHeight P.toLocalChartFamily p) :
    ‖(cgpGlobalMap P.toLocalChartFamily P.zero p (cgpEdgeTag P.toLocalChartFamily P.zero)).fst‖ =
        ρ p * cgpHeight P.toLocalChartFamily p *
          ((1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight P.toLocalChartFamily p / Δ)) *
            cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum P.toLocalChartFamily p)) ∧
      (1 - (1 + 2 * cgpProfileBound) * d) * (ρ p * cgpHeight P.toLocalChartFamily p) ≤
        ‖(cgpGlobalMap P.toLocalChartFamily P.zero p
          (cgpEdgeTag P.toLocalChartFamily P.zero)).fst‖ ∧
      ‖(cgpGlobalMap P.toLocalChartFamily P.zero p (cgpEdgeTag P.toLocalChartFamily P.zero)).fst‖ ≤
        ρ p * cgpHeight P.toLocalChartFamily p := by
  obtain ⟨-, -, hEZ, hmk⟩ := edp02_ez_GAFS P.toLocalChartFamily hΔ i hp hη hd hdP hζ
  have hnorm := norm_cgpGlobalMap_edgeCoord P.toLocalChartFamily P.zero p
  rw [hmk ht] at hnorm
  have hρt : 0 ≤ ρ p * cgpHeight P.toLocalChartFamily p :=
    mul_nonneg (hρ p).le (cgpHeight_nonneg P.toLocalChartFamily p)
  have hz := cgpEdgeMarker_mem_Icc P.toLocalChartFamily p
  rw [hmk ht] at hz
  refine ⟨hnorm, ?_, ?_⟩
  · rw [hnorm]
    calc (1 - (1 + 2 * cgpProfileBound) * d) * (ρ p * cgpHeight P.toLocalChartFamily p)
        ≤ ((1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight P.toLocalChartFamily p / Δ)) *
            cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum P.toLocalChartFamily p)) *
            (ρ p * cgpHeight P.toLocalChartFamily p) :=
          mul_le_mul_of_nonneg_right hEZ.le hρt
      _ = _ := by ring
  · rw [hnorm]
    calc ρ p * cgpHeight P.toLocalChartFamily p *
          ((1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight P.toLocalChartFamily p / Δ)) *
            cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum P.toLocalChartFamily p))
        ≤ ρ p * cgpHeight P.toLocalChartFamily p * 1 := mul_le_mul_of_nonneg_left hz.2 hρt
      _ = _ := by ring

end DifferentialGeometry.Geometry.Collapse
