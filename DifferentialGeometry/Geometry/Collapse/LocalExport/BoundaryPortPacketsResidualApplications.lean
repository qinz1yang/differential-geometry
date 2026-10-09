import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): LocalChartPacketsResidualApplications (circle-stage closure)

GENERATED from
`DifferentialGeometry/Geometry/Collapse/LocalExport/LocalChartPacketsResidualApplications.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

namespace LocalPacketsOnBF

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of the zero kind, as a local instance. -/
local instance instMetricN_CH13CLOSE2_BAUGP
    (L : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (L.N a) :=
  L.instMetricN a

/-- The model charts of the zero kind, as a local instance. -/
local instance instChartedN_CH13CLOSE2_BAUGP
    (L : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (L.N a) :=
  L.instChartedN a

/-- The cone metrics of the zero kind, as a local instance. -/
local instance instMetricC_CH13CLOSE2_BAUGP
    (L : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (L.C a) :=
  L.instMetricC a

/-- **TCP01, circle clause.** At every circle centre `j`, every point `x` of the chart domain
`B(j, 200ρ(j))` with `|η_j(x)| ≤ 8` lies in `D_j = B(j, 10ρ(j))`. -/
theorem dist_lt_of_norm_coord_le_BAUGP
    (L : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    {j : X} (hj : j ∈ L.circle.centres) {x : X} (hx : dist x j < 200 * ρ j)
    (h8 : let c := L.circle.chart j hj
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      ‖c.coord x‖ ≤ 8) :
    dist x j < 10 * ρ j := by
  have hres := L.circle_residual j hj
  have hx' : (ρ j)⁻¹ * dist x j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have h10 : (ρ j)⁻¹ * dist x j < 10 := hres x hx' h8
  have h := (inv_mul_lt_iff₀ (hρ j)).mp h10
  linarith

/-- **TCP01, zero clause.** If the zero-model ball `B(c, r_c)` meets `B(p, 10ρ(p))`, `T ≥ 20` and
`Λ ≤ 1/20`, then `T/20 ≤ r_c/ρ(p)` (LC62's local comparison at `p`, which the meeting point puts in
the closed ball `d(c, p) ≤ 10 r_c`). -/
theorem zero_ratio_of_meets_BAUGP
    (L : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (hT : 20 ≤ T) (hΛ : Λ ≤ 1 / 20) {c : X} (hc : c ∈ L.zero.centres) {p : X}
    (hmeet : (ball c (L.zero.zero c hc).radius ∩ ball p (10 * ρ p)).Nonempty) :
    T / 20 ≤ (L.zero.zero c hc).radius / ρ p := by
  obtain ⟨x, hxc, hxp⟩ := hmeet
  have hxc' : dist x c < (L.zero.zero c hc).radius := hxc
  have hxp' : dist x p < 10 * ρ p := hxp
  set r := (L.zero.zero c hc).radius with hr
  have hrpos : 0 < r := (L.zero.zero c hc).radius_pos
  have hTρ : T * ρ c ≤ r := (L.zero.radius_mem c hc).1
  have hρc : ρ c ≤ r / 20 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hρ c]
  have hcp : dist c p < r + 10 * ρ p := by
    have := dist_triangle c x p
    rw [dist_comm c x] at this
    linarith
  have hΛ' : ((Real.toNNReal Λ : ℝ≥0) : ℝ) ≤ 1 / 20 := by
    rw [Real.coe_toNNReal']
    exact max_le hΛ (by norm_num)
  have hlip := L.lipschitz_scale.dist_le_mul p c
  rw [Real.dist_eq, dist_comm] at hlip
  have hΛ0 : (0 : ℝ) ≤ ((Real.toNNReal Λ : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hρp : ρ p ≤ ρ c + ((Real.toNNReal Λ : ℝ≥0) : ℝ) * dist c p := by
    have h1 := (abs_le.mp hlip).2
    linarith
  have hmul : ((Real.toNNReal Λ : ℝ≥0) : ℝ) * dist c p ≤ 1 / 20 * (r + 10 * ρ p) :=
    mul_le_mul hΛ' hcp.le dist_nonneg (by norm_num)
  have hρp' : ρ p ≤ r / 5 := by linarith
  have hcp' : dist c p ≤ 10 * r := by linarith
  exact L.zero_local_comparison c hc p hcp'

end LocalPacketsOnBF


end DifferentialGeometry.Geometry.Collapse
