import DifferentialGeometry.Geometry.Fibration.ActualZeroBlockIsolation
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): ActualZeroBlockIsolation (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualZeroBlockIsolation.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
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
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNZ_GAF_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNZ_GAF_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCZ_GAF_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **LPA05 on the zero supports**: at a point of the closed support of LC31's annular cutoff of the
zero ball at `c`, `ρ(p) ≤ 20 R_c / T`. -/
theorem zero_cutoff_ratio_GAF_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr) {c : X} (hc : c ∈ P.zero.centres) {p : X}
    (hp : p ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero c hc).radial y))) :
    ρ p ≤ 20 * (P.zero.zero c hc).radius / T := by
  have hball := zero_tsupport_subset_ball_KA2 (P.zero.zero c hc) hεr he hp
  rw [P.zero.zero_center c hc, mem_ball] at hball
  have hr := (P.zero.zero c hc).radius_pos
  have hcp : dist c p ≤ 10 * (P.zero.zero c hc).radius := by
    rw [dist_comm]
    linarith
  have hratio := P.zero_local_comparison c hc p hcp
  have hρp := hρ p
  rw [le_div_iff₀ hρp] at hratio
  rw [le_div_iff₀ hT]
  linarith

/-- **ZSP01 (ZI), original half**: if `20 R_c/T < ρ(p)` the WHOLE zero block of `𝓔⁰(p)` at the zero
ball of `c` is zero. -/
theorem zsp01_original_zero_block_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr) (i : P.zero.finite_centres.toFinset)
    {p : X} (hρp : 20 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p) :
    cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero p (.inr (.inr (.inr (.inl i)))) = 0 := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hcut :
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p) = 0 := by
    by_contra h
    have hmem : p ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero i.1 hi).radial y)) := subset_tsupport _ h
    have := zero_cutoff_ratio_GAF_BAUGP P hT he hεr hi hmem
    linarith
  change WithLp.toLp 2 ((cgpRadius_BAUGP P.toLocalPacketsOnB P.zero (.inr (.inr (.inr (.inl i)))) p
      *
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p)) •
      cgpCoord_BAUGP P.toLocalPacketsOnB P.zero (.inr (.inr (.inr (.inl i)))) p,
    cgpRadius_BAUGP P.toLocalPacketsOnB P.zero (.inr (.inr (.inr (.inl i)))) p *
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p)) = 0
  rw [hcut, mul_zero, zero_smul]
  rfl


end DifferentialGeometry.Geometry.Collapse
