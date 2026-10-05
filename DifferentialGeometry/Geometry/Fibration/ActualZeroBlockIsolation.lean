import DifferentialGeometry.Geometry.Fibration.ActualFirstComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsResidualApplications

/-!
# ZSP01, original half: the zero blocks of the actual `𝓔⁰` are isolated

Blueprint `master207B.tex`, ZSP01 (`lem:fibration-actual-zero-block-isolation`, B:6323–6372), first
step of the proof: "A positive original `i` cutoff places `p` in the selected zero ball's closed
ten-radius neighborhood, by its annular support and the radial value estimate. LPA05 then gives
`ρ(p) ≤ 20R_i/T₀`. Thus the original block vanishes in (ZI)." On `LocalChartPacketsR` (LC87 with
LC62's local comparison `zero_local_comparison`, the LPA05 ratio `T/20 ≤ r_c/ρ(q)` on
`d(c, q) ≤ 10 r_c`):

* `zero_cutoff_ratio_GAF`: at a point of the closed support of the zero cutoff of the zero ball at
  `c`, `ρ(p) ≤ 20 R_c / T`;
* `zsp01_original_zero_block`: if `20 R_c/T < ρ(p)`, the WHOLE zero block of `𝓔⁰(p)` vanishes; in
  particular for (ZI)'s range `200 R_c/T < ρ(p)` (consumer `zsp01_original_zero_block_ZI`).
The stage half of (ZI) and (ZE) consume GAF02's stage maps and are not part of this module.
Parameter ranges: `0 < T`, `e < 1/10`, `0 ≤ 1 + εr`.
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
local instance instMetricNZ_GAF
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNZ_GAF
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCZ_GAF
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **LPA05 on the zero supports**: at a point of the closed support of LC31's annular cutoff of the
zero ball at `c`, `ρ(p) ≤ 20 R_c / T`. -/
theorem zero_cutoff_ratio_GAF
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
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
theorem zsp01_original_zero_block
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr) (i : P.zero.finite_centres.toFinset)
    {p : X} (hρp : 20 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p) :
    cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i)))) = 0 := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hcut :
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p) = 0 := by
    by_contra h
    have hmem : p ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero i.1 hi).radial y)) := subset_tsupport _ h
    have := zero_cutoff_ratio_GAF P hT he hεr hi hmem
    linarith
  change WithLp.toLp 2 ((cgpRadius P.toLocalChartFamily P.zero (.inr (.inr (.inr (.inl i)))) p *
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p)) •
      cgpCoord P.toLocalChartFamily P.zero (.inr (.inr (.inr (.inl i)))) p,
    cgpRadius P.toLocalChartFamily P.zero (.inr (.inr (.inr (.inl i)))) p *
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p)) = 0
  rw [hcut, mul_zero, zero_smul]
  rfl

end DifferentialGeometry.Geometry.Collapse
