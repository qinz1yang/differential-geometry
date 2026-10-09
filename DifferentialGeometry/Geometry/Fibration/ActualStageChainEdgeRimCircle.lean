import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeInterior
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCircleCover

/-!
# EDP06, first step: a point of the vertical boundary of the actual `X₂` lies in a rim box

Blueprint `master207B.tex`, EDP06 (B:7102–7108: "At a point of (EV), (ELoc) and (EH) give
`|η_i| < 4.01Δ` and `|t - 4Δ| < h_*` for a witnessing edge index. LFR38 applies to the SAME original
pair on this full band and makes the point two-stratum ... LPA06's original circle cover supplies a
circle chart with `|η_a| < 2`. GAF07 therefore puts the point in `X₁`"). Chain-level part:

* `Gaf02ChainE.rim_localization_EFC`: a point of the ACTUAL `X₂ = (π₂E)⁻¹(B₂) ∩ V`
  (`W₂ = C.finalBase_BAS 1`) with `T = 4Δ` has a witnessing edge index `k` with `p ∈ U_k`,
  `|η_k(p)| < 5Δ`, `t(p) < 5Δ` and `|g_k(p)| < 4Δ` (the hypotheses of EDP-E's rim lemmas):
  (ELoc) (`ratio_localization_FDC`) and GAF05's exact marker (`gaf05_edge_plateau_G47`);
* `Gaf02ChainEJA.rim_mem_X₁_of_circle_ball_EFC`: such a point in a circle covering ball
  `B(a, 2ρ_a)` lies in GAF07's `X₁ = (π₁E)⁻¹(W₁ ∩ R₁)` (lane C14-FDCb's `circle_ball_mem_X₁_FDC`).

The tail step (LFR38 + LPA06: the rim point is two-stratum and in a circle covering ball) is lane
C14-EDP-E's `eventually_edp06_final_rim_circle_EDPE`; the composition is in the Applications file.
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
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainE

/-- **Rim localization for the actual `X₂`** (`Δ ≥ 2`): a point of `X₂` with `T = 4Δ` has a
witnessing edge index `k` with `p ∈ U_k`, `|η_k(p)| < 5Δ`, `t(p) < 5Δ` and `|g_k(p)| < 4Δ`. -/
theorem rim_localization_EFC
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ) {p : X}
    (hp : p ∈ {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
        Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : L.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      ({x | L.edge.smoothing x / ρ x ≤ 7 / 20 * Δ} ∪ {x | 0 < Ĉ.toChain.scale x ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ}))
    (hT4 : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
      (Ĉ.toChain.E p)) / Ĉ.toChain.scale p = 4 * Δ) :
    ∃ k : L.toLocalChartFamily.edge.finite_centres.toFinset,
      p ∈ ball k.1 (100 * Δ * ρ k.1) ∧ |L.edge.coord k.1 p| < 5 * Δ ∧
        L.edge.smoothing p / ρ p < 5 * Δ ∧
        |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
          (Ĉ.toChain.E p)) / ρ k.1| < 4 * Δ := by
  obtain ⟨-, k, hv, hu⟩ := Ĉ.edgeBase_ratio_EFC hp
  have hV : p ∈ {x | L.edge.smoothing x / ρ x ≤ 7 / 20 * Δ} ∪ {x | 0 < Ĉ.toChain.scale x ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ} :=
    Or.inr ⟨(Ĉ.toChain.scale_pos p).2, le_of_eq hT4⟩
  obtain ⟨hball, hη, ht, -⟩ := Ĉ.toChain.ratio_localization_FDC hΔ k hv hu hV
  have hmk : blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) (Ĉ.toChain.E p) = ρ k.1 :=
    Ĉ.gaf05_edge_plateau_G47 k hball (by linarith)
      (by change L.edge.smoothing p / ρ p < 6 * Δ; linarith)
  have hrk := hρ k.1
  refine ⟨k, hball, by linarith, by linarith, ?_⟩
  rw [abs_div, abs_of_pos hrk, div_lt_iff₀ hrk]
  have h1 := abs_proj_zero_le_norm_EFC (blockVectorCLM (V := fun _ : CGPTag
    L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E p))
  rw [hmk] at hu
  exact lt_of_le_of_lt h1 hu

end Gaf02ChainE

namespace Gaf02ChainEJA

/-- **A rim point in a circle covering ball lies in `X₁`** (`0 ≤ γ ≤ 3/4`). -/
theorem rim_mem_X₁_of_circle_ball_EFC {cadj : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4)
    {p a : X} (ha : a ∈ P.circle.centres) (hpa : dist p a < 2 * ρ a) :
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
      C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets :=
  C.circle_ball_mem_X₁_FDC hγ hγ1 ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩ (mem_ball.mpr hpa)

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
