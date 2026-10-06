import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Row
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRemainderCircleApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRemainderApplications

/-!
# FC38 (the remaining circle bundle): the delivered part of the row, GAF07 circle ∧ FDC03

Lane S-FC-WRAP, group G2 (suffix `_FCW`). Blueprint `master207B.tex`, FC38
(`found:fibration-circle-bundles`, B:6287–6309): truncate `W₁` by marker `> .9R_i` and ratio `< 4`
with FULL preimages under `E`; KL 14.13 gives the proper circle bundle on `U'₁` (contains the local
`3.5` regions, lies in `U₁`) [GAF07, circle part]; the complement of the interiors of the zero,
slim and edge pieces lies in `U'₁`, is saturated for this bundle and is a compact manifold with
corners of depth at most two [FDC03]; the induced circle fibration on the vertical boundary of an
edge disk bundle agrees with the one on `M^{2-stratum}` [EDP06].

`Gaf02ChainEJA.fc38_row_FCW` (final family `LocalChartPacketsC14Z`, chain with (JA)) is the
conjunction of everything of FC38 that is delivered in the tree:

1. `type_of% (C.gaf07_circle_row_GAFD hβ hd)` — GAF07's circle row: `B₁` relatively open in `W₁`,
   `{‖η_i‖ ≤ 3.5} ⊂ X₁ ⊂ U₁`, `π₁E : X₁ → B₁` proper, onto, submersion in the base chart, every
   WHOLE fibre the whole adjusted level, `≃ₜ` the original fibre, connected, a smooth circle, with
   its whole trace in `{‖η_i‖ < 4.01}`; whole stage fibre = whole final fibre;
2. `type_of% (fdc03_remainder_subset_X₁_C14Z_EFC C …)` — FDC03's first clause: for ZSP04's `K₃` and
   the actual `Z`, `M₁`, `M₂`, edge piece `A` and `M₃ = M₂ ∖ int_{M₂} A`: `M₃ ⊆ X₁`;
3. `type_of% (fdc03_remainder_C14Z_FDC C.toGaf02ChainE hσc)` — FDC03's coverage and the saturation
   input: `X₂°` open, the complement of `X₂°` lies in the zero stratum, a selected circle ball or a
   selected slim ball, and `X₂°`-membership is constant on the fibres of `E`.

NOT in the tree (so not in the row; owners in the delivery block): the circle bundle's local
trivializations (`gaf07_circle_trivial_circle_EFE`, lane S-EDP-FDC's undelivered G6 file), the
saturation of `M₃` and `M₃ = E⁻¹(C₁) ∩ X₁`, the corner structure of `C₁` (depth `≤ 2`) and
(LastFaces), EDP06 (B), (C): the vertical circles are WHOLE fibres of `E : X₁ → B₁`, saturation of
`M₂ ∩ X₁`, the base coordinates `(g_i, T)`.

Consumer: `fc38_remainder_fibres_FCW`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **FC38, the delivered part of the row on the final family**: GAF07's circle row ∧ FDC03's
`M₃ ⊆ X₁` for the actual pieces ∧ FDC03's coverage / fibre-constancy of the edge candidate. -/
theorem fc38_row_FCW
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    type_of% (C.gaf07_circle_row_GAFD hβ hd) ∧
    type_of% (fdc03_remainder_subset_X₁_C14Z_EFC C hεr hσc hγ hγ1) ∧
    type_of% (fdc03_remainder_C14Z_FDC C.toGaf02ChainE hσc) :=
  ⟨C.gaf07_circle_row_GAFD hβ hd, fdc03_remainder_subset_X₁_C14Z_EFC C hεr hσc hγ hγ1,
    fdc03_remainder_C14Z_FDC C.toGaf02ChainE hσc⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
