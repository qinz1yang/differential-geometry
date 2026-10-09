import DifferentialGeometry.Geometry.Fibration.ActualStageChainPiecesFD4
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgePiecesFD4
import DifferentialGeometry.Geometry.Fibration.ActualStageChainHorizontalDisksFD4

/-!
# FDC04: the row candidate on the actual chain (G3, chain form)

Lane S-FDC04 (`_FD4`), group G3. Blueprint `master207B.tex`, FDC04
(`thm:fibration-actual-closed-decomposition`, B:7367-7435). On the final family
`LocalChartPacketsC14Z`, for a chain `C : Gaf02ChainEJA ...` with (JA), the smooth stage bases `A`,
ANY admissible `K₃, D₃` (the five properties of `zsp04_D3_ZSP35`) and `hcpt` (FDC02's compactness
of `M^edge`; the tail form `eventually_fdc04_row_C14Z_FD4` of the next file discharges it),
`Gaf02ChainEJA.fdc04_row_FD4` is the conjunction of

1. the zero pieces (`zero_pieces_FD4`: finite list, compact, ZSP02 strong row, `Z` compact);
2. the slim pieces (`slim_pieces_FD4`: ZSP04's full row on this `K₃, D₃`, finite list of arcs and
   loops, compact pieces, `S² × I` / `T² × I` products, circle submersions over the loops);
3. the four-piece cover (`fdc04_cover_FD4`: `M^edge`, `M₃` compact, `M₂ = M^edge ∪ M₃`, cover,
   pairwise disjoint ambient interiors);
4. the edge pieces (`edge_pieces_FD4`: finite compact components of `C₂`, compact pieces of
   `M^edge`);
5. the whole FDC02 / EDP05 row (`edgeRow_EFE`, already delivered: smooth base domain, components,
   `EdgeBundle` data, faces (EF));
6. the horizontal disks (`edge_horizontal_disks_FD4`: whole smooth disks in `∂M₂`, disjoint or
   equal, in one component of `∂M₂`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology
open GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

section Row

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **FDC04, the row candidate on the actual chain** (see the module docstring). -/
theorem fdc04_row_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hK : 5 ≤ K)
    (hcpt : IsCompact (C.edgeA_FD4 K₃ Δ)) :
    type_of% (C.toGaf02ChainE.zero_pieces_FD4 hεr) ∧
    type_of% (C.slim_pieces_FD4 hεr hK K₃ D₃ hD hKs hKF hDreg hdD) ∧
    type_of% (C.fdc04_cover_FD4 hεr K₃ D₃ hD hKs hKF hDreg hcpt) ∧
    type_of% (C.edge_pieces_FD4 A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt) ∧
    type_of% (C.edgeRow_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt) ∧
    type_of% (C.edge_horizontal_disks_FD4 A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃
      hD hKs hKF hDreg hdD hcpt) :=
  ⟨C.toGaf02ChainE.zero_pieces_FD4 hεr, C.slim_pieces_FD4 hεr hK K₃ D₃ hD hKs hKF hDreg hdD,
    C.fdc04_cover_FD4 hεr K₃ D₃ hD hKs hKF hDreg hcpt,
    C.edge_pieces_FD4 A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg
      hdD hcpt,
    C.edgeRow_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD
      hcpt,
    C.edge_horizontal_disks_FD4 A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs
      hKF hDreg hdD hcpt⟩

end Row

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
