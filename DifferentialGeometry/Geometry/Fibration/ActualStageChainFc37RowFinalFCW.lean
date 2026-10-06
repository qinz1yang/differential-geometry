import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc37RowEdp05FCW
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCornersEFE

/-!
# FC37 (proper edge disk bundles with faces): the final row

Lane S-FC-WRAP3, group G10 (suffix `_FCW`). Blueprint `master207B.tex`, FC37
(`found:fibration-edge-bundles`, B:6260–6285) = EDP04 (B:6949–7038) ∧ EDP05 (B:7040–7090) ∧
FDC02 (B:7246–7283). On the final family `LocalChartPacketsC14Z`, for a chain `C` with (JA), the
smooth stage bases `A`, ZSP04's `K₃, D₃` and FDC02's compactness `hcpt` of `M^edge`,
`Gaf02ChainEJA.fc37_row_final_FCW` is the conjunction of

1. `fc37_row_edp05_FCW` (group G7): the EDP02 / EDP04 row (`fc37_row_edp02_FCW`), E1
   (`edgeCompactDomain_EFE`: compact `C₂`, saturation, smooth defining functions at every
   frontier point) and the finite arc / circle components of `C₂` (`fc37_components_FCW`);
2. `edp05_row_EFE` (S-EDP-FDC4 G11): the whole EDP05 row — the `EdgeBundle` data with rank two,
   the faces (EF) `H` and `V_e`, `M^edge ∩ ∂M₂ = ⋃ disks`, every horizontal disk in ONE zero or
   slim face, and the face package with corner independence at every endpoint of `C₂`;
3. `edgeRow_EFE` (S-EDP-FDC4 G9): the whole FDC02 row on the actual objects;
4. `edge_rank_two_EFE` (EDP04's final-time rank two of `(f₂, T)` at `T = 4Δ`) and
   `edge_corner_independence_EFE` (independence of `d(φ ∘ f₂)` and `dT` at `T = 4Δ` for every
   `φ` with `dφ ≠ 0`), both stated for every point of the edge source.

READING (review 77, R13 / D77-3): the EDP02 clause of conjunct 1 is the FULL-NORM theorem
(`|u_i|` is the norm `‖u_i‖` of the `ℝ²`-valued vector block, the convention of every accepted
EDP-E / EFC / EFE / FDC theorem; `B₂^full ⊆ B₂^axis`). This row makes NO claim about the
axis-coordinate reading of EDP02; its faithfulness is a separate open item, and no clause here
(exact domains, covers, cutoff boundaries, fibre identification) is asserted for the axis reading.

No hypothesis is left undischarged: `hcpt` is FDC02's compactness, supplied by the tail form
(`eventually_fc37_row_final_C14Z_FCW`); the numerics are the register's; the labelled
`S¹ × D²` / `I × D²` product models (`EdgeComponentModels`) are the separate draft-74 exit
(S-EDGE-INT2), not a conjunct.
-/


set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology

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

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **FC37, the final row on the final family** (see the module docstring; full-norm reading of
EDP02, no axis-coordinate claim). -/
theorem fc37_row_final_FCW
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain) (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
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
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    type_of% (C.fc37_row_edp05_FCW A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
      hKs hKF hDreg hdD hcpt) ∧
    type_of% (C.edp05_row_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt) ∧
    type_of% (C.edgeRow_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt) ∧
    (∀ (x : C.edgeSource_EFE) (hx : C.edgeHeight_EFE x = 4 * Δ),
      type_of% (C.toGaf02ChainE.edge_rank_two_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 x hx)) ∧
    (∀ (x : C.edgeSource_EFE) (hx : C.edgeHeight_EFE x = 4 * Δ),
      type_of% (C.toGaf02ChainE.edge_corner_independence_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1
        x hx)) :=
  ⟨C.fc37_row_edp05_FCW A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg
      hdD hcpt,
    C.edp05_row_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD
      hcpt,
    C.edgeRow_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD
      hcpt,
    fun x hx => C.toGaf02ChainE.edge_rank_two_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 x hx,
    fun x hx => C.toGaf02ChainE.edge_corner_independence_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1
      x hx⟩

end Final

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
