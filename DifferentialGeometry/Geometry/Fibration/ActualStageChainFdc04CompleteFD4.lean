import DifferentialGeometry.Geometry.Fibration.ActualStageChainFdc04RowFD4
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCornersEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38RowFinalFCW

/-!
# FDC04: the COMPLETE row on the actual chain (G5, chain form)

Lane S-FDC04b (`_FD4`), group G5. Blueprint `master207B.tex`, FDC04
(`thm:fibration-actual-closed-decomposition`, B:7367-7435). On the final family
`LocalChartPacketsC14Z`, for a chain `C : Gaf02ChainEJA ...` with (JA), the smooth stage bases `A`,
ANY admissible `K₃, D₃` (the five properties of `zsp04_D3_ZSP35`) and `hcpt` (FDC02's compactness
of `M^edge`; the tail form of the next file discharges it), `Gaf02ChainEJA.fdc04_row_complete_FD4`
is the conjunction of

1. `fdc04_row_FD4` (G3: zero pieces, slim pieces, four-piece cover, edge pieces, FDC02 row,
   whole horizontal disks in `∂M₂`);
2. `edp05_row_EFE` (S-EDP-FDC4 G11: whole EDP05 row, in particular `edge_disk_in_face_EFE`: the
   whole horizontal disk over an endpoint of `C₂` lies in ONE zero face or slim fibre of `∂M₂`);
3. `fc38_row_final_FCW` (S-FC-WRAP4 G13: FC38's final row on the same `K₃, D₃`: circle bundle,
   saturation `M₃ = (π₁E)⁻¹(C₁) ∩ X₁`, `C₁ ⊆ B₁`, compactness, rim = whole circle fibre, the whole
   EDP06 row with corner data).

NOT in this row (single-listed gaps, see the clause table of the delivery block): the set-level
quadrant model of `C₁` / finite list of components of `M₃`, the mapping torus structure of the slim
loops and the product structure `S¹ × D²` of the circular edge components (E4a-c, D74-12), FC41
corner rounding and FC42's KL graph presentation. The numeric premises are the register's.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

namespace Gaf02ChainEJA

/-- **FDC04, the complete row on the actual chain** (see the module docstring). -/
theorem fdc04_row_complete_FD4 {cadj : ℝ}
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4)
    (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
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
    (hK : 5 ≤ K) (hcpt : IsCompact (C.edgeA_FD4 K₃ Δ)) :
    type_of% (C.fdc04_row_FD4 A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hK hcpt) ∧
    type_of% (C.edp05_row_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt) ∧
    type_of% (fc38_row_final_FCW P C A hβ hd hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγ hγ1 hγc hγc1
      hβc1 K₃ D₃ hD hKs hKF hDreg hdD hcpt) :=
  ⟨C.fdc04_row_FD4 A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD
      hK hcpt,
    C.edp05_row_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD
      hcpt,
    fc38_row_final_FCW P C A hβ hd hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγ hγ1 hγc hγc1 hβc1 K₃ D₃
      hD hKs hKF hDreg hdD hcpt⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
