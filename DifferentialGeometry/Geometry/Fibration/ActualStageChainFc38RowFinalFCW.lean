import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38SaturationFinalFCW
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38RowHalfFCW

/-!
# FC38 (the remaining circle bundle): the FINAL row on the actual objects

Lane S-FC-WRAP4, group G13 (suffix `_FCW`). `Gaf02ChainEJA.fc38_row_final_FCW` is the conjunction,
for ONE given `K₃, D₃` with the five ZSP04 properties (`zsp04_D3_ZSP35`) and FDC02's compactness
`hcpt`, of: GAF07's circle row (`gaf07_circle_row_GAFD`), AOX's circle bundle, the strong circle
part (D1, D2), `E`-fibre constancy of `X₂°` (`fdc03_remainder_C14Z_FDC`), FDC03's saturation
`M₃ = (π₁E)⁻¹(C₁) ∩ X₁` with (hint') and (hsat) PROVED (`fdc03_saturation_final_FCW`),
compactness of `M₂`, `M₃` and (Last) at set level (`fdc03_remainder_compact_given_FCW`), the rim
as whole circle fibre (`edp06_rim_eq_whole_fibre_EFE`), and EDP06's whole row `edp06_row_EFE`
(saturation, rim point, corner data: face data, rank two, descent to the circle base). Not a
conjunct: the corner CHART as a set-level quadrant model of `C₁` (`edp06_base_chart_EFE` gives the
coordinates `(Tb, hb)`; the quadrant identification of `C₁` is not delivered), and the circle
bundle's `CircleBundle` structure assembly (the assembler's). READING (review 77, R13 / D77-3):
the EDP02 clauses are the full-norm theorems; no claim for the axis-coordinate reading.
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

/-- **FC38, the final row on the actual objects** (see the module docstring). -/
theorem fc38_row_final_FCW {cadj : ℝ}
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
    (hcpt : IsCompact (C.edgeM2_EFE K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    type_of% (C.gaf07_circle_row_GAFD hβ hd) ∧
    type_of% (Gaf02ChainEJA.gaf07_circle_bundle_C14Z_EFE P C hβ hd) ∧
    (∀ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      type_of% (C.toGaf02ChainE.gaf07_circle_piece_GAFD C.c_two_lt hβ hd i) ∧
      type_of% (C.toChain.gaf07_circle_chart_map_GAFD C.c_two_lt hβ hd i) ∧
      type_of% (C.toChain.gaf07_circle_local_trivial_GAFD C.c_two_lt hβ hd i)) ∧
    (∀ w (hW : w ∈ C.toChain.finalBase_BAS 0)
      (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
      (hm : 9 / 10 * ρ i.1 < blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w)
      (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w),
      type_of% (C.toGaf02ChainE.gaf07_circle_isotopy_GAFD C.c_two_lt hβ hd w hW i hm hr)) ∧
    type_of% (fdc03_remainder_C14Z_FDC C.toGaf02ChainE (hσc.trans (by norm_num))) ∧
    type_of% (C.fdc03_saturation_final_FCW A hβ hd hεr (hσc.trans (by norm_num)) hγ hγ1 hΔ2 hc hϑ
      hε0 hε hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD) ∧
    type_of% (C.fdc03_remainder_compact_given_FCW hεr K₃ D₃ hD hKs hDreg) ∧
    type_of% (C.edp06_rim_eq_whole_fibre_EFE hβ hd) ∧
    type_of% (C.edp06_row_EFE A hβ hd hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
      hKs hKF hDreg hdD hcpt) :=
  ⟨C.gaf07_circle_row_GAFD hβ hd, Gaf02ChainEJA.gaf07_circle_bundle_C14Z_EFE P C hβ hd,
    fun i => ⟨C.toGaf02ChainE.gaf07_circle_piece_GAFD C.c_two_lt hβ hd i,
      C.toChain.gaf07_circle_chart_map_GAFD C.c_two_lt hβ hd i,
      C.toChain.gaf07_circle_local_trivial_GAFD C.c_two_lt hβ hd i⟩,
    fun w hW i hm hr => C.toGaf02ChainE.gaf07_circle_isotopy_GAFD C.c_two_lt hβ hd w hW i hm hr,
    fdc03_remainder_C14Z_FDC C.toGaf02ChainE (hσc.trans (by norm_num)),
    C.fdc03_saturation_final_FCW A hβ hd hεr (hσc.trans (by norm_num)) hγ hγ1 hΔ2 hc hϑ hε0 hε
      hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD,
    C.fdc03_remainder_compact_given_FCW hεr K₃ D₃ hD hKs hDreg,
    C.edp06_rim_eq_whole_fibre_EFE hβ hd,
    C.edp06_row_EFE A hβ hd hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
