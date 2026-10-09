import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCompactDomainEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1Applications

import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRowFacesEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1Applications

/-!
# Consumer of the whole edge row (G9): the final closed family, eventual form

Lane S-EDP-FDC4, group G9. `eventually_fdc02_edgeRow_C14Z_EFE`: on the final closed family
`LocalChartPacketsC14Z`, with the tail of `eventually_fdc02_M1_C14Z_EFC` (LC20, FDC02's limit
argument) and a chain `C : Gaf02ChainEJA …`, for EVERY `K₃, D₃` with ZSP04's properties the compact
edge piece `M^edge = M₂ ∩ X₂` is compact (`hcpt`, FDC02's limit argument, as in G7) and the whole
row `edgeRow_EFE` holds with that `hcpt` (compact smooth base domain `C₂`, finite interval / circle
components, the `EdgeBundle` data over `B₂`, and the faces (EF)). The numeric premises of EDP04
(`hc … hβc1`, the register layer) and the stage bases `A` are explicit. Edge family empty
(`B₂ = ∅`): every set is empty and the statement is vacuous.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

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

/-- **The whole FDC02 / EDP05 row on the final closed family** (see the module docstring). -/
theorem eventually_fdc02_edgeRow_C14Z_EFE {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000) (hΛ₀ : 0 < Λ₀) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧ ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (Y : ℕ → Type) [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E3 (Y i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (Y i)] [∀ i, CompactSpace (Y i)]
        (gY : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (Y i))
        (hmY : ∀ i a b, riemannianEDistOf (gY i) a b = ENNReal.ofReal (dist a b)),
      ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
      (∀ i (p : Y i), ENNReal.ofReal (α i * firstVolumeScale (gY i) p (α i)⁻¹) ≤
        curvatureRadius (gY i) p) →
      ∀ᶠ i in atTop, ∀ (ρY : Y i → ℝ) (hρY : ∀ y, 0 < ρY y),
        (∀ p, firstVolumeScale (gY i) p w / 2 ≤ ρY p ∧
          ρY p ≤ 2 * firstVolumeScale (gY i) p (w / (2 * (1 + 2 * Λ₀⁻¹) ^ 3))) →
        ∀ (Λ : ℝ) (βY : ℕ → ℝ) (σs : ℝ) (K : ℕ)
          (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
          (oM : ManifoldOrientation 𝓘(ℝ, E3) (Y i) 3),
        βY 3 ≤ threeSplittingExclusionThreshold.{0, 0} → βY 2 < 1 / 1000000 →
        b < 1 / 1000000 → b ≤ η₀ → s < 1 / 1000000 → βY 1 ≤ η₀ → Lc ≤ Lmax →
        (hμ : μ ≤ 1 / 10 ^ 8) → (hτ : τ ≤ 1 / 10 ^ 8) → (hσc : σc ≤ 1 / 10 ^ 12) →
        μ * Δ < 1 / 10 ^ 4 → (hεr : εr < 1 / 2) → e ≤ 1 / 1000 →
        ∀ P : LocalChartPacketsC14Z (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz oM,
        ∀ (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ) (cadj : ℝ)
          (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw
            cadj),
        (hc : c 2 < 1 / 100000) →
        (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
          1 / 1000000) → (hε0 : 0 ≤ ε) → (hε : ε < 1) → (hb' : b * (1000 * Δ) ≤ 1) →
        (hγc : 0 < γc) → (hγc1 : γc ≤ 1 / 100) → (hβc1 : βc ≤ 1 / 100000) →
        ∀ A : SmoothStageBasesOn74 C.toChain,
        ∀ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
          (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35) →
          (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
            Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) →
          (hKF : Disjoint (K₃.carrier \
              Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
            C.slimFacePoints_ZSP35) →
          (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
            (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35))) →
          (hdD : D₃.carrier \ Subtype.val '' interior
              (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
            ((K₃.carrier \ Subtype.val '' interior
                  (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
                Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
              (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
                C.slimFacePoints_ZSP35)) →
          ∃ hcpt : IsCompact (C.edgeM2_EFE K₃ ∩
              Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ}),
            type_of% (C.edgeRow_EFE A hεr (le_trans (by norm_num) hΔ) hc hϑ hε0 hε hμ hτ
              (hσc.trans (by norm_num)) hb' hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD hcpt) := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc02_M1_C14Z_EFC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw cadj C hc hϑ hε0 hε hb' hγc hγc1 hβc1
    A K₃ D₃ hD hKs hKF hDreg hdD
  have hΔ2 : 2 ≤ Δ := by linarith
  have hSeq : C.slimPiece_ZSP35 K₃.carrier =
      (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' K₃.carrier :=
    (C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg).2.1
  have hS' : ∀ q ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier, ∀ k (hk : k ∈ P.slim.centres),
      dist q k < 9 * Δ * ρY k → 10 * Δ ≤ |(P.slim.centre k hk).coord q| := fun q hq k hk hd =>
    C.toGaf02ChainE.slim_far_of_relint_EFC (fun w hw => hKs (Or.inl hw))
      (M₁ := (interior C.zeroUnion_ZSP35)ᶜ)
      (fun p hp hpK => by rw [hSeq]; exact ⟨hp, hpK⟩) hq hk hd
  have hM := hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3
    hβ2 hb hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw C.toGaf02ChainE
    C.zeroUnion_ZSP35 (C.slimPiece_ZSP35 K₃.carrier) (interior C.zeroUnion_ZSP35)ᶜ
    (C.toGaf02ChainE.cutM2_R74 K₃.carrier) rfl rfl rfl hS'
  have hcpt : IsCompact (C.toGaf02ChainE.cutM2_R74 K₃.carrier ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ}) := by
    rw [C.toGaf02ChainE.edgePiece_eq_EFE hΔ2, hM.1]
    exact hM.2.1
  exact ⟨hcpt, C.edgeRow_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ (hσc.trans (by norm_num)) hb' hγc
    hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD hcpt⟩

end DifferentialGeometry.Geometry.Collapse
