import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimCircleApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1Applications

/-!
# Consumer of the EDP06 row (G10 of S-EDP-FDC4): the final closed family, eventual form

Lane S-FC-WRAP4, group G14 (suffix `_FCW`). `eventually_edp06_row_C14Z_FCW`: on the final closed
family `LocalChartPacketsC14Z`, merging the tail of `eventually_fdc02_M1_C14Z_EFC` (FDC02's limit
argument; it discharges the compactness `hcpt` as in `eventually_fdc02_edgeRow_C14Z_EFE`) and the
tail of `eventually_edp06_rim_mem_X₁_C14Z_EFC` (EDP06's first clause `∂X₂ ⊆ X₁`, which discharges
the `hX₁` of the corner part via `mem_circleDomain_of_EFE`), for EVERY chain with (JA), stage
bases `A` and every `K₃, D₃` with ZSP04's five properties: `hcpt` holds, and the three clauses of
`edp06_row_EFE` (saturation of `M₂ ∩ X₁` by whole circle fibres, rim point over every point of
`B₂`, corner data at every endpoint of `C₂` and rim point over it) hold, the corner part with the
membership `q₀ ∈ circleDomain` PRODUCED (an `∃`). Numerics: those of the two tails plus the GAF07
pair `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`, `0 ≤ γ ≤ 3/4`, `3 βc ≤ β₂` (register layer).
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

/-- **EDP06's whole row on the final closed family, eventual form** (see the module docstring). -/
theorem eventually_edp06_row_C14Z_FCW {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
        (h3βc : 3 * βc ≤ βY 2) → (hβ : βY 2 ≤ 1 / 10000000) → (hγ : 0 ≤ γ) → (hγ1 : γ ≤ 3 / 4) →
        (hd : γ + βY 2 < 1 / 10) →
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
            type_of% (C.edp06_saturation_EFE hβ hd hεr K₃ D₃ hD hKs hKF hDreg hdD) ∧
            (∀ cc : C.edgeBaseOpens_EFE, type_of% (C.toGaf02ChainE.edge_rim_point_EFE
              (le_trans (by norm_num) hΔ) hc hϑ hε0 hε hμ hτ (hσc.trans (by norm_num)) hb' hγc
              hγc1 hβc1 cc)) ∧
            (∀ (c₀ : C.edgeBaseOpens_EFE) (hc₀ : c₀ ∈ frontier (C.edgeC2_EFE K₃))
              (q₀ : C.edgeSource_EFE) (hq₀c : C.edgeProj_EFE q₀ = c₀)
              (hT : C.edgeHeight_EFE q₀ = 4 * Δ),
              ∃ hX₁ : q₀.1 ∈ C.circleDomain_EFE,
                type_of% (C.edp06_corner_EFE A hβ hd hεr (le_trans (by norm_num) hΔ) hc hϑ hε0 hε
                  hμ hτ (hσc.trans (by norm_num)) hb' hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD
                  hcpt hc₀ q₀ hq₀c hT hX₁)) := by
  refine (eventually_fdc02_M1_C14Z_EFC hΔ hβ₂ hβ₂1 hΛ₀).imp fun Lc h1 => h1.imp fun η₀ h2 =>
    ⟨h2.1, h2.2.1, ?_⟩
  have h3 := h2.2.2
  obtain ⟨w₀', hw₀', hrim⟩ := eventually_edp06_rim_mem_X₁_C14Z_EFC hΛ₀
  refine h3.elim fun w₀ h4 => ⟨min w₀ w₀', lt_min h4.1 hw₀', ?_⟩
  have htail := h4.2
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  have hww0 : w < w₀ := lt_of_lt_of_le hww (min_le_left _ _)
  have hww1 : w < w₀' := lt_of_lt_of_le hww (min_le_right _ _)
  filter_upwards [htail w hw hww0 hwc Y gY hmY α hα hstand,
    hrim w hw hww1 hwc Y gY hmY α hα hstand] with n hn hrn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he h3βc hβ hγ hγ1 hd P Kj Ξ Γ S eg c cw cadj C hc hϑ hε0 hε
    hb' hγc hγc1 hβc1 A K₃ D₃ hD hKs hKF hDreg hdD
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
  have hσc' : σc ≤ 1 / 1000 := hσc.trans (by norm_num)
  refine ⟨hcpt, C.edp06_saturation_EFE hβ hd hεr K₃ D₃ hD hKs hKF hDreg hdD,
    fun cc => C.toGaf02ChainE.edge_rim_point_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc' hb' hγc hγc1 hβc1 cc,
    fun c₀ hc₀ q₀ hq₀c hT => ?_⟩
  have hX₁ : q₀.1 ∈ C.circleDomain_EFE := by
    have hR := C.toGaf02ChainE.edgeSource_mem_EFE q₀.2
    have hV : q₀.1 ∈ {x | P.edge.smoothing x / ρY x ≤ 7 / 20 * Δ} ∪ {x | 0 < C.toChain.scale x ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartPackets.toLocalChartFamily
          P.toLocalChartPackets.zero (C.toChain.E x)) / C.toChain.scale x ≤ 4 * Δ} :=
      Or.inr ⟨(C.toChain.scale_pos q₀.1).2, hT.le⟩
    obtain ⟨-, hW0, hR0⟩ := hrn ρY hρY hwin Λ βY Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz oM hβ3 h3βc (hβ2.trans (by norm_num)) hγ hγ1 hΔ2 P Kj Ξ Γ S eg c cw cadj C hc hϑ hε0
      hε q₀.1 ⟨hR, hV⟩ hT
    exact C.mem_circleDomain_of_EFE hW0 hR0
  exact ⟨hX₁, C.edp06_corner_EFE A hβ hd hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc' hb' hγc hγc1 hβc1 K₃ D₃
    hD hKs hKF hDreg hdD hcpt hc₀ q₀ hq₀c hT hX₁⟩

end DifferentialGeometry.Geometry.Collapse
