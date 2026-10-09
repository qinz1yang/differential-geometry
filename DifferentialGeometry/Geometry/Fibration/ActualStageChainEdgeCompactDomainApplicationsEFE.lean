import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCompactDomainEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1Applications

/-!
# Consumer of FDC02 / EDP05 (G7): the final closed family, eventual form

Lane S-EDP-FDC3, group G7. `eventually_fdc02_edgeCompactDomain_C14Z_EFE`: on the final closed
family `LocalChartPacketsC14Z`, with the tail of `eventually_fdc02_M1_C14Z_EFC` (LC20, FDC02's
limit argument) and a chain `C : Gaf02ChainEJA …`, for EVERY `K₃, D₃` with ZSP04's properties
(`D₃ = K₃ ∩ C₃`, (SK), `∂K₃ ∩ F₃ = ∅`, regularity and the formula for `∂D₃` — exactly the outputs of
`zsp04_D3_ZSP35`) the compact edge base `C₂`, the saturation `M₂ ∩ X₂ = f₂⁻¹(C₂) ∩ X₂` and the
smooth local defining functions of `C₂ = {φ ≥ 0}` (EDP05's descent at every face) hold over the
abstract base `B₂ ⊆ W₂` (smooth stage bases `A`). `hcpt` of `edgeCompactDomain_EFE` is discharged
here: ZSP04's slim exclusion (`slim_far_of_relint_EFC`) feeds the FDC02 tail, whose compactness of
the witnessed piece becomes `M₂ ∩ X₂` by D74-11's set equality (`edgePiece_eq_EFE`).

The numeric premises of EDP04's whole disks (`hc … hβc1`, the register layer) are explicit. When the
edge family is empty (`B₂ = ∅`, as on the dihedral fixture) every set of the conclusion is empty
and the statement is vacuously true.
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

/-- **FDC02 / EDP05 on the final closed family** (see the module docstring). -/
theorem eventually_fdc02_edgeCompactDomain_C14Z_EFE {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
        μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 10 ^ 12 → μ * Δ < 1 / 10 ^ 4 →
        εr < 1 / 2 → e ≤ 1 / 1000 →
        ∀ P : LocalChartPacketsC14Z (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz oM,
        ∀ (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ) (cadj : ℝ)
          (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw
            cadj),
        c 2 < 1 / 100000 →
        100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
          1 / 1000000 → 0 ≤ ε → ε < 1 → b * (1000 * Δ) ≤ 1 → 0 < γc → γc ≤ 1 / 100 →
        βc ≤ 1 / 100000 →
        ∀ A : SmoothStageBasesOn74 C.toChain,
        ∀ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
          D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 →
          C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
            Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) →
          Disjoint (K₃.carrier \
              Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
            C.slimFacePoints_ZSP35 →
          D₃.carrier ⊆ closure (Subtype.val '' interior
            (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)) →
          D₃.carrier \ Subtype.val '' interior
              (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
            ((K₃.carrier \ Subtype.val '' interior
                  (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
                Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
              (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
                C.slimFacePoints_ZSP35) →
          let _ := A.edgeChartedSpace1
          IsCompact (C.edgeProj_EFE '' {x : C.edgeSource_EFE |
              (x : Y i) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧ C.edgeHeight_EFE x ≤ 4 * Δ}) ∧
            C.toGaf02ChainE.cutM2_R74 K₃.carrier ∩
                Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ} =
              Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x ∈ C.edgeProj_EFE ''
                {x : C.edgeSource_EFE | (x : Y i) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧
                  C.edgeHeight_EFE x ≤ 4 * Δ} ∧ C.edgeHeight_EFE x ≤ 4 * Δ} ∧
            ∀ c₀ ∈ frontier (C.edgeProj_EFE '' {x : C.edgeSource_EFE |
                (x : Y i) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧
                  C.edgeHeight_EFE x ≤ 4 * Δ}),
              ∃ U : TopologicalSpace.Opens C.edgeBaseOpens_EFE, c₀ ∈ U ∧
                ∃ φ : C.edgeBaseOpens_EFE → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c₀ = 0 ∧
                  mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c₀ ≠ 0 ∧
                  C.edgeProj_EFE '' {x : C.edgeSource_EFE |
                    (x : Y i) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧
                      C.edgeHeight_EFE x ≤ 4 * Δ} ∩ U = {c | c ∈ U ∧ 0 ≤ φ c} := by
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
  exact C.edgeCompactDomain_EFE A hεr hΔ2 hc hϑ hε0 hε (hμ) (hτ) (hσc.trans (by norm_num)) hb' hγc
    hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD hcpt

end DifferentialGeometry.Geometry.Collapse
