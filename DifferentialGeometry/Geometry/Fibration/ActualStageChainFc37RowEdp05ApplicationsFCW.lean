import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCompactDomainApplicationsEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc37RowEdp05FCW

/-!
# Consumer of the FC37 row candidate (G7): the final closed family, eventual form

Lane S-FC-WRAP2, group G7. `eventually_fc37_row_C14Z_FCW`: on the final closed family
`LocalChartPacketsC14Z`, with the tail of `eventually_fdc02_M1_C14Z_EFC` (LC20, FDC02's limit
argument), for EVERY chain with (JA), stage bases `A` and ZSP04's `K₃, D₃` the conjunction of the
chain-level EDP02 / EDP04 row (`fc37_row_edp02_FCW`), E1 (compact edge base `C₂`, saturation of
`M₂ ∩ X₂`, smooth defining functions at every frontier point: `eventually_fdc02_edgeCompactDomain_
C14Z_EFE`, FDC02's compactness discharged by the tail) and FDC02's finite arc / circle components
of `C₂` (`edgeBase_components_FCW`). The numerics are the register's.
-/


set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open GC.GraphManifold.Assembly.FC39P0

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

/-- **FC37, the row candidate on the final closed family, eventual form** (see the module
docstring). -/
theorem eventually_fc37_row_C14Z_FCW {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
        ∀ (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 10 ^ 12), μ * Δ < 1 / 10 ^ 4 →
        εr < 1 / 2 → e ≤ 1 / 1000 →
        ∀ P : LocalChartPacketsC14Z (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz oM,
        ∀ (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ) (cadj : ℝ)
          (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw
            cadj),
        ∀ (hc : c 2 < 1 / 100000)
          (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
            1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hb' : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc)
          (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000),
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
          type_of% (C.fc37_row_edp02_FCW (by linarith) hc hϑ hε0 hε hμ hτ
            (hσc.trans (by norm_num)) hb' hγc hγc1 hβc1) ∧
          let _ := A.edgeChartedSpace1
          have _ := A.edge_isManifold1.1
          (
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
                      C.edgeHeight_EFE x ≤ 4 * Δ} ∩ U = {c | c ∈ U ∧ 0 ≤ φ c}) ∧
          (∃ (m l : ℕ) (e : (Fin m ⊕ Fin l) ≃ ActualComponent
              (C.edgeProj_EFE '' {x : C.edgeSource_EFE |
              (x : Y i) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧ C.edgeHeight_EFE x ≤ 4 * Δ}))
            (a : Fin m → Icc (0 : ℝ) 1 → C.edgeBaseOpens_EFE)
            (c : Fin l → Circle → C.edgeBaseOpens_EFE)
            (ε : (Fin m × Bool) ≃ {x : C.edgeBaseOpens_EFE // x ∈ frontier
              (C.edgeProj_EFE '' {x : C.edgeSource_EFE |
              (x : Y i) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧ C.edgeHeight_EFE x ≤ 4 * Δ})}),
            (∀ i, Manifold.IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (a i)) ∧
            (∀ i, range (a i) = (e (Sum.inl i)).1) ∧
            (∀ j, Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (c j)) ∧
            (∀ j, range (c j) = (e (Sum.inr j)).1) ∧
            ∀ i b, (ε (i, b)).1 = a i (GC.GraphManifold.Assembly.iccEnd b))
  := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ :=
    eventually_fdc02_edgeCompactDomain_C14Z_EFE hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw cadj C hc hϑ hε0 hε hb' hγc hγc1 hβc1
    A K₃ D₃ hD hKs hKF hDreg hdD
  have hE1 := hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3
    hβ2 hb hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw cadj C hc hϑ hε0 hε hb' hγc hγc1
    hβc1 A K₃ D₃ hD hKs hKF hDreg hdD
  refine ⟨C.fc37_row_edp02_FCW (by linarith) hc hϑ hε0 hε hμ hτ (hσc.trans (by norm_num)) hb'
    hγc hγc1 hβc1, ?_⟩
  exact ⟨hE1, C.toGaf02ChainE.edgeBase_components_FCW A hE1.1 hE1.2.2⟩

end DifferentialGeometry.Geometry.Collapse
