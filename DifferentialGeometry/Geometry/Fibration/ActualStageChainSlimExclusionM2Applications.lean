import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimExclusionM2
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1Applications

/-!
# Consumers: FDC01 / FDC02 / FDC04 on the ACTUAL `M₂` (both halves of `q ∈ M₂` discharged)

Blueprint `master207B.tex`, FDC01 (B:7157–7244), on the final closed family `LocalChartPacketsC14Z`
with an enhanced chain with (JA). `eventually_fdc01_M2_C14Z_EFC` composes this lane's G1 consumer
`eventually_fdc01_M1_C14Z_EFC` (zero half: ZSP02's actual `Z`) with `exists_slimPiece_hS_C14Z_EFC`
(slim half: ZSP04's actual `K₃`, lane C14-ZSP35d): for the actual `M₂ = (M ∖ int Z) ∖ int_{M ∖ int
Z} M^slim(K₃)`, every edge-near point of `M₂` satisfies FDC01's conclusion with NO exclusion
hypothesis. Premises: those of G1's consumer (incl. `εr < 1/2` and LC30's `e ≤ 1/1000`); (JA) is the
chain's.
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **FDC01 with q ∈ the ACTUAL `M₂`** (LC20's tail, final family): ZSP02's actual zero domains (`M₁
= M ∖ int Z`) and ZSP04's actual `K₃` (`M₂ = M₁ ∖ int_{M₁} M^slim(K₃)`, with (SK)); for every `q ∈
M₂` in `U_j` with `|η_j(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`: `p_j` is a nonslim one-stratum point and a
selected `k ∈ J_e(j)` satisfies (Repl) with `π₂E(q) ∈ W₂ ∩ {v_k > .9R_k, |u_k| < 4Δ v_k} ⊆ B₂`. No
exclusion hypothesis on `q` remains. -/
theorem eventually_fdc01_M2_C14Z_EFC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000) (hΛ₀ : 0 < Λ₀) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧ ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (Y : ℕ → Type) [mY : ∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E3 (Y i)]
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
          (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw
            cadj),
        ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF Ĉ.slimBs_ZSP35,
        Ĉ.toChain.slimSlabImage_ZSP35 ⊆
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35) ∧
        ∀ j ∈ P.edge.centres, ∀ q ∈ (interior Ĉ.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
            (Subtype.val ⁻¹' Ĉ.slimPiece_ZSP35 K₃.carrier : Set ↥(interior Ĉ.zeroUnion_ZSP35)ᶜ),
          q ∈ ball j (100 * Δ * ρY j) →
          |P.edge.coord j q| ≤ 401 / 100 * Δ → P.edge.smoothing q / ρY q ≤ 401 / 100 * Δ →
          j ∈ scaledSplittingStratum.{0, 0} ρY hρY βY 1 ∧
          ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
            Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
            Nonempty (@KleinerLottApprox (Y i) (WithLp 2 (ℝ × Z))
              ((mY i).rescale (ρY j)⁻¹ (inv_pos.mpr (hρY j))) _ j (WithLp.toLp 2 ((0 : ℝ), z))
                (βY 1))) ∧
          ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
            k.1 ∈ egpEdgeList P.toLocalChartFamily j ∧
            |P.edge.coord k.1 q| < 2 * Δ ∧ P.edge.cutoff k.1 q = 1 ∧
            blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
                ((gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                  1).starProjection (Ĉ.toChain.E q)) = ρY k.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
                ((gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                  1).starProjection (Ĉ.toChain.E q))‖ / ρY k.1 < 3 * Δ ∧
            (gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                1).starProjection (Ĉ.toChain.E q) ∈ Ĉ.toChain.finalBase_BAS 1 ∧
            9 / 10 * ρY k.1 < blockMarkerCLM (V := fun _ : CGPTag
                P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
                (.inr (.inr (.inl k)))
                ((gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                  1).starProjection (Ĉ.toChain.E q)) ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
                ((gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                  1).starProjection (Ĉ.toChain.E q))‖ <
              4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
                ((gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                  1).starProjection (Ĉ.toChain.E q)) := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc01_M1_C14Z_EFC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y mY _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw cadj Ĉ
  obtain ⟨K₃, hSK, -, hS⟩ := exists_slimPiece_hS_C14Z_EFC Ĉ hεr
  refine ⟨K₃, hSK, fun j hj q hq hqb hηq htq => ?_⟩
  exact hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw Ĉ.toGaf02ChainE j hj q hqb hηq htq
    hq.1 (hS q hq)

/-- **FDC02 for the ACTUAL `M₂`** (LC20's tail, final family): with ZSP02's `Z`, `M₁ = M ∖ int Z`
and ZSP04's `K₃` (`M₂ = M₁ ∖ int_{M₁} M^slim(K₃)`, (SK)), `M₂ ∩ X₂` equals the witnessed piece,
is compact, and its base `C₂ = π₂E(M₂ ∩ X₂)` is compact. No exclusion hypothesis remains. -/
theorem eventually_fdc02_M2_C14Z_EFC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
          (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw
            cadj),
        ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF Ĉ.slimBs_ZSP35,
        Ĉ.toChain.slimSlabImage_ZSP35 ⊆
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35) ∧
        ∀ (Z M₁ M₂ : Set (Y i)),
          Z = ⋃ k : P.zero.finite_centres.toFinset,
            zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E →
          M₁ = (interior Z)ᶜ →
          M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' Ĉ.slimPiece_ZSP35 K₃.carrier :
            Set M₁) →
          M₂ ∩ ({x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x) ∈
                Ĉ.toChain.finalBase_BAS 1 ∧
              ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
                9 / 10 * ρY k.1 < blockMarkerCLM (V := fun _ : CGPTag
                    P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
                    (.inr (.inr (.inl k)))
                    ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
                      P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x)) ∧
                ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                    P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
                    ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
                      P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x))‖ <
                  4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
                    P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
                    (.inr (.inr (.inl k)))
                    ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
                      P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x))} ∩
            ({p | P.edge.smoothing p / ρY p ≤ 7 / 20 * Δ} ∪
              {p | 0 < Ĉ.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
                P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                  (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ})) =
            M₂ ∩ ({p | P.edge.smoothing p / ρY p ≤ 7 / 20 * Δ} ∪
              {p | 0 < Ĉ.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
                P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                  (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∩
            {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
              blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) =
                ρY k.1 ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
                4 * Δ * ρY k.1} ∧
          IsCompact (M₂ ∩ ({p | P.edge.smoothing p / ρY p ≤ 7 / 20 * Δ} ∪
            {p | 0 < Ĉ.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
              P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∩
            {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
              blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) =
                ρY k.1 ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
                4 * Δ * ρY k.1}) ∧
          IsCompact ((fun x => (gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x)) ''
            (M₂ ∩ ({p | P.edge.smoothing p / ρY p ≤ 7 / 20 * Δ} ∪
            {p | 0 < Ĉ.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
              P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∩
            {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
              blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) =
                ρY k.1 ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
                4 * Δ * ρY k.1})) := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc02_M1_C14Z_EFC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw cadj Ĉ
  obtain ⟨K₃, hSK, -, hS⟩ := exists_slimPiece_hS_C14Z_EFC Ĉ hεr
  refine ⟨K₃, hSK, fun Z M₁ M₂ hZ hM₁ hM₂ => ?_⟩
  have hS' : ∀ q ∈ M₂, ∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
      10 * Δ ≤ |(P.slim.centre k hk).coord q| := by
    subst hZ hM₁ hM₂
    exact hS
  exact hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw Ĉ.toGaf02ChainE Z
    (Ĉ.slimPiece_ZSP35 K₃.carrier) M₁ M₂ hZ hM₁ hM₂ hS'

/-- **FDC04's four-piece cover for the ACTUAL pieces** (LC20's tail, final family, point-set level):
ZSP02's `Z`, ZSP04's `M^slim(K₃)` (with (SK)), the actual `M₂ = M₁ ∖ int_{M₁} M^slim`, the compact
edge piece `A = M^edge` and `M₃ = M₂ ∖ int_{M₂} A`: `A`, `M₃` compact, `M₂ = A ∪ M₃`, the four
pieces cover the carrier and their ambient interiors are pairwise disjoint. No hypothesis on the
pieces remains (ZSP04's regularity and collar clauses are supplied by `zsp04_row_ZSP35`). -/
theorem eventually_fdc04_M2_C14Z_EFC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
          (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw
            cadj),
        ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF Ĉ.slimBs_ZSP35,
        Ĉ.toChain.slimSlabImage_ZSP35 ⊆
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35) ∧
        ∀ (Z M₁ M₂ A M₃ : Set (Y i)),
          Z = ⋃ k : P.zero.finite_centres.toFinset,
            zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E → M₁ = (interior Z)ᶜ →
          M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' Ĉ.slimPiece_ZSP35 K₃.carrier :
            Set M₁) →
          A = M₂ ∩ ({p | P.edge.smoothing p / ρY p ≤ 7 / 20 * Δ} ∪
            {p | 0 < Ĉ.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
              P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∩
            {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
              blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) =
                ρY k.1 ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
                4 * Δ * ρY k.1} →
          M₃ = M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) →
          IsCompact A ∧ IsCompact M₃ ∧ M₂ = A ∪ M₃ ∧
            A ∩ M₃ = A \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) ∧
            Z ∪ Ĉ.slimPiece_ZSP35 K₃.carrier ∪ A ∪ M₃ = univ ∧
            Disjoint (interior Z) (interior (Ĉ.slimPiece_ZSP35 K₃.carrier)) ∧
            Disjoint (interior Z) (interior A) ∧ Disjoint (interior Z) (interior M₃) ∧
            Disjoint (interior (Ĉ.slimPiece_ZSP35 K₃.carrier)) (interior A) ∧
            Disjoint (interior (Ĉ.slimPiece_ZSP35 K₃.carrier)) (interior M₃) ∧
            Disjoint (interior A) (interior M₃) := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc04_M1_C14Z_EFC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw cadj Ĉ
  obtain ⟨K₃, hKs, -, -, -, hSeq, -, hreg, -, -, hcollar, -, -⟩ := Ĉ.zsp04_row_ZSP35 hεr
  refine ⟨K₃, fun w hw => hKs (Or.inl hw), fun Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ => ?_⟩
  have hSM : Ĉ.slimPiece_ZSP35 K₃.carrier ⊆ (interior Z)ᶜ := by
    subst hZ
    rw [hSeq]
    exact inter_subset_left
  have hcol : Ĉ.slimPiece_ZSP35 K₃.carrier ∩ frontier (interior Z)ᶜ ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' Ĉ.slimPiece_ZSP35 K₃.carrier :
        Set ↥(interior Z)ᶜ) := by
    subst hZ
    exact hcollar
  have hS : ∀ q ∈ M₂, ∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
      10 * Δ ≤ |(P.slim.centre k hk).coord q| := by
    subst hZ hM₁ hM₂
    exact fun q hq k hk hd => Ĉ.toGaf02ChainE.slim_far_of_relint_EFC
      (fun w hw => hKs (Or.inl hw)) (M₁ := (interior Ĉ.zeroUnion_ZSP35)ᶜ)
      (fun p hp hpK => by rw [hSeq]; exact ⟨hp, hpK⟩) hq hk hd
  exact hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw Ĉ.toGaf02ChainE Z
    (Ĉ.slimPiece_ZSP35 K₃.carrier) M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ hSM hreg hcol hS

end DifferentialGeometry.Geometry.Collapse
