import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimCircle
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpHeightApplications

/-!
# Consumer: EDP06's first clause on the final closed family — `∂X₂ ⊆ X₁`, two-stratum

Blueprint `master207B.tex`, EDP06 (B:7092–7108: "The whole vertical boundary `∂X₂` lies in GAF07's
circle region `X₁`"; proof: (ELoc), (EH), LFR38 (two-stratum), LPA06 (circle chart `|η_a| < 2`),
GAF07). On LC20's tail, for the final closed family `P : LocalChartPacketsC14Z` and an enhanced
chain with (JA) `Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 …`, every point
of the ACTUAL `X₂ = (π₂E)⁻¹(B₂) ∩ V` with `T = 4Δ` is two-stratum and lies in
`X₁ = (π₁E)⁻¹(W₁ ∩ R₁)`: `eventually_edp06_rim_mem_X₁_C14Z_EFC`, composing
`Gaf02ChainE.rim_localization_EFC` (this lane), lane C14-EDP-E's
`eventually_edp06_final_rim_circle_EDPE` (LFR38 + LPA06 on the tail) and lane C14-FDCb's
`circle_ball_mem_X₁_FDC` (GAF07). Here `∂X₂` is read as `X₂ ∩ {T = 4Δ}` (EDP04's (EV)).

Premises: those of EDP-E's rim lemma (`β₃` below LC18's threshold, `3βc ≤ β₂ < 1`, `0 ≤ γ`,
`c₃ < 10⁻⁵`, `C_ρΛΔ < 10⁻⁶`, `0 ≤ ε < 1`), `γ ≤ 3/4` (FDC03's circle ball) and `Δ ≥ 2` ((ELoc)).
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

/-- **EDP06's first clause on the final closed family** (LC20's tail): every point of the actual
`X₂` with `T = 4Δ` is two-stratum and lies in GAF07's circle region `X₁`. -/
theorem eventually_edp06_rim_mem_X₁_C14Z_EFC {Λ₀ : ℝ} (hΛ₀ : 0 < Λ₀) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
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
        ∀ (Λ : ℝ) (βY : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
          (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
          (oM : ManifoldOrientation 𝓘(ℝ, E3) (Y i) 3),
        βY 3 ≤ threeSplittingExclusionThreshold.{0, 0} → 3 * βc ≤ βY 2 → βY 2 < 1 → 0 ≤ γ →
        γ ≤ 3 / 4 → 2 ≤ Δ →
        ∀ P : LocalChartPacketsC14Z (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz oM,
        ∀ (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ) (cadj : ℝ)
          (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw
            cadj),
        c 2 < 1 / 100000 →
        100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
          1 / 1000000 → 0 ≤ ε → ε < 1 →
        ∀ p ∈ {x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x) ∈
                Ĉ.toChain.finalBase_BAS 1 ∧
            ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
              9 / 10 * ρY k.1 < blockMarkerCLM (V := fun _ : CGPTag
                  P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
                (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x)) ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
                ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x))‖ <
              4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
                ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x))} ∩
          ({x | P.edge.smoothing x / ρY x ≤ 7 / 20 * Δ} ∪ {x | 0 < Ĉ.toChain.scale x ∧
            EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
              P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ}),
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartPackets.toLocalChartFamily
          P.toLocalChartPackets.zero (Ĉ.toChain.E p)) / Ĉ.toChain.scale p = 4 * Δ →
        p ∈ scaledSplittingStratum.{0, 0} ρY hρY βY 2 ∧
          (gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
              0).starProjection (Ĉ.toChain.E p) ∈
            Ĉ.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets := by
  obtain ⟨w₀, hw₀, hrim⟩ := eventually_edp06_final_rim_circle_EDPE hΛ₀
  refine ⟨w₀, hw₀, ?_⟩
  intro w hw hww hwc Y mY _ _ _ gY hmY α hα hstand
  filter_upwards [hrim w hw hww hwc Y gY hmY α hα hstand] with i hi
  intro ρY hρY hwin Λ βY Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 h3βc
    hβ2 hγ hγ1 hΔ P Kj Ξ Γ S eg c cw cadj Ĉ hc hϑ hε0 hε p hp hT4
  obtain ⟨k, hball, hη, ht, hg⟩ := Ĉ.toGaf02ChainE.rim_localization_EFC hΔ hp hT4
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  obtain ⟨h2, a, ha, hpa, -⟩ := hi ρY hρY hwin Λ βY Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
    e T V vs ζ Λz hβ3 h3βc hβ2 hγ P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c
    cw Ĉ.toChain (Ĉ.rough.cw_nonneg 0) (Ĉ.rough.sigma_le 0).le hc hϑ hε0 hε k.1 hk p hball hη ht
    hg hT4
  exact ⟨h2, Ĉ.rim_mem_X₁_of_circle_ball_EFC hγ hγ1 ha hpa⟩

end DifferentialGeometry.Geometry.Collapse
