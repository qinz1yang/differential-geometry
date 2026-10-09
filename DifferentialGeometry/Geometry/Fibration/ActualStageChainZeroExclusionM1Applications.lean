import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFourPieceCover

/-!
# Consumers: FDC01, FDC02, FDC04 with the ACTUAL zero domains (the zero half of `q ∈ M₂`)

Blueprint `master207B.tex`, FDC01 (B:7157–7244), FDC02 (B:7246–7283), FDC04 (B:7367–7383), on the
final closed family `LocalChartPacketsC14Z` with an enhanced chain
`Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 …`. Lane C14-FDCb's consumers
carry `q ∈ M₂` as two original-coordinate exclusions `hZ` (outside every `.38`-zero ball) and `hS`
(outside every slim region). Here `hZ` is DISCHARGED by ZSP02's actual zero domains
`Z = ⋃_k Z_k` (`zspDomain_ZSP35 … Ĉ.E`, lane C14-ZSP35b), `M₁ = M \ int Z` (ZSP03, B:6483) and
`M₂ = M₁ \ int_{M₁} Sl` (ZSP05's (RC), B:6601) for an arbitrary slim set `Sl`:

* `eventually_fdc01_M1_C14Z_EFC` — FDC01 for `q ∉ int Z` (and `hS`);
* `eventually_fdc02_M1_C14Z_EFC` — FDC02 (`M₂ ∩ X₂` = witnessed piece, compact; `C₂` compact) for
  the actual `M₂` of ANY `Sl` (closedness of `M₂` is now proved, `isClosed_relative_removal_EFC`);
* `eventually_fdc04_M1_C14Z_EFC` — FDC04's four-piece cover with the actual `Z`.

Parameter premises: `εr < 1/2` (ZSP02) and LC30's tolerance `e ≤ 1/1000` (ZSP02's verbatim (ZB)
radius `.38`; the unconditional radius is `.381 − e`, and FDC01's zero step alone needs only
`e < 1/40`: `Gaf02ChainE.fdc01_not_zero_of_mem_M1_EFC`). `e` is requestable (`C14Requests.e_le`).

STILL a hypothesis: `hS` (slim exclusion), i.e. `M₂ ∩ int_{M₁} M^slim = ∅` needs the actual
`M^slim = M₁ ∩ f₃⁻¹(K₃)` with (SK) — ZSP04's `K₃` (lane C14-ZSP35c), not yet delivered.
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

/-- **FDC01 with the actual zero domains** (LC20's tail, LC02's window): for `q ∈ U_i`,
`|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, `q ∉ int ⋃_k Z_k` (ZSP02's actual domains) and outside every
selected slim region: `p_i` is a nonslim one-stratum point and a selected `k ∈ J_e(i)` satisfies
(Repl) with `π₂E(q) ∈ W₂ ∩ {v_k > .9R_k, |u_k| < 4Δ v_k} ⊆ B₂`. -/
theorem eventually_fdc01_M1_C14Z_EFC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
        ∀ (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ)
          (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw),
        ∀ j ∈ P.edge.centres, ∀ q : Y i, q ∈ ball j (100 * Δ * ρY j) →
          |P.edge.coord j q| ≤ 401 / 100 * Δ → P.edge.smoothing q / ρY q ≤ 401 / 100 * Δ →
          q ∈ (interior (⋃ k : P.zero.finite_centres.toFinset,
            zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ →
          (∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
            10 * Δ ≤ |(P.slim.centre k hk).coord q|) →
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
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc01_C14Z_FDC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y mY _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw Ĉ j hj q hq hηq htq hM₁ hS
  exact hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ j hj q hq hηq htq
    (Ĉ.zero_far_verbatim_of_mem_M1_EFC hεr he hM₁) hS

/-- **FDC02 with the actual zero domains** (LC20's tail): with `Z = ⋃_k Z_k` (ZSP02),
`M₁ = M \ int Z` and `M₂ = M₁ \ int_{M₁} Sl` for any slim set `Sl` whose regions `M₂` avoids,
`M₂ ∩ X₂` equals the witnessed piece, is compact, and has compact base `C₂ = π₂E(M₂ ∩ X₂)`. -/
theorem eventually_fdc02_M1_C14Z_EFC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
        ∀ (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ)
          (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
          (Z Sl M₁ M₂ : Set (Y i)),
          Z = ⋃ k : P.zero.finite_centres.toFinset,
            zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E →
          M₁ = (interior Z)ᶜ → M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' Sl : Set M₁) →
          (∀ q ∈ M₂, ∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
            10 * Δ ≤ |(P.slim.centre k hk).coord q|) →
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
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc02_actual_C14Z_FDC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw Ĉ Z Sl M₁ M₂ hZ hM₁ hM₂ hS
  have hM := Ĉ.relative_removal_zero_far_EFC hεr he hZ hM₁ hM₂
  exact hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ M₂ hM.1 hM.2 hS

/-- **FDC04's four-piece cover with the actual zero domains** (point-set level): with
`Z = ⋃_k Z_k` (ZSP02), `Sl` with ZSP05's point-set hypotheses, `M₁ = M \ int Z`,
`M₂ = M₁ \ int_{M₁} Sl` avoiding the slim regions, the compact edge piece `M^edge` and
`M₃ = M₂ \ int_{M₂} M^edge`: the four pieces cover the carrier, `M₂ = M^edge ∪ M₃`, and the four
ambient interiors are pairwise disjoint. -/
theorem eventually_fdc04_M1_C14Z_EFC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
        ∀ (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ)
          (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
          (Z Sl M₁ M₂ A M₃ : Set (Y i)),
          Z = ⋃ k : P.zero.finite_centres.toFinset,
            zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E → M₁ = (interior Z)ᶜ →
          M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' Sl : Set M₁) →
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
          Sl ⊆ (interior Z)ᶜ → closure (interior Sl) = Sl →
          Sl ∩ frontier (interior Z)ᶜ ⊆
            Subtype.val '' interior (Subtype.val ⁻¹' Sl : Set ↥(interior Z)ᶜ) →
          (∀ q ∈ M₂, ∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
            10 * Δ ≤ |(P.slim.centre k hk).coord q|) →
          IsCompact A ∧ IsCompact M₃ ∧ M₂ = A ∪ M₃ ∧
            A ∩ M₃ = A \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) ∧
            Z ∪ Sl ∪ A ∪ M₃ = univ ∧
            Disjoint (interior Z) (interior Sl) ∧ Disjoint (interior Z) (interior A) ∧
            Disjoint (interior Z) (interior M₃) ∧ Disjoint (interior Sl) (interior A) ∧
            Disjoint (interior Sl) (interior M₃) ∧ Disjoint (interior A) (interior M₃) := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc04_cover_C14Z_FDC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ hεr he P Kj Ξ Γ S eg c cw Ĉ Z Sl M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃
    hSM hreg hcollar hS
  exact hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ Z Sl M₁ M₂ A M₃ hM₁ hM₂ hA hM₃ hSM hreg
    hcollar (Ĉ.relative_removal_zero_far_EFC hεr he hZ hM₁ hM₂).2 hS

end DifferentialGeometry.Geometry.Collapse
