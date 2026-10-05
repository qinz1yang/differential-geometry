import DifferentialGeometry.Geometry.Fibration.ActualStageChainEReplacement
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeLimit
import DifferentialGeometry.Geometry.Fibration.ActualStageChainReplacementApplications

/-!
# Consumers: FDC01 with the EXACT marker, and FDC02's compactness, on the final closed family

Blueprint `master207B.tex`, FDC01 (B:7157–7243) and FDC02 (B:7246–7283), for an enhanced chain
`Ĉ : Gaf02ChainE` on the final closed family `LocalChartPacketsC14Z` (projection
`P.toLocalChartPacketsC14D.toLocalChartPacketsC14`; `Gaf02ChainEJA` projects to it).

* `eventually_fdc01_exact_C14Z_FDC` (LC20's tail, LC02's window): for `q ∈ U_i` with
  `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, outside every selected `.38`-zero ball and slim region (the
  original-coordinate consequences of `q ∈ M₂`), a selected edge index `k ∈ J_e(i)` has
  `|η_k(q)| < 2Δ`, `ζ_k(q) = 1`, the EXACT marker `v_k(E q) = R_k`, `|u_k(E q)| < 3ΔR_k` and
  `|u_k(E q)| < 4Δ v_k(E q)`, and (Repl) at `π₂E q` (`v_k(π₂E q) = R_k`, `|u_k(π₂E q)|/R_k < 3Δ`,
  by `stageQ_edge_repl_FDC`). This is (Repl) except `π₂E(q) ∈ W₂`.
* `eventually_fdc02_compact_C14Z_FDC`: for every closed `M₂` whose points satisfy those original
  exclusions, the set `M₂ ∩ V ∩ {x | ∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}` (EDP02's description
  of `M₂ ∩ X₂` with `W₂` dropped: `π_{Q₂}` keeps the edge blocks) is COMPACT. Composes
  `Gaf02Chain.fdc02_isCompact_FDC` (limit step, no (JA)) with the exact replacement above.

NOT here: `π₂E(x) ∈ W₂` (BASES), the actual `M₂` (ZSP02, GAF07), `C₂`'s smooth structure (EDP05).
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

/-- **FDC01 with the EXACT replacement marker on the final closed family** (LC20's tail, LC02's
window): for an enhanced chain `Ĉ` on the family, `q ∈ U_i`, `|η_i(q)| ≤ 4.01Δ`,
`t(q) ≤ 4.01Δ`, outside the selected `.38`-zero balls and slim regions, a selected `k ∈ J_e(i)`
has `|η_k(q)| < 2Δ`, `ζ_k(q) = 1`, `v_k(E q) = R_k`, `|u_k(E q)| < 3ΔR_k`,
`|u_k(E q)| < 4Δ v_k(E q)`, and (Repl) on `π₂E q`: `v_k(π₂E q) = R_k`, `|u_k(π₂E q)|/R_k < 3Δ`. -/
theorem eventually_fdc01_exact_C14Z_FDC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
        ∀ P : LocalChartPacketsC14Z (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz oM,
        ∀ (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ)
          (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw),
        ∀ j ∈ P.edge.centres, ∀ q : Y i, q ∈ ball j (100 * Δ * ρY j) →
          |P.edge.coord j q| ≤ 401 / 100 * Δ → P.edge.smoothing q / ρY q ≤ 401 / 100 * Δ →
          (∀ z (hz : z ∈ P.zero.centres), 38 / 100 * (P.zero.zero z hz).radius ≤ dist q z) →
          (∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
            10 * Δ ≤ |(P.slim.centre k hk).coord q|) →
          ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
            k.1 ∈ egpEdgeList P.toLocalChartFamily j ∧
            |P.edge.coord k.1 q| < 2 * Δ ∧ P.edge.cutoff k.1 q = 1 ∧
            blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E q) =
              ρY k.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E q)‖ <
              3 * Δ * ρY k.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E q)‖ <
              4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E q) ∧
            blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
                ((gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                  1).starProjection (Ĉ.toChain.E q)) = ρY k.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
                ((gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                  1).starProjection (Ĉ.toChain.E q))‖ / ρY k.1 < 3 * Δ := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc01_chain_replacement_C14Z_FDC hΔ hβ₂
    hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ j hj q hq hηq htq hZ hS
  obtain ⟨k, hlist, hηk, hζ, -, h3, h4⟩ := hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax
    τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw
    Ĉ.toChain j hj q hq hηq htq hZ hS
  have hv := Ĉ.edge_exact_marker_FDC k (by rw [hζ]; exact one_ne_zero) (by linarith)
    (by linarith)
  obtain ⟨h5, h6⟩ := stageQ_edge_repl_FDC P.toLocalChartPackets k (Ĉ.toChain.E q) hv h3
  exact ⟨k, hlist, hηk, hζ, hv, h3, h4, h5, h6⟩

/-- **FDC02's compactness on the final closed family, modulo `W₂`** (LC20's tail): for an enhanced
chain `Ĉ` and every closed `M₂` outside the selected `.38`-zero balls and slim regions, the set
`M₂ ∩ V ∩ {x | ∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}` is compact. -/
theorem eventually_fdc02_compact_C14Z_FDC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
        ∀ P : LocalChartPacketsC14Z (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz oM,
        ∀ (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ)
          (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
          (M₂ : Set (Y i)), IsClosed M₂ →
          (∀ q ∈ M₂, ∀ z (hz : z ∈ P.zero.centres), 38 / 100 * (P.zero.zero z hz).radius ≤
            dist q z) →
          (∀ q ∈ M₂, ∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
            10 * Δ ≤ |(P.slim.centre k hk).coord q|) →
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
                4 * Δ * ρY k.1}) := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc01_exact_C14Z_FDC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ M₂ hM₂ hZ hS
  refine Ĉ.toChain.fdc02_isCompact_FDC hM₂ inter_subset_left (fun x hx => hx.2)
    (fun x hx i hi hxi hηx htx => ⟨hx, ?_⟩)
  obtain ⟨k, -, -, -, hv, h3, -, -, -⟩ := hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz oM hβ3 hβ2 hb hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ i hi x hxi
    hηx htx (hZ x hx.1) (hS x hx.1)
  have h34 : 3 * Δ * ρY k.1 ≤ 4 * Δ * ρY k.1 := by
    have := hρY k.1
    nlinarith
  exact ⟨k, hv, lt_of_lt_of_le h3 h34⟩

end DifferentialGeometry.Geometry.Collapse
