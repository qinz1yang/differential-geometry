import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBase
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEReplacementApplications

/-!
# Consumers: FDC01 in full and FDC02's compact witnessed edge piece inside `M₂ ∩ X₂`

Blueprint `master207B.tex`, FDC01 (B:7157–7243) and FDC02 (B:7246–7283), for an enhanced chain
`Ĉ : Gaf02ChainE` on the final closed family `LocalChartPacketsC14Z` (projection
`P.toLocalChartPacketsC14D.toLocalChartPacketsC14`; `Gaf02ChainEJA` projects to it), with
`W₂ = Ĉ.toChain.finalBase_BAS 1` (BASES) and `B₂`, `X₂` of EDP02's (ED) written out.

* `eventually_fdc01_C14Z_FDC` (LC20's tail, LC02's window) — FDC01: for `q ∈ U_i`,
  `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, outside every selected `.38`-zero ball and slim region (the
  original-coordinate consequences of `q ∈ M₂`, ZSP02 / GAF07), `p_i` is a nonslim one-stratum
  point and a selected `k ∈ J_e(i)` has `|η_k(q)| < 2Δ`, `ζ_k(q) = 1`, `v_k(π₂E q) = R_k`,
  `|u_k(π₂E q)|/R_k < 3Δ` (Repl), and `π₂E(q) ∈ W₂` with `v_k(π₂E q) > .9R_k`,
  `|u_k(π₂E q)| < 4Δ v_k(π₂E q)` (so `π₂E(q) ∈ B₂`). No hypothesis `q ∈ X₂`, `π₂E(q) ∈ B₂`.
* `eventually_fdc02_C14Z_FDC` — FDC02: for every closed `M₂` outside those balls and regions, the
  witnessed edge piece `S = M₂ ∩ V ∩ {x | ∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}` is compact, lies
  in `M₂ ∩ X₂` (`X₂ = (π₂E)⁻¹(B₂) ∩ V`), and its base `π₂E(S)` is compact.

NOT here: `M₂ ∩ X₂ ⊆ S`, i.e. the exact marker `v_i = R_i` on every `B₂`-patch (EDP02's "each
indicated patch has `v_i = R_i`" = GAF05's patch clause on `W₂`, lanes C14-GAF47 / BASES); the
actual `M₂` (ZSP02, GAF07); `C₂`'s smooth structure (EDP05, FC34).
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

/-- **FDC01 on the final closed family** (LC20's tail, LC02's window): for an enhanced chain `Ĉ`,
`q ∈ U_i`, `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, outside the selected `.38`-zero balls and slim
regions: `p_i` is a nonslim one-stratum point, and a selected `k ∈ J_e(i)` satisfies (Repl)
(`|η_k(q)| < 2Δ`, `ζ_k(q) = 1`, `v_k(π₂E q) = R_k`, `|u_k(π₂E q)|/R_k < 3Δ`) and
`π₂E(q) ∈ W₂ ∩ {v_k > .9R_k, |u_k| < 4Δ v_k} ⊆ B₂`. -/
theorem eventually_fdc01_C14Z_FDC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
        ∀ P : LocalChartPacketsC14Z (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz oM,
        ∀ (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ)
          (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw),
        ∀ j ∈ P.edge.centres, ∀ q : Y i, q ∈ ball j (100 * Δ * ρY j) →
          |P.edge.coord j q| ≤ 401 / 100 * Δ → P.edge.smoothing q / ρY q ≤ 401 / 100 * Δ →
          (∀ z (hz : z ∈ P.zero.centres), 38 / 100 * (P.zero.zero z hz).radius ≤ dist q z) →
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
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc01_efree_C14Z_FDC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y mY _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ j hj q hq hηq htq hZ hS
  have hstd := Ĉ.toChain.std
  have hΛ : 0 ≤ Λ := hstd.1
  have hLΛ : 1000000 * Δ * Λ < 1 / 100000 := hstd.2.2.2.2.1
  have hT : 1600 * (1000000 * Δ) ≤ T := hstd.2.2.2.2.2.2.2.1
  have hσs : 0 ≤ σs := hstd.2.2.2.2.2.2.2.2.1
  have hσs1 : σs ≤ 1 / 100 := hstd.2.2.2.2.2.2.2.2.2.1
  have hT' : 1000 * Δ ≤ T := by linarith
  have H := hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb hbη hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hT' hσs hσs1
    P j hj q hq hηq htq hZ hS
  refine ⟨H.1, H.2.1, ?_⟩
  have H2 := H.2.2
  clear H hn hstand hwin
  obtain ⟨k, hk, hlist, hqk, hηk, hζ⟩ := H2
  obtain ⟨kk, rfl⟩ : ∃ kk : P.toLocalChartPackets.edge.finite_centres.toFinset, kk.1 = k :=
    ⟨⟨k, (Set.Finite.mem_toFinset _).mpr hk⟩, rfl⟩
  exact ⟨kk, hlist, hηk, hζ, Ĉ.fdc01_base_clauses_FDC hΔ kk hζ hqk hηk htq⟩

/-- **FDC02 on the final closed family** (LC20's tail): for an enhanced chain `Ĉ` and every
closed `M₂` outside the selected `.38`-zero balls and slim regions, the witnessed edge piece
`S = M₂ ∩ V ∩ {x | ∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}` is compact, every point of it is in
`M₂ ∩ X₂` (`π₂E(x) ∈ W₂`, `v_k(π₂E x) > .9R_k`, `|u_k(π₂E x)| < 4Δ v_k(π₂E x)`, `x ∈ V`), and its
base `π₂E(S)` is compact. -/
theorem eventually_fdc02_C14Z_FDC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
                4 * Δ * ρY k.1}) ∧
          (∀ x ∈ M₂ ∩ ({p | P.edge.smoothing p / ρY p ≤ 7 / 20 * Δ} ∪
            {p | 0 < Ĉ.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
              P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∩
            {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
              blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) =
                ρY k.1 ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
                4 * Δ * ρY k.1},
            (gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                1).starProjection (Ĉ.toChain.E x) ∈ Ĉ.toChain.finalBase_BAS 1 ∧
            ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
              9 / 10 * ρY k.1 < blockMarkerCLM (V := fun _ : CGPTag
                  P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
                  (.inr (.inr (.inl k)))
                  ((gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                    1).starProjection (Ĉ.toChain.E x)) ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
                  ((gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                    1).starProjection (Ĉ.toChain.E x))‖ <
                4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
                  P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
                  (.inr (.inr (.inl k)))
                  ((gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
                    1).starProjection (Ĉ.toChain.E x))) ∧
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
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc02_compact_C14Z_FDC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ M₂ hM₂ hZ hS
  have hK := hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2
    hb hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ M₂ hM₂ hZ hS
  have hcont : Continuous fun x => (gafStageQ P.toLocalChartPackets.toLocalChartFamily
      P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x) :=
    (gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
      1).starProjection.continuous.comp Ĉ.toChain.stage_smooth.2.2.continuous
  refine ⟨hK, fun x hx => ?_, hK.image hcont⟩
  obtain ⟨⟨-, hxV⟩, k, hv, hu⟩ := hx
  obtain ⟨hW, h9, h4⟩ := Ĉ.toChain.stageTwo_mem_base_FDC k hv hu hxV
  exact ⟨hW, k, h9, h4⟩

end DifferentialGeometry.Geometry.Collapse
