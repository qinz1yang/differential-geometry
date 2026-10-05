import DifferentialGeometry.Geometry.Fibration.ActualStageChainReplacement
import DifferentialGeometry.Geometry.Fibration.ActualReplacementCentreDecisionApplications

/-!
# Consumer: FDC01's replacement contract for a chain on the final closed family

Blueprint `master207B.tex`, FDC01 (B:7157–7243); draft 61 §6.2, steps one to four of (Repl∂)
in the closed form, with NO hypothesis `q ∈ X₂` or `π₂E(q) ∈ B₂`.

* `eventually_fdc01_chain_replacement_C14Z_FDC` (LC20's tail, LC02's window): for every family
  `LocalChartPacketsC14Z` on that scale, every chain `C` on it, every edge index `i` and every
  `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, outside every selected zero ball
  `B(z, .38R_z)` and every selected slim region `{d(q, k) < 9Δρ(k), |η_k(q)| < 10Δ}` (the
  original-coordinate consequences of `q ∈ M₂`): a selected edge index `j ∈ J_e(i)` has
  `|η_j(q)| < 2Δ`, `ζ_j(q) = 1`, `|v_j(E q) − R_j| < (5/4)c₃R_j`, `|u_j(E q)| < 3ΔR_j` and
  `|u_j(E q)| < 4Δ v_j(E q)` (the values at `π₂E q`). Composes
  `eventually_fdc01_efree_C14Z_FDC` (centre decision on the tail),
  `Gaf02Chain.edge_block_window_FDC` and `fdc01_window_numbers_FDC`.
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

/-- **FDC01's replacement contract for a chain on the final closed family** (LC20's tail, LC02's
window): for `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, outside every selected zero ball
`B(z, .38R_z)` and every selected slim region, and every chain `C` on the family, a selected edge
index `j ∈ J_e(i)` has `|η_j(q)| < 2Δ`, `ζ_j(q) = 1`, `|v_j(E q) − R_j| < (5/4)c₃R_j`,
`|u_j(E q)| < 3ΔR_j` and `|u_j(E q)| < 4Δ v_j(E q)`. -/
theorem eventually_fdc01_chain_replacement_C14Z_FDC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
          (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw),
        ∀ j ∈ P.edge.centres, ∀ q : Y i, q ∈ ball j (100 * Δ * ρY j) →
          |P.edge.coord j q| ≤ 401 / 100 * Δ → P.edge.smoothing q / ρY q ≤ 401 / 100 * Δ →
          (∀ z (hz : z ∈ P.zero.centres), 38 / 100 * (P.zero.zero z hz).radius ≤ dist q z) →
          (∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
            10 * Δ ≤ |(P.slim.centre k hk).coord q|) →
          ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
            k.1 ∈ egpEdgeList P.toLocalChartFamily j ∧
            |P.edge.coord k.1 q| < 2 * Δ ∧ P.edge.cutoff k.1 q = 1 ∧
            |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.E q) - ρY k.1| <
              5 / 4 * c 2 * ρY k.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.E q)‖ <
              3 * Δ * ρY k.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.E q)‖ <
              4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.E q) := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc01_efree_C14Z_FDC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw C j hj q hq hηq htq hZ hS
  obtain ⟨hΛ, -, -, -, hLΛ, -, -, hT, hσs, hσs1, -⟩ := C.std
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc2, -⟩ := C.numbers
  have hT' : 1000 * Δ ≤ T := by nlinarith
  have h1 := hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3
    hβ2 hb hbη hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hT' hσs hσs1 P j hj q hq hηq htq hZ hS
  obtain ⟨-, -, k, hk, hlist, hqk, hηk, hζ⟩ := h1
  let kk : P.toLocalChartPackets.edge.finite_centres.toFinset :=
    ⟨k, (Set.Finite.mem_toFinset _).mpr hk⟩
  obtain ⟨hmk, hvec⟩ := C.edge_block_window_FDC kk hζ hqk
  obtain ⟨-, h3, h4⟩ := fdc01_window_numbers_FDC hΔ (hρY k) hc2 hηk hmk hvec
  exact ⟨kk, hlist, hηk, hζ, hmk, h3, h4⟩

end DifferentialGeometry.Geometry.Collapse
