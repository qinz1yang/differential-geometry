import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeLimit
import DifferentialGeometry.Geometry.Fibration.ActualStageChainReplacementApplications

/-!
# Consumer: FDC02's limit step followed by FDC01's replacement, on the final closed family

Blueprint `master207B.tex`, FDC02 (B:7259–7277): "Let `q_n ∈ M₂ ∩ X₂` converge to `q`. … After a
subsequence, one selected index `i` witnesses the base condition for every `q_n`. … FDC01 now gives
a replacement index with STRICT base inequalities."

* `eventually_fdc02_limit_replacement_C14Z_FDC` (LC20's tail, LC02's window): for every family
  `LocalChartPacketsC14Z` on that scale and every chain `C` on it, a sequence `q_n → q` with
  witnessing edge indices `w_n` (`v_{w_n}(E q_n) = R_{w_n}`, `|u_{w_n}(E q_n)| < 4ΔR_{w_n}`,
  `q_n ∈ V`), whose limit lies outside every selected zero ball `B(z, .38R_z)` and every selected
  slim region (the original-coordinate consequences of `q ∈ M₂`, `M₂` closed), has an edge index
  `j` with `v_j(E q) = R_j`, `|u_j(E q)| ≤ 4ΔR_j`, `q ∈ V`, and a replacement index `k ∈ J_e(j)`
  with `|η_k(q)| < 2Δ`, `ζ_k(q) = 1`, `|v_k(E q) − R_k| < (5/4)c₃R_k`, `|u_k(E q)| < 3ΔR_k` and
  `|u_k(E q)| < 4Δ v_k(E q)` (the values at `π₂E q`). Composes `Gaf02Chain.fdc02_limit_witness_FDC`
  (no (JA)) with `eventually_fdc01_chain_replacement_C14Z_FDC`.

NOT here: `π₂E(q) ∈ W₂ ∩ B₂` (exact replacement marker; BASES), hence `q ∈ X₂`.
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

/-- **FDC02's limit step with FDC01's replacement on the final closed family** (LC20's tail,
LC02's window): a sequence `q_n → q` with witnessing edge indices (exact final marker, strict
vector bound, `q_n ∈ V`), whose limit lies outside the selected `.38`-zero balls and slim regions,
has a limit witness `j` (`v_j(E q) = R_j`, `|u_j(E q)| ≤ 4ΔR_j`, `q ∈ V`) and a replacement index
`k ∈ J_e(j)` with the STRICT chain clauses of FDC01. -/
theorem eventually_fdc02_limit_replacement_C14Z_FDC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
        ∀ (qs : ℕ → Y i) (q : Y i), Tendsto qs atTop (𝓝 q) →
        ∀ wt : ℕ → P.toLocalChartPackets.edge.finite_centres.toFinset,
          (∀ n, blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl (wt n)))) (C.E (qs n)) =
            ρY (wt n).1) →
          (∀ n, ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl (wt n)))) (C.E (qs n))‖ <
            4 * Δ * ρY (wt n).1) →
          (∀ n, qs n ∈ {p | P.edge.smoothing p / ρY p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
            EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
              P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero (C.E p)) /
                C.scale p ≤ 4 * Δ}) →
          (∀ z (hz : z ∈ P.zero.centres), 38 / 100 * (P.zero.zero z hz).radius ≤ dist q z) →
          (∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
            10 * Δ ≤ |(P.slim.centre k hk).coord q|) →
          ∃ j : P.toLocalChartPackets.edge.finite_centres.toFinset,
            blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl j))) (C.E q) = ρY j.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl j))) (C.E q)‖ ≤
              4 * Δ * ρY j.1 ∧
            q ∈ {p | P.edge.smoothing p / ρY p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
              EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
                P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero (C.E p)) /
                  C.scale p ≤ 4 * Δ} ∧
            ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
              k.1 ∈ egpEdgeList P.toLocalChartFamily j.1 ∧
              |P.edge.coord k.1 q| < 2 * Δ ∧ P.edge.cutoff k.1 q = 1 ∧
              |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.E q) - ρY k.1| <
                5 / 4 * c 2 * ρY k.1 ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.E q)‖ <
                3 * Δ * ρY k.1 ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                  P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.E q)‖ <
                4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
                  P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
                  (.inr (.inr (.inl k))) (C.E q) := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc01_chain_replacement_C14Z_FDC hΔ hβ₂
    hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw C qs q hq wt hv hu hV hZ hS
  obtain ⟨j, hvj, huj, hVq, hball, hη, ht, -⟩ := C.fdc02_limit_witness_FDC hq wt hv hu hV
  obtain ⟨k, hk⟩ := hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM
    hβ3 hβ2 hb hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw C j.1
    ((Set.Finite.mem_toFinset _).mp j.2) q hball hη.le ht.le hZ hS
  exact ⟨j, hvj, huj, hVq, k, hk⟩

end DifferentialGeometry.Geometry.Collapse
