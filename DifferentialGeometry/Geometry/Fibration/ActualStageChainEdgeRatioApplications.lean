import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRatio
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseApplications

/-!
# Consumer: FDC02 — `M₂ ∩ X₂` is compact, on the final closed family

Blueprint `master207B.tex`, FDC02 (B:7246–7283): "The set `M^edge = M₂ ∩ X₂` is compact. … Its
continuous image `C₂` is compact." For an enhanced chain `Ĉ : Gaf02ChainE` on the final closed
family `LocalChartPacketsC14Z` (projection `P.toLocalChartPacketsC14D.toLocalChartPacketsC14`;
`Gaf02ChainEJA` projects to it), with BASES' `W₂ = Ĉ.toChain.finalBase_BAS 1`, EDP02's (ED)
`X₂ = (π₂E)⁻¹(B₂) ∩ V`, `B₂ = ⋃_i {w ∈ W₂ : v_i(w) > .9R_i, |u_i(w)| < 4Δ v_i(w)}` written out.

* `eventually_fdc02_actual_C14Z_FDC` (LC20's tail): for every closed `M₂` outside the selected
  `.38`-zero balls and slim regions (the original-coordinate consequences of the actual `M₂`,
  ZSP02 / GAF07), `M₂ ∩ X₂` is EQUAL to the witnessed piece
  `S = M₂ ∩ V ∩ {x | ∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}`, it is compact, and its base
  `C₂ = π₂E(M₂ ∩ X₂)` is compact. `⊆`: (ELoc) for every ratio preimage
  (`Gaf02Chain.edgePiece_eq_witnessed_FDC`) and FDC01 with the exact marker
  (`eventually_fdc01_exact_C14Z_FDC`); compactness: `eventually_fdc02_C14Z_FDC`.

NOT here: the actual `M₂` (ZSP02, GAF07), `C₂`'s smooth one-manifold structure and the disk bundle
(EDP04–EDP05, FC34).
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

/-- **FDC02 on the final closed family** (LC20's tail): for an enhanced chain `Ĉ` and every closed
`M₂` outside the selected `.38`-zero balls and slim regions, `M₂ ∩ X₂` equals the witnessed piece
`M₂ ∩ V ∩ {x | ∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}`, is compact, and has compact base
`π₂E(M₂ ∩ X₂)`. -/
theorem eventually_fdc02_actual_C14Z_FDC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
  obtain ⟨Lc, η₀, hLc, hη₀, w₁, hw₁, ht1⟩ := eventually_fdc01_exact_C14Z_FDC hΔ hβ₂ hβ₂1 hΛ₀
  obtain ⟨Lc', η₀', hLc', hη₀', w₂, hw₂, ht2⟩ := eventually_fdc02_C14Z_FDC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨max Lc Lc', min η₀ η₀', lt_max_of_lt_left hLc, lt_min hη₀ hη₀', min w₁ w₂,
    lt_min hw₁ hw₂, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [ht1 w hw (lt_of_lt_of_le hww (min_le_left _ _)) hwc Y gY hmY α hα hstand,
    ht2 w hw (lt_of_lt_of_le hww (min_le_right _ _)) hwc Y gY hmY α hα hstand] with n hn1 hn2
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ M₂ hM₂ hZ hS
  have hbη1 : b ≤ η₀ := le_trans hbη (min_le_left _ _)
  have hbη2 : b ≤ η₀' := le_trans hbη (min_le_right _ _)
  have hβ11 : βY 1 ≤ η₀ := le_trans hβ1 (min_le_left _ _)
  have hβ12 : βY 1 ≤ η₀' := le_trans hβ1 (min_le_right _ _)
  have hL1 : Lc ≤ Lmax := le_trans (le_max_left _ _) hLmax
  have hL2 : Lc' ≤ Lmax := le_trans (le_max_right _ _) hLmax
  have h2 := hn2 ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3
    hβ2 hb hbη2 hs hβ12 hL2 hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ M₂ hM₂ hZ hS
  refine ⟨Ĉ.toChain.edgePiece_eq_witnessed_FDC (by linarith) M₂
    (fun x hxM hxV i hxi hηx htx => ?_), h2.1, h2.2.2⟩
  have hrep := hn1 ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM
    hβ3 hβ2 hb hbη1 hs hβ11 hL1 hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ i.1
    ((Set.Finite.mem_toFinset _).mp i.2) x hxi hηx htx (hZ x hxM) (hS x hxM)
  obtain ⟨k, -, -, -, hvk, h3, -⟩ := hrep
  have hrk := hρY k.1
  have h34 : 3 * Δ * ρY k.1 ≤ 4 * Δ * ρY k.1 :=
    mul_le_mul_of_nonneg_right (by linarith) hrk.le
  exact ⟨k, hvk, lt_of_lt_of_le h3 h34⟩

end DifferentialGeometry.Geometry.Collapse
