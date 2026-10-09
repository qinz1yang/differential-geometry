import DifferentialGeometry.Topology.Maps.RelativeInteriorRemovalEdge
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRatioApplications

/-!
# Consumer: FDC04's four-piece cover of the closed carrier, point-set level, on the final family

Blueprint `master207B.tex`, FDC04 (B:7367–7383): "The domains `Z, M^slim, M^edge, M^{2-stratum}` …
cover the carrier, and have disjoint ambient interiors. … Combine (RF) and (LastFaces) for the union
and every complement identity." with FDC02's compact edge piece and FDC03's (Last).

* `eventually_fdc04_cover_C14Z_FDC` (LC20's tail, `LocalChartPacketsC14Z`, `Ĉ : Gaf02ChainE`): for
  zero / slim pieces `Z`, `Sl` satisfying ZSP05's point-set hypotheses (`Sl ⊆ M \ int Z` regular
  closed with its relative collar), `M₁ = M \ int Z`, `M₂ = M₁ \ int_{M₁} Sl` outside the selected
  `.38`-zero balls and slim regions, the edge piece `M^edge = M₂ ∩ V ∩ {∃ k, v_k(E) = R_k,
  |u_k(E)| < 4ΔR_k}` (`= M₂ ∩ X₂`, `eventually_fdc02_actual_C14Z_FDC`) and
  `M₃ = M₂ \ int_{M₂} M^edge`: `M^edge` and `M₃` are compact, `M₂ = M^edge ∪ M₃`,
  `M^edge ∩ M₃` is the relative frontier, `Z ∪ Sl ∪ M^edge ∪ M₃ = M`, and the four ambient
  interiors are pairwise disjoint.

NOT here: the actual `Z`, `M^slim` (ZSP02, ZSP04) and their ZSP05 hypotheses; smooth structures,
faces and the FC39 fields (FDC02–FDC03 remaining clauses, FC40–FC42).
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

/-- **FDC04's four-piece cover on the final closed family** (point-set level): `Z`, `Sl`, the
compact edge piece `M^edge` and the compact remainder `M₃ = M₂ \ int_{M₂} M^edge` cover the
carrier, `M₂ = M^edge ∪ M₃`, and the four ambient interiors are pairwise disjoint. -/
theorem eventually_fdc04_cover_C14Z_FDC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ)
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
          (Z Sl M₁ M₂ A M₃ : Set (Y i)), M₁ = (interior Z)ᶜ →
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
          (∀ q ∈ M₂, ∀ z (hz : z ∈ P.zero.centres), 38 / 100 * (P.zero.zero z hz).radius ≤
            dist q z) →
          (∀ q ∈ M₂, ∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
            10 * Δ ≤ |(P.slim.centre k hk).coord q|) →
          IsCompact A ∧ IsCompact M₃ ∧ M₂ = A ∪ M₃ ∧
            A ∩ M₃ = A \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) ∧
            Z ∪ Sl ∪ A ∪ M₃ = univ ∧
            Disjoint (interior Z) (interior Sl) ∧ Disjoint (interior Z) (interior A) ∧
            Disjoint (interior Z) (interior M₃) ∧ Disjoint (interior Sl) (interior A) ∧
            Disjoint (interior Sl) (interior M₃) ∧ Disjoint (interior A) (interior M₃) := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, htail⟩ := eventually_fdc02_actual_C14Z_FDC hΔ hβ₂ hβ₂1 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with n hn
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ Z Sl M₁ M₂ A M₃ hM₁ hM₂ hA hM₃ hSM hreg
    hcollar hZ hS
  have hM₂c : IsClosed M₂ := by
    have h := (DifferentialGeometry.Topology.relative_interior_removal Z Sl hSM hreg hcollar).1
    rw [hM₂, hM₁]
    exact h
  have hK := (hn ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3
    hβ2 hb hbη hs hβ1 hLmax hμ hτ hσc hμΔ P Kj Ξ Γ S eg c cw Ĉ M₂ hM₂c hZ hS).2.1
  have hAM : A ⊆ M₂ := by
    rw [hA]
    exact fun x hx => hx.1.1
  have hcov := DifferentialGeometry.Topology.relative_removal_third_FDC Z Sl A M₁ M₂ M₃ hM₁ hM₂
    hM₃ hSM hreg hcollar hAM
  rw [← hA] at hK
  exact ⟨hK, hcov.1.isCompact, hcov.2⟩

end DifferentialGeometry.Geometry.Collapse
