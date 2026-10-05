import DifferentialGeometry.Geometry.Fibration.ActualStageChainRemainderCircle

/-!
# Consumer: FDC03's `M₃ ⊆ X₁` for the actual pieces on the final closed family

`fdc03_remainder_subset_X₁_C14Z_EFC`: on `P : LocalChartPacketsC14Z` with an enhanced chain with
(JA), for ZSP04's `K₃` (with (SK)) and the actual `Z`, `M₁ = M ∖ int Z`, `M₂ = M₁ ∖ int_{M₁}
M^slim`, `A = M₂ ∩ V ∩ {∃ k, v_k(E) = R_k, |u_k(E)| < 4ΔR_k}` (FDC04's edge piece) and `M₃ = M₂ ∖
int_{M₂} A`: `M₃ ⊆ X₁ = (π₁E)⁻¹(W₁ ∩ R₁)` (FDC03, B:7285–7335). Premises: `εr < 1/2` (ZSP02 /
ZSP04), `σc ≤ 1/2` (FDC03's coverage), `0 ≤ γ ≤ 3/4` (circle balls).
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **FDC03's first clause for the ACTUAL pieces**: `M₃ ⊆ X₁`. -/
theorem fdc03_remainder_subset_X₁_C14Z_EFC {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF Ĉ.slimBs_ZSP35,
      Ĉ.toChain.slimSlabImage_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35) ∧
      ∀ (Z M₁ M₂ A M₃ : Set X),
        Z = ⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E → M₁ = (interior Z)ᶜ →
        M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' Ĉ.slimPiece_ZSP35 K₃.carrier :
          Set M₁) →
        A = M₂ ∩ ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪
          {p | 0 < Ĉ.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
            P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
              (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∩
          {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
            blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) =
              ρ k.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
              4 * Δ * ρ k.1} →
        M₃ = M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) →
        M₃ ⊆ {x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E x) ∈
          Ĉ.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets} := by
  obtain ⟨K₃, hKs, -, -, -, hSeq, -⟩ := Ĉ.zsp04_row_ZSP35 hεr
  refine ⟨K₃, fun w hw => hKs (Or.inl hw), fun Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ => ?_⟩
  have hM₂₁ : M₂ ⊆ (interior Ĉ.zeroUnion_ZSP35)ᶜ := by
    intro x hx
    rw [hM₂, hM₁, hZ] at hx
    exact hx.1
  have hzero : ∀ x ∈ M₂, x ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0 :=
    fun x hx => Ĉ.toGaf02ChainE.not_zero_of_mem_M1_EFC hεr (hM₂₁ hx)
  have hS : ∀ x ∈ M₂, ∀ k (hk : k ∈ P.slim.centres), dist x k < 9 * Δ * ρ k →
      10 * Δ ≤ |(P.slim.centre k hk).coord x| := by
    subst hZ hM₁ hM₂
    exact fun q hq k hk hd => Ĉ.toGaf02ChainE.slim_far_of_relint_EFC
      (fun w hw => hKs (Or.inl hw)) (M₁ := (interior Ĉ.zeroUnion_ZSP35)ᶜ)
      (fun p hp hpK => by rw [hSeq]; exact ⟨hp, hpK⟩) hq hk hd
  have hAx : M₂ ∩ ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
        P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero (Ĉ.toChain.E x)) /
        Ĉ.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
          4 * Δ * ρ k.1}) ⊆ A := by
    rintro x ⟨hxM, hxT, hxk⟩
    rw [hA]
    exact ⟨⟨hxM, Or.inr ⟨(Ĉ.toChain.scale_pos x).2, le_of_lt hxT⟩⟩, hxk⟩
  rw [hM₃]
  exact Ĉ.remainder_subset_X₁_EFC hσc hγ hγ1 hzero hS hAx

end DifferentialGeometry.Geometry.Collapse
