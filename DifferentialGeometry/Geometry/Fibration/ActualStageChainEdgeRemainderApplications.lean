import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRemainder

/-!
# Consumer: FDC03's coverage and fibre constancy for an enhanced chain on the final closed family

Blueprint `master207B.tex`, FDC03 (B:7322–7346), for `Ĉ : Gaf02ChainE` on the final closed family
`LocalChartPacketsC14Z` (projection `P.toLocalChartPacketsC14D.toLocalChartPacketsC14`;
`Gaf02ChainEJA` projects to it), with the edge candidate
`X₂° = {T < 4Δ} ∩ {x | ∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}` (EDP02's `X₂`, `W₂` dropped).

* `fdc03_remainder_C14Z_FDC`: `X₂°` is open; every point outside it (in particular every point of
  the relative remainder `M₃`) is zero-stratum, in a selected circle ball `B(j, 2ρ_j)` or in a
  selected slim ball `B(j, 2Δρ_j)`; and `X₂°`-membership is constant on the fibres of `E`
  (the input of `EdgeDisk.relativeRemoval_saturated`).
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

/-- **FDC03 on the final closed family** (`W₂` dropped): the edge candidate `X₂°` of an enhanced
chain is open, its complement is covered by the zero stratum, the selected circle balls
`B(j, 2ρ_j)` and the selected slim balls `B(j, 2Δρ_j)`, and `X₂°` is a union of `E`-fibres. -/
theorem fdc03_remainder_C14Z_FDC {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hσc : σc ≤ 1 / 2) :
    IsOpen ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1}) ∧
    (∀ x ∉ ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1}),
      x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0 ∨
        (∃ j ∈ P.circle.centres, x ∈ ball j (2 * ρ j)) ∨
        (∃ j ∈ P.slim.centres, x ∈ ball j (2 * (Δ * ρ j)))) ∧
    ∀ p p', Ĉ.toChain.E p = Ĉ.toChain.E p' →
      (p ∈ {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1} ↔
      p' ∈ {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1}) := by
  refine ⟨Ĉ.isOpen_edgeCandidate_FDC, fun x hx => ?_, fun p p' h => ?_⟩
  · rcases Ĉ.fdc03_coverage_FDC hσc x with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd (interior_subset h) hx
  · obtain ⟨-, hT, -, hk⟩ := Ĉ.toChain.fibre_constancy_FDC h
    simp only [mem_inter_iff, mem_ofPred_eq]
    rw [hT, hk]

end DifferentialGeometry.Geometry.Collapse
