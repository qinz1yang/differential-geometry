import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38Row

/-!
# Consumer of FC38's row: every point of the actual remainder lies on a WHOLE smooth circle fibre

Lane S-FC-WRAP, group G2 (suffix `_FCW`). From `fc38_row_FCW`: the actual remainder `M₃` lies in
GAF07's circle region `X₁` (conjunct 2), and GAF07's circle row (conjunct 1, item (7)) then puts
every point `x ∈ M₃` on a whole circle fibre of `π₁E`: the image of a smooth embedding of `Circle`
that equals the whole fibre `(π₁E)⁻¹{π₁E x}` and is connected.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.Endpoint

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
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **Consumer of FC38**: for ZSP04's `K₃` and the actual pieces `Z, M₁, M₂, A, M₃` of FDC03, every
point of `M₃` lies on a whole connected circle fibre of `π₁E`, the image of a smooth embedding of
`Circle`. -/
theorem fc38_remainder_fibres_FCW
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      ∀ (Z M₁ M₂ A M₃ : Set X),
        Z = ⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E → M₁ = (interior Z)ᶜ →
        M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
          Set M₁) →
        A = M₂ ∩ ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪
          {p | 0 < C.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
            P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
              (C.toChain.E p)) / C.toChain.scale p ≤ 4 * Δ}) ∩
          {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
            blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.toChain.E x) =
              ρ k.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.toChain.E x)‖ <
              4 * Δ * ρ k.1} →
        M₃ = M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) →
        ∀ x ∈ M₃, ∀ w, w = (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
            (C.toChain.E x) →
          ∃ f : Circle → X, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧
            range f = (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
              (C.toChain.E p)) ⁻¹' {w} ∧ IsConnected (range f) := by
  obtain ⟨hrow, hsub, -⟩ := C.fc38_row_FCW hβ hd hεr hσc hγ hγ1
  obtain ⟨K₃, -, hK⟩ := hsub
  refine ⟨K₃, fun Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ x hx w hw => ?_⟩
  obtain ⟨hw0, hw1⟩ := hK Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hw1
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hrow
  subst hw
  obtain ⟨-, -, -, hconn, hf, -⟩ := h7 _ hw0 i hi.1 hi.2
  obtain ⟨f, hfe, hfr⟩ := hf
  exact ⟨f, hfe, hfr, hfr ▸ hconn⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
