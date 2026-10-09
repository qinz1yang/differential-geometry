import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageSubmersionSlim
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageSubmersionEdge

/-!
# A4 / G11 (lane S-BASES-PORT), group G1c: consumer of the three native stage submersions

`BoundaryGaf02ChainE.stage_submersions_native_BBP` assembles the circle (B-BASES-PORT G1), slim
(G1b) and edge (G1c) stage submersions into the family statement the BASES producer quantifies
over: on the original plateau of every chart of every stage, `D(κ_j ∘ f_st⁰)` is onto the
stage-`st` chart target (`ℝ²`, `ℝ`, `ℝ`). The register premises are explicit hypotheses
(`β₂ ≤ 10⁻⁷`, `γ ≤ 1/2` for the circle; `σ_c ≤ 1/4`, `b ≤ 1/(1000Δ)` for the edge).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

/-- **Consumer of G1 / G1b / G1c**: the three native stage submersions on their original
plateaus (circle: `dist < 200ρ_j`, `‖η_j‖ < 6`; edge: `dist < 100Δρ_j`, `|η_j| < 6Δ`,
`t_B < 6Δ`; slim: `dist < 10⁶Δρ_j`, `|η_j| < 6·10⁵Δ`). -/
theorem BoundaryGaf02ChainE.stage_submersions_native_BBP
    (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hσ : σc ≤ 1 / 4)
    (hb : b ≤ 1 / (1000 * Δ)) :
    (∀ (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1) →
      ‖S.circleEta_BIF j.1 q‖ < 6 →
      Surjective (mfderiv W.model 𝓘(ℝ, ℝ²)
        (fun p => S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 p)) q.val)) ∧
    (∀ (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1) →
      |S.edgeEta_BIF j.1 q| < 6 * Δ → S.edgeHeightRaw q < 6 * Δ →
      Surjective (mfderiv W.model 𝓘(ℝ, ℝ)
        (fun p => S.edgeKappa_BBP j (C.toChain.nativeStageMap_BIFc 1 p)) q.val)) ∧
    (∀ (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric;
        dist q j.1 < 1000000 * Δ * S.rho j.1) →
      |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ) →
      Surjective (mfderiv W.model 𝓘(ℝ, ℝ)
        (fun p => S.slimKappa_BBP j (C.toChain.nativeStageMap_BIFc 2 p)) q.val)) :=
  ⟨fun j _ hq hη => C.stage_submersion_circle_BBP hβ2 hγ j hq hη,
    fun j _ hq hη hh => C.stage_submersion_edge_BBP hσ hb j hq hη hh,
    fun j _ hq hη => C.stage_submersion_slim_BBP j hq hη⟩

end DifferentialGeometry.Geometry.Collapse
