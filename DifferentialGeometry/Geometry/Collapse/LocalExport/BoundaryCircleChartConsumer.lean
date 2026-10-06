import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleChart

/-!
# Consumer of the circle-stage whole-fibre layer (O-WF G1+G2)

`BoundaryGaf02ChainE.circle_stage_OWF`: on the BASES core sources / bases of the boundary chain,
every whole circle fibre `X₀ ∩ f₀⁻¹{y}`, `y ∈ B₀`, is homeomorphic to `S¹` (the derived exit of
`circle_chart_OWF`), and `Θ₀` is a topological embedding of the native base `f₀⁰(X₀)` (no
merging, G11's `hemb` at `st = 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The circle stage of the boundary chain**: whole fibres `≃ₜ S¹` and no merging. -/
theorem circle_stage_OWF (hc : c 2 < 1 / 1000) (hβ : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hd : γ + β 2 < 1 / 10) :
    (∀ y ∈ C.baseSet_BBP 0, Nonempty
      ((C.baseSource_BBP 0 ∩ C.toChain.stageMap 0 ⁻¹' {y} : Set W.Carrier) ≃ₜ Circle)) ∧
      Topology.IsEmbedding (fun x : C.toChain.nativeStageMap_BIFc 0 '' C.baseSource_BBP 0 =>
        C.toChain.laterV2_BAUGD 0 x) :=
  ⟨fun _ hy => (C.circle_chart_OWF hc hβ hγ hd hy).nonempty_fibre_homeomorph,
    C.circle_later_isEmbedding_OWF hc hβ hγ hd⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
