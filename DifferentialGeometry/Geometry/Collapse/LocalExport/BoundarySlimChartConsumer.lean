import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimChart

/-!
# Consumer of the slim-stage whole-fibre layer (O-WF G3)

`BoundaryGaf02ChainE.slim_stage_OWF`: on the BASES core sources / bases of the boundary chain,
every whole slim fibre `X₂ ∩ f₂⁻¹{y}`, `y ∈ B₂`, is homeomorphic to the standard `ClosureSphere`
or to `Circle × Circle` (the derived exit of `slim_chart_OWF`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic GC.GraphManifold
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

/-- **The slim stage of the boundary chain**: whole fibres `≃ₜ S²` or `≃ₜ T²`. -/
theorem slim_stage_OWF (hc : c 2 < 1 / 1000) (hK : 5 ≤ K) :
    ∀ y ∈ C.baseSet_BBP 2,
      Nonempty ((C.baseSource_BBP 2 ∩ C.toChain.stageMap 2 ⁻¹' {y} : Set W.Carrier) ≃ₜ
          ClosureSphere.{0}) ∨
        Nonempty ((C.baseSource_BBP 2 ∩ C.toChain.stageMap 2 ⁻¹' {y} : Set W.Carrier) ≃ₜ
          Circle × Circle) := by
  intro _ hy
  rcases C.slim_chart_OWF hc hK hy with h | h
  · exact Or.inl h.nonempty_fibre_homeomorph
  · exact Or.inr h.nonempty_fibre_homeomorph

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
