import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesEdgeParentData
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentOfCore

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3b: consumer of the edge parent set

`BoundaryGaf02ChainE.edgeParent_of_basesCore_BBP`: G12's `exists_edgeParent_of_core_BAUGD` applied
to the core `basesCore_BBP` with `U = edgeParentSet_BBP`; the arguments `hU hcut hrk` are
discharged here, `hsub` (fibres over `U` meet `{T ≤ 4Δ}`) is the explicit argument.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **Consumer (G12 plumbing)**: the open edge parent of the core `basesCore_BBP`, given
`hsub : U ⊆ f₁⁻¹(B₁)`. -/
theorem edgeParent_of_basesCore_BBP (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hσ : σc ≤ 1 / 4) (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (hsub : C.edgeParentSet_BBP ⊆ C.toChain.stageMap 1 ⁻¹' C.baseSet_BBP 1) :
    Nonempty (BoundaryEdgeParent_BIFc C.toChain (C.basesCore_BBP hβ2 hγ hσ hb).source
      (C.basesCore_BBP hβ2 hγ hσ hb).base) :=
  C.exists_edgeParent_of_core_BAUGD hc hC hε0 hε hγc hγc1 hβc1 (C.basesCore_BBP hβ2 hγ hσ hb)
    C.edgeParentSet_BBP C.isOpen_edgeParentSet_BBP C.baseSource_one_eq_edgeParent_BBP hsub
    (fun _ hp => C.edgeParent_rank_BBP hσ hb hp)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
